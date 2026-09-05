#!/usr/bin/env python3
"""Replay the published exact-statement checks with pinned local verifier binaries."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkout', type=Path, default=ROOT / '.build/formal-conjectures')
    parser.add_argument('--comparator', type=Path, required=True)
    parser.add_argument('--exporter', type=Path, required=True)
    args = parser.parse_args()
    checkout = args.checkout.resolve()
    comparator, exporter = args.comparator.resolve(), args.exporter.resolve()
    evidence = json.loads((ROOT / 'verification/results.json').read_text())
    for path, expected in evidence['files'].items():
        if sha(ROOT / path) != expected:
            raise ValueError('Publication artifact changed: ' + path)
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=checkout, text=True).strip()
    if head != evidence['upstream_commit'] or sha(checkout / 'lake-manifest.json') != evidence['dependency_manifest_sha256']:
        raise ValueError('Unexpected upstream revision or dependency manifest')
    # Binaries differ across platforms. Require their source checkouts at the
    # recorded revisions, and record the locally built executable hashes.
    for binary, revision in [(comparator, evidence['comparator_revision']), (exporter, evidence['exporter_revision'])]:
        repository = binary.parents[3]
        actual = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=repository, text=True).strip()
        dirty = subprocess.check_output(['git', 'status', '--porcelain', '--untracked-files=no'], cwd=repository, text=True)
        permitted_change = (binary == comparator and dirty.strip() == 'M lean-toolchain'
                            and (repository / 'lean-toolchain').read_text().strip() == evidence['lean_toolchain'])
        if actual != revision or (dirty and not permitted_change):
            raise ValueError('Unexpected verifier revision or source modification')
    if (comparator.parents[3] / 'lean-toolchain').read_text().strip() != evidence['lean_toolchain']:
        raise ValueError('Comparator must use the recorded Lean toolchain')
    if sha(comparator.parents[3] / 'lake-manifest.json') != evidence['comparator_manifest_sha256']:
        raise ValueError('Comparator dependency manifest differs')
    prefix = Path(subprocess.check_output(['lake', 'env', 'lean', '--print-prefix'], cwd=checkout, text=True).strip())
    raw = subprocess.check_output(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=checkout, text=True).strip()
    paths = [str((checkout / p).resolve()) for p in raw.split(':')]
    packages = [p.resolve() for p in (checkout / '.lake/packages').iterdir() if p.is_dir()]
    roots = [checkout, prefix, comparator.parents[3], exporter.parents[3], *packages]
    output = ROOT / '.build/replays'
    output.mkdir(parents=True, exist_ok=True)
    run = Path(tempfile.mkdtemp(prefix='run-', dir=output))
    for number in ['867', '769']:
        directory = run / number
        directory.mkdir()
        (directory / '.lake').mkdir()
        for name in ['Challenge.lean', 'Solution.lean', 'config.json']:
            shutil.copyfile(ROOT / 'verification' / number / name, directory / name)
        (directory / 'lakefile.toml').write_text('name = "publication_check"\n')
        (directory / 'lean-toolchain').write_text(evidence['lean_toolchain'] + '\n')
        adapter = directory / 'sandbox-runner'
        shutil.copyfile(ROOT / 'scripts/sandbox.py', adapter)
        adapter.chmod(0o755)
        env = {'PATH': str(prefix / 'bin') + ':/usr/bin:/bin',
               'LEAN_PATH': str(directory / '.lake/build/lib/lean') + ':' + ':'.join(paths),
               'COMPARATOR_LANDRUN': str(adapter), 'COMPARATOR_LEAN4EXPORT': str(exporter),
               'ERDOS_PROOF_READ_ROOTS': json.dumps([str(p) for p in roots]),
               'LEAN_ABORT_ON_PANIC': '1'}
        process = subprocess.Popen([str(comparator), 'config.json'], cwd=directory, env=env,
                                   text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
        try:
            stdout, stderr = process.communicate(timeout=600)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGKILL)
            stdout, stderr = process.communicate()
        (directory / 'stdout.log').write_text(stdout)
        (directory / 'stderr.log').write_text(stderr)
        result = {'verified': process.returncode == 0 and 'Your solution is okay!' in stdout,
                  'exit_code': process.returncode, 'theorem_names': evidence['checks'][number]['theorem_names'],
                  'challenge_sha256': sha(directory / 'Challenge.lean'),
                  'solution_sha256': sha(directory / 'Solution.lean'),
                  'comparator_binary_sha256': sha(comparator), 'exporter_binary_sha256': sha(exporter)}
        (directory / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
        print(number, json.dumps(result), flush=True)
        if not result['verified']:
            raise SystemExit('Proof check failed; inspect ' + str(directory))


if __name__ == '__main__':
    main()
