#!/usr/bin/env python3
"""Build the published patches against the exact upstream revision."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--checkout', type=Path, default=ROOT / '.build/formal-conjectures')
    parser.add_argument('--skip-cache', action='store_true', help='Use already installed trusted dependencies')
    args = parser.parse_args()
    checkout = args.checkout.resolve()
    evidence = json.loads((ROOT / 'verification/results.json').read_text())
    for path, expected in evidence['files'].items():
        if sha(ROOT / path) != expected:
            raise ValueError('Publication artifact changed: ' + path)
    if not checkout.exists():
        checkout.parent.mkdir(parents=True, exist_ok=True)
        subprocess.run(['git', 'clone', evidence['upstream_repository'] + '.git', str(checkout)], check=True)
        subprocess.run(['git', 'checkout', '--detach', evidence['upstream_commit']], cwd=checkout, check=True)
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=checkout, text=True).strip()
    if head != evidence['upstream_commit']:
        raise ValueError('Existing checkout must be at the recorded upstream commit')
    if sha(checkout / 'lake-manifest.json') != evidence['dependency_manifest_sha256']:
        raise ValueError('Dependency manifest differs from the verified version')
    targets = {v['target_file'] for v in evidence['artifacts'].values()}
    changed = subprocess.check_output(['git', 'diff', 'HEAD', '--name-only'], cwd=checkout, text=True).splitlines()
    if set(changed) - targets:
        raise ValueError('Existing checkout has unrelated tracked changes')
    for number, artifact in evidence['artifacts'].items():
        path = checkout / artifact['target_file']
        if sha(path) == artifact['upstream_file_sha256']:
            patch = ROOT / 'erdos' / number / (number + '.patch')
            subprocess.run(['git', 'apply', '--check', str(patch)], cwd=checkout, check=True)
            subprocess.run(['git', 'apply', str(patch)], cwd=checkout, check=True)
        if sha(path) != artifact['patched_file_sha256']:
            raise ValueError('Unexpected patched source: ' + str(path))
    source = ROOT / 'erdos/769/Regression769.lean'
    target = checkout / 'FormalConjectures/ErdosProblems/Regression769.lean'
    if target.exists() and sha(source) != sha(target):
        raise ValueError('Refusing to replace a different regression file')
    shutil.copyfile(source, target)
    for relative, expected in evidence.get('imported_sources', {}).items():
        if sha(checkout / relative) != expected:
            raise ValueError('Imported upstream source differs: ' + relative)
    if not args.skip_cache:
        subprocess.run(['lake', 'exe', 'cache', 'get'], cwd=checkout, check=True)
    subprocess.run(['lake', '--wfail', 'build', 'FormalConjectures.ErdosProblems.«867»',
                    'FormalConjectures.ErdosProblems.«769»',
                    'FormalConjectures.ErdosProblems.Regression769',
                    'FormalConjectures.ErdosProblems.«304»'], cwd=checkout, check=True)
    subprocess.run(['lake', 'env', 'lean', str(ROOT / 'erdos/304/Lower1950.lean')],
                   cwd=checkout, check=True)
    print('Both patched files and the zero-dimensional regression built successfully.')
    print('The repaired 769 growth-rate conjecture remains unproved.')


if __name__ == '__main__':
    main()
