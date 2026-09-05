# Verification and reproduction

[results.json](results.json) records the upstream revision, dependency manifest, tool revisions, artifact hashes and accepted comparison targets. The `304`, `867` and `769` directories contain the exact challenge, solution, configuration and successful logs from the recorded proof replays. Paths and unrelated experiment records are excluded from this package.

The 304 check proves `erdos_304.variants.lower_1950_candidate.erdos_304.variants.lower_1950`. Its challenge obtains the type of `Erdos304.erdos_304.variants.lower_1950` from the freshly built upstream module, then declares a placeholder of exactly that type under the candidate name. The solution is byte-identical to the published proof. The imported 304 source is hash-checked against the recorded snapshot.

The 867 check proves `Erdos867.erdos_867.variants.lower_bound`. The 769 check proves `PublicationRegression769.no_cutoff_zero`. The edited 769 growth-rate conjecture remains unproved. Warnings about `sorry` in the supplied full-source files concern the independently compiled challenge or unrelated original declarations. Neither accepted proof depends on `sorryAx`.

## Build the contributions

Install Git, Python 3 and [Lean's elan toolchain manager](https://github.com/leanprover/elan). From this repository's root, run:

```sh
python3 scripts/build.py
```

This clones the recorded upstream revision under `.build/formal-conjectures`, obtains its pinned dependency cache, applies both patches, and runs `lake --wfail build` on the two patched problem modules, the 304 upstream module and the 769 regression. It also compiles the external 304 proof with `lake env lean`. That unchanged external file has three style/deprecation warnings described in its [README](../erdos/304/README.md); compilation succeeds and the final theorem has no `sorryAx` dependency. It does not build every conjecture. Dependency downloads can be large. If the exact checkout already has trusted dependencies installed, use `--skip-cache`. `--checkout PATH` selects an existing checkout at the recorded revision; unrelated tracked edits are refused.

## Replay the exact proof checks

On Linux, install `bubblewrap`, then build the pinned public verifier sources:

```sh
git clone https://github.com/leanprover/comparator.git .build/comparator
git -C .build/comparator checkout --detach 3927ad383f208ae977c340a91c48ac9b497d2097
cp .build/formal-conjectures/lean-toolchain .build/comparator/lean-toolchain
cp verification/comparator-lake-manifest.json .build/comparator/lake-manifest.json
(cd .build/comparator && lake build comparator lean4export)
```

The recorded comparator revision originally selected Lean 4.33.0. The explicit toolchain override above selects the verified Lean 4.33.1 environment. The supplied dependency manifest pins lean4export to `15f6055e299ad5b89345e533cc2192f4cc00f659`. After building the contributions, run:

```sh
python3 scripts/replay.py \
  --comparator .build/comparator/.lake/build/bin/comparator \
  --exporter .build/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export
```

The script uses fresh comparison directories, the recorded source inputs, and a bubblewrap adapter that disables networking and permits writes only to each check's `.lake` directory. The trusted challenge is exported before the candidate is compiled. Verifier revisions and tracked cleanliness are checked, allowing only that exact comparator toolchain override; you are responsible for building those trusted binaries. Executable hashes are recorded, and may differ across platforms. The published original executable hashes came from an aarch64 Linux machine.

All selected checks must exit successfully. Add `--targets 304` to replay only the migrated proof; by default all three checks run. Fresh results and logs remain under `.build/replays`. The proof check allows only `propext`, `Classical.choice`, and `Quot.sound`. It uses Lean's builtin kernel and trusted dependency build artifacts, not a second kernel implementation or an independent rebuild of all dependencies. See the [comparator documentation](https://github.com/leanprover/comparator/tree/3927ad383f208ae977c340a91c48ac9b497d2097) for its trust assumptions.
