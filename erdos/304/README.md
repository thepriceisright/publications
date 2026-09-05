# Erdős 304: the 1950 lower bound

[Lower1950.lean](Lower1950.lean) proves the known bound `log log b = O(N(b))`, where `N(b)` is the largest minimum number of distinct unit fractions needed for `a/b` with `1 ≤ a < b`. The open question asks for a matching upper bound. This contribution supplies the classical lower bound attributed to Erdős in 1950 in the [problem source](https://www.erdosproblems.com/304).

The proof is the artifact linked by [upstream PR #5237](https://github.com/google-deepmind/formal-conjectures/pull/5237), migrated byte for byte. Its SHA-256 is `3af1b018dd843696fc46893229f9403d70f354f4fbf26273d0b500a5359ac774`. The original header describes the earlier check at upstream `d1401976e8c59c6341cd0eceb425d5180092e176`. Fresh verification on 2026-09-05 used upstream `8323e878b83fcd7f4a448256069352a265460d75`, Lean 4.33.1, and the same unchanged 304 source file.

The exact declaration is:

```lean
erdos_304.variants.lower_1950_candidate.erdos_304.variants.lower_1950
```

The argument first proves that `(b-1)/b` has a finite distinct-unit-fraction representation, so the minimum used in the proof is attained. A quantitative gap bound gives `b ≤ (2(k+1))^(4^k)` for its minimum length `k`. For `b ≥ 3`, taking logarithms gives `log log b ≤ 6k ≤ 6N(b)`. The argument therefore supplies an explicit eventual bound and does not rely on an empty-set minimum.

The external proof compiles with no errors and three warnings: a missing module docstring, deprecated `push_neg`, and duplicated namespace components. These are preserved with the original source. Its axiom report contains only `propext`, `Classical.choice`, and `Quot.sound`. The imported upstream module passes `lake --wfail build`; the external proof is compiled with `lake env lean`, without treating warnings as errors.

[Verification inputs and logs](../../verification/304) record a separate challenge copied from the upstream theorem's type, exact exported-statement comparison, and Lean builtin kernel replay. The challenge intentionally contains a placeholder; the accepted solution is permitted no `sorryAx`. The [upstream source snapshot](../../verification/304/Upstream.lean) includes other unproved statements, which this proof does not establish. See [reproduction instructions](../../verification/README.md).

Harmonic Aristotle produced the proof through an automated workflow. The file retains its original provenance. No human mathematical review, independent kernel implementation, or new open-problem solution is claimed. Trusted third-party dependency caches were reused.
