# Publications

Selected Lean artifacts prepared under Keith Vertrees' direction. These contributions concern known mathematics and a formal-statement repair. They do not establish a newly solved open problem.

| Contribution | Artifact | Scope |
| --- | --- | --- |
| Erdős 304 | [1950 lower-bound proof](erdos/304/README.md) | A classical Egyptian-fraction bound, supporting upstream PR #5237. |
| Erdős 867 | [Proof and patch](erdos/867/README.md) | The elementary upper-half construction proves the known lower bound. |
| Erdős 769 | [Repair and regression](erdos/769/README.md) | Restrict the cutoff condition to positive dimensions. The growth-rate conjecture remains open. |

The source base is [Formal Conjectures at `8323e878`](https://github.com/google-deepmind/formal-conjectures/tree/8323e878b83fcd7f4a448256069352a265460d75), using Lean 4.33.1 and its pinned Mathlib dependencies. The patched files preserve unrelated upstream `sorry` declarations. Verification concerns the named 304 and 867 lower-bound theorems and the separate 769 regression theorem.

See [verification evidence and reproduction](verification/README.md). All three targets passed comparison against separately compiled challenges and replay with Lean's builtin kernel, allowing only `propext`, `Classical.choice`, and `Quot.sound`. Third-party dependency caches were trusted. No second kernel implementation or human mathematical review is claimed.

These artifacts were prepared with AI assistance. The 304 and 867 proofs came from Harmonic Aristotle. The 769 regression was extracted from a GLM 5.3 Flash boundary refutation. The proposed positive-dimension convention should receive mathematical or maintainer review. Details are in [NOTICE](NOTICE).

Code and Lean sources are distributed under [Apache-2.0](LICENSE), with original source notices retained. The contributions are proposed in upstream PRs [#5237](https://github.com/google-deepmind/formal-conjectures/pull/5237), [#5287](https://github.com/google-deepmind/formal-conjectures/pull/5287), and [#5288](https://github.com/google-deepmind/formal-conjectures/pull/5288). Hosting the evidence does not imply maintainer acceptance.
