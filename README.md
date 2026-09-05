# Publications

Selected Lean artifacts prepared under Keith Vertrees' direction. These contributions concern known mathematics and a formal-statement repair. They do not establish a newly solved open problem.

| Contribution | Artifact | Scope |
| --- | --- | --- |
| Erdős 867 | [Proof and patch](erdos/867/README.md) | The elementary upper-half construction proves the known lower bound. |
| Erdős 769 | [Repair and regression](erdos/769/README.md) | Restrict the cutoff condition to positive dimensions. The growth-rate conjecture remains open. |

The source base is [Formal Conjectures at `8323e878`](https://github.com/google-deepmind/formal-conjectures/tree/8323e878b83fcd7f4a448256069352a265460d75), using Lean 4.33.1 and its pinned Mathlib dependencies. The patched files preserve unrelated upstream `sorry` declarations. Verification concerns only the named 867 lower-bound theorem and the separate 769 regression theorem.

See [verification evidence and reproduction](verification/README.md). Both targets passed comparison against separately compiled challenges and replay with Lean's builtin kernel, allowing only `propext`, `Classical.choice`, and `Quot.sound`. Third-party dependency caches were trusted. No second kernel implementation or human mathematical review is claimed.

These artifacts were prepared with AI assistance. The 867 proof came from Harmonic Aristotle. The 769 regression was extracted from a GLM 5.3 Flash boundary refutation. The proposed positive-dimension convention should receive mathematical or maintainer review. Details are in [NOTICE](NOTICE).

Code and Lean sources are distributed under [Apache-2.0](LICENSE), with original source notices retained. Hosting these artifacts does not indicate that an upstream pull request has been submitted or accepted.
