# Erdős 867: elementary lower bound

The upper half of `{1, …, N}` is consecutive-sum-free. Any sum of at least two of its elements exceeds `N`, and the set has at least `N/2` elements. The proof takes the error constant to be zero.

- [Complete patched upstream file](867.lean)
- [Minimal proof-body patch](867.patch)
- [Exact challenge and solution used for verification](../../verification/867)

The target is `Erdos867.erdos_867.variants.lower_bound`. The patch changes only its proof body. This is the known baseline described in the source; the main problem already has a negative solution and a stronger formal construction. No first-formalization claim is made.

The 24-line proof was generated with Aristotle and adapted for an inline contribution. It passed a targeted build against the recorded upstream revision and exact-statement exported-term comparison with Lean kernel replay. Other declarations in the complete source still contain their upstream placeholders and are not claimed as proved here.

Sources: [upstream target](https://github.com/google-deepmind/formal-conjectures/blob/8323e878b83fcd7f4a448256069352a265460d75/FormalConjectures/ErdosProblems/867.lean#L62), [public problem](https://www.erdosproblems.com/867), [existing stronger construction](https://github.com/plby/lean-proofs/blob/main/src/v4.29.1/ErdosProblems/Erdos867.lean).
