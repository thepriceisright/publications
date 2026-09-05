/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import FormalConjecturesUtil
import FormalConjectures.ErdosProblems.«769»

/-!
# Zero-dimensional cutoff regression for Erdős 769

This regression records the boundary obstruction in the original declaration.
-/

namespace PublicationRegression769
open Erdos769

@[category API, AMS 52]
theorem no_cutoff_zero : ∀ m : ℕ, ¬IsCutoff 0 m := by
  intro m hm
  obtain ⟨hall, _⟩ :
      (∀ k, m ≤ k → Admissible 0 k) ∧ (m = 0 ∨ ¬Admissible 0 (m - 1)) := hm
  have h0 : 0 < m + 2 := by omega
  have h1 : 1 < m + 2 := by omega
  have hle : m ≤ m + 2 := by omega
  have hab : ¬((⟨0, h0⟩ : Fin (m + 2)) = ⟨1, h1⟩) := by
    intro heq
    have hv : (0 : ℕ) = 1 := congrArg Fin.val heq
    omega
  have hbad : ¬Admissible 0 (m + 2) := by
    intro hA
    obtain ⟨tiles, hT⟩ :
        ∃ tiles : Fin (m + 2) → Cube 0, IsTiling tiles := hA
    obtain ⟨_, hcover⟩ :
        (∀ i, (tiles i).InsideUnit) ∧ ∀ x : Fin 0 → ℝ, InUnit x →
          ∃! i : Fin (m + 2), (tiles i).Mem x := hT
    have hx : InUnit (fun _ : Fin 0 => (0 : ℝ)) :=
      fun j => absurd j.isLt (Nat.not_lt_zero j.val)
    have hmem : ∀ i : Fin (m + 2), (tiles i).Mem (fun _ : Fin 0 => (0 : ℝ)) :=
      fun _ j => absurd j.isLt (Nat.not_lt_zero j.val)
    obtain ⟨i, _, hu⟩ := hcover (fun _ : Fin 0 => (0 : ℝ)) hx
    exact hab ((hu ⟨0, h0⟩ (hmem ⟨0, h0⟩)).trans ((hu ⟨1, h1⟩ (hmem ⟨1, h1⟩)).symm))
  exact hbad (hall (m + 2) hle)

end PublicationRegression769
