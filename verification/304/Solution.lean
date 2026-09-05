/-
Formal proof of `erdos_304.variants.lower_1950` (Erdős 1950: log log b ≪ N(b))
from google-deepmind/formal-conjectures, verified against that repository at
commit d1401976e8c59c6341cd0eceb425d5180092e176 (lean-toolchain v4.33.1):
`lake env lean` on this file compiles with no errors, no incomplete proofs, and
`#print axioms` reports exactly [propext, Classical.choice, Quot.sound].

Provenance: proof produced by Harmonic's Aristotle prover
(project d4c4ae71-8eb2-4607-88b1-dd174b6baaa6) inside an automated harness
(https://github.com/thepriceisright/erdos-agent); the harness generated the
theorem statement verbatim from the pinned repository file, assembled the
multi-file job output, and verified it against the pinned definitions.
No human mathematician has reviewed the proof; the Lean kernel is the
authority for the claim. The auxiliary section formalizes the
Fibonacci–Sylvester greedy algorithm and a tower bound.
-/

import FormalConjectures.ErdosProblems.«304»

/-
Auxiliary material for the lower bound `log log b ≪ N(b)` of Erdős problem 304.

The mathematical content is:

* `exists_unitFraction_repr`: the greedy (Fibonacci–Sylvester) algorithm, showing that every
  rational `a / b ∈ (0, 1/N)` is a sum of finitely many distinct unit fractions with all
  denominators `> N`.
* `key_bound`: a quantitative version of the classical fact that a sum of `k` distinct unit
  fractions which is `< p / q` is at most `p / q - 1 / (2 (k+1) q) ^ (4 ^ k)`.  In particular a
  sum of `k` distinct unit fractions which is `< 1` is at most `1 - 1 / (2 (k+1)) ^ (4 ^ k)`.
* `log_log_le_of_le_tower`: the elementary estimate turning `b ≤ (2 (k+1)) ^ (4 ^ k)` into
  `log log b ≤ 6 k`.
-/


namespace Erdos304Aux

open Finset

/-- The greedy (Fibonacci–Sylvester) algorithm: every rational `a / b` with `0 < a / b < 1 / N`
is a sum of distinct unit fractions all of whose denominators are `> N`. -/
theorem exists_unitFraction_repr (a : ℕ) : ∀ b N : ℕ, 0 < a → 0 < N → 0 < b →
    (a : ℚ) / (b : ℚ) < 1 / (N : ℚ) →
    ∃ s : Finset ℕ, (∀ n ∈ s, N < n) ∧ (a : ℚ) / (b : ℚ) = ∑ n ∈ s, (n : ℚ)⁻¹ := by
  induction a using Nat.strong_induction_on with
  | _ a IH =>
    intro b N ha hN hb hlt
    have hbQ : (0 : ℚ) < (b : ℚ) := by exact_mod_cast hb
    have hNQ : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
    have hab : a < b := by
      have h1 : (a : ℚ) / b < 1 := by
        refine hlt.trans_le ?_
        rw [div_le_one hNQ]
        exact_mod_cast hN
      rw [div_lt_one hbQ] at h1
      exact_mod_cast h1
    set n : ℕ := (b - 1) / a + 1 with hn
    have hnmul : a * n = a * ((b - 1) / a) + a := by rw [hn]; ring
    have hd1 := Nat.div_add_mod (b - 1) a
    have hd2 := Nat.mod_lt (b - 1) ha
    have hd3 : a * ((b - 1) / a) ≤ b - 1 := by omega
    have hbn : b ≤ a * n := by omega
    have hna : a * n < b + a := by rw [hnmul]; omega
    have hnpos : 0 < n := by rw [hn]; exact Nat.succ_pos _
    have hnQ : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hnpos
    have hinv_le : (n : ℚ)⁻¹ ≤ (a : ℚ) / b := by
      rw [inv_eq_one_div, div_le_div_iff₀ hnQ hbQ]
      have : (b : ℚ) ≤ (a : ℚ) * n := by exact_mod_cast hbn
      linarith
    have hNn : N < n := by
      have h1 : (n : ℚ)⁻¹ < 1 / (N : ℚ) := lt_of_le_of_lt hinv_le hlt
      rw [inv_eq_one_div, div_lt_div_iff₀ hnQ hNQ] at h1
      have : (N : ℚ) < n := by linarith
      exact_mod_cast this
    rcases eq_or_lt_of_le hbn with heq | hlt'
    · refine ⟨{n}, ?_, ?_⟩
      · intro m hm
        simp only [Finset.mem_singleton] at hm
        subst hm; exact hNn
      · rw [Finset.sum_singleton, inv_eq_one_div, div_eq_div_iff (ne_of_gt hbQ) (ne_of_gt hnQ)]
        have : (b : ℚ) = (a : ℚ) * n := by exact_mod_cast heq
        linarith
    · set a' : ℕ := a * n - b with ha'def
      set b' : ℕ := b * n with hb'def
      have ha'pos : 0 < a' := by omega
      have ha'lt : a' < a := by omega
      have hb'pos : 0 < b' := by positivity
      have hb'Q : (0 : ℚ) < (b' : ℚ) := by exact_mod_cast hb'pos
      have hcast : (a' : ℚ) = (a : ℚ) * n - b := by
        rw [ha'def, Nat.cast_sub hbn]
        push_cast
        ring
      have hident : (a' : ℚ) / (b' : ℚ) = (a : ℚ) / b - (n : ℚ)⁻¹ := by
        rw [hcast, hb'def]
        push_cast
        field_simp
      have hsmall : (a' : ℚ) / (b' : ℚ) < 1 / (n : ℚ) := by
        rw [div_lt_div_iff₀ hb'Q hnQ]
        have hnat : a' * n < 1 * b' := by
          have hlt2 : a' < b := by omega
          rw [hb'def, one_mul]
          exact (Nat.mul_lt_mul_right hnpos).2 hlt2
        exact_mod_cast hnat
      obtain ⟨s', hs'mem, hs'sum⟩ := IH a' ha'lt b' n ha'pos hnpos hb'pos hsmall
      have hnotmem : n ∉ s' := fun h => lt_irrefl n (hs'mem n h)
      refine ⟨insert n s', ?_, ?_⟩
      · intro m hm
        rcases Finset.mem_insert.1 hm with rfl | hm
        · exact hNn
        · exact hNn.trans (hs'mem m hm)
      · rw [Finset.sum_insert hnotmem, ← hs'sum, hident]
        ring

set_option maxHeartbeats 1000000 in
/-- The key quantitative statement: a sum of at most `k` distinct unit fractions (with all
denominators `≥ 2`) which is `< p / q` is at most `p / q - 1 / (2 (k+1) q) ^ (4 ^ k)`. -/
theorem key_bound : ∀ (k p q : ℕ) (s : Finset ℕ), 0 < p → 0 < q → (∀ n ∈ s, 2 ≤ n) →
    s.card ≤ k → (∑ n ∈ s, (n : ℚ)⁻¹) < (p : ℚ) / (q : ℚ) →
    (1 : ℚ) / (2 * ((k : ℚ) + 1) * (q : ℚ)) ^ (4 ^ k) ≤
      (p : ℚ) / (q : ℚ) - ∑ n ∈ s, (n : ℚ)⁻¹ := by
  intro k
  induction k with
  | zero =>
    intro p q s hp hq _ hcard _
    have hs : s = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 hcard)
    subst hs
    have hqQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
    have hpQ : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    simp only [Finset.sum_empty, sub_zero, Nat.cast_zero, pow_zero, pow_one, zero_add]
    rw [div_le_div_iff₀ (by positivity) hqQ]
    nlinarith
  | succ k IH =>
    intro p q s hp hq h2 hcard hsum
    have hqQ : (0 : ℚ) < (q : ℚ) := by exact_mod_cast hq
    have hq1 : (1 : ℚ) ≤ (q : ℚ) := by exact_mod_cast hq
    have hpQ : (1 : ℚ) ≤ (p : ℚ) := by exact_mod_cast hp
    have hkR : (0 : ℚ) ≤ (k : ℚ) := by positivity
    obtain ⟨D, hD⟩ : ∃ D : ℚ, D = 2 * ((k : ℚ) + 1 + 1) * (q : ℚ) := ⟨_, rfl⟩
    have hD1 : (1 : ℚ) ≤ D := by rw [hD]; nlinarith
    have hDpos : (0 : ℚ) < D := by linarith
    have hDgoal : (2 : ℚ) * (((k + 1 : ℕ) : ℚ) + 1) * (q : ℚ) = D := by rw [hD]; push_cast; ring
    rw [hDgoal]
    have hpowmono : ∀ j : ℕ, 1 ≤ j → D ≤ D ^ j := by
      intro j hj
      calc D = D ^ 1 := (pow_one D).symm
        _ ≤ D ^ j := pow_le_pow_right₀ hD1 hj
    have hpow1 : (1 : ℕ) ≤ 4 ^ (k + 1) := Nat.one_le_pow _ _ (by norm_num)
    rcases Finset.eq_empty_or_nonempty s with rfl | hne
    · simp only [Finset.sum_empty, sub_zero]
      have h1 : (q : ℚ) ≤ D ^ (4 ^ (k + 1)) := by
        have hqD : (q : ℚ) ≤ D := by rw [hD]; nlinarith
        exact hqD.trans (hpowmono _ hpow1)
      calc (1 : ℚ) / D ^ (4 ^ (k + 1)) ≤ 1 / (q : ℚ) := one_div_le_one_div_of_le hqQ h1
        _ ≤ (p : ℚ) / q := by gcongr
    · obtain ⟨m, hm, hmmin⟩ : ∃ m ∈ s, ∀ x ∈ s, m ≤ x :=
        ⟨s.min' hne, s.min'_mem hne, fun x hx => s.min'_le x hx⟩
      have hm2 : 2 ≤ m := h2 m hm
      have hmQ : (0 : ℚ) < (m : ℚ) := by
        have h0 : (0 : ℕ) < m := by omega
        exact_mod_cast h0
      have hmem : (m : ℚ)⁻¹ ≤ ∑ n ∈ s, (n : ℚ)⁻¹ :=
        Finset.single_le_sum (f := fun n : ℕ => (n : ℚ)⁻¹)
          (fun i _ => inv_nonneg.mpr (Nat.cast_nonneg i)) hm
      by_cases hcase : 2 * (k + 2) * q ≤ m
      · -- the smallest denominator is large, so the whole sum is at most `1 / (2 q)`
        have hmD : D ≤ (m : ℚ) := by
          have hc : (((2 * (k + 2) * q : ℕ)) : ℚ) ≤ (m : ℚ) := by exact_mod_cast hcase
          push_cast at hc
          rw [hD]; linarith
        have hcardQ : ((s.card : ℕ) : ℚ) ≤ (k : ℚ) + 1 := by exact_mod_cast hcard
        have hsumle : (∑ n ∈ s, (n : ℚ)⁻¹) ≤ (s.card : ℚ) * (m : ℚ)⁻¹ := by
          calc (∑ n ∈ s, (n : ℚ)⁻¹) ≤ ∑ _n ∈ s, (m : ℚ)⁻¹ := by
                refine Finset.sum_le_sum ?_
                intro i hi
                have hmi : (m : ℚ) ≤ (i : ℚ) := by exact_mod_cast hmmin i hi
                exact inv_anti₀ hmQ hmi
            _ = (s.card : ℚ) * (m : ℚ)⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
        have hinvm : (m : ℚ)⁻¹ ≤ 1 / D := by
          rw [inv_eq_one_div]
          exact one_div_le_one_div_of_le hDpos hmD
        have hhalf : (∑ n ∈ s, (n : ℚ)⁻¹) ≤ 1 / (2 * (q : ℚ)) := by
          have hstep : (s.card : ℚ) * (m : ℚ)⁻¹ ≤ ((k : ℚ) + 1) * (1 / D) :=
            mul_le_mul hcardQ hinvm (by positivity) (by linarith)
          have hfin : ((k : ℚ) + 1) * (1 / D) ≤ 1 / (2 * (q : ℚ)) := by
            rw [mul_one_div, div_le_div_iff₀ hDpos (by positivity)]
            rw [hD]; nlinarith
          linarith
        have hpq : (1 : ℚ) / q ≤ (p : ℚ) / q := by gcongr
        have hkey : (1 : ℚ) / (2 * (q : ℚ)) ≤ (p : ℚ) / q - ∑ n ∈ s, (n : ℚ)⁻¹ := by
          have harith : (1 : ℚ) / q - 1 / (2 * q) = 1 / (2 * q) := by field_simp; ring
          linarith
        refine le_trans ?_ hkey
        apply one_div_le_one_div_of_le (by positivity)
        have h2q : (2 : ℚ) * q ≤ D := by rw [hD]; nlinarith
        exact h2q.trans (hpowmono _ hpow1)
      · -- otherwise remove the smallest denominator and apply the inductive hypothesis
        push_neg at hcase
        have hmDlt : (m : ℚ) ≤ D := by
          have hc : (m : ℚ) ≤ (((2 * (k + 2) * q : ℕ)) : ℚ) := by exact_mod_cast hcase.le
          push_cast at hc
          rw [hD]; linarith
        have hlt1 : (m : ℚ)⁻¹ < (p : ℚ) / q := lt_of_le_of_lt hmem hsum
        have hnat : q < p * m := by
          rw [inv_eq_one_div, div_lt_div_iff₀ hmQ hqQ] at hlt1
          have hc : (q : ℚ) < (p : ℚ) * m := by linarith
          exact_mod_cast hc
        have hp'pos : 0 < p * m - q := by omega
        have hq'pos : 0 < q * m := by positivity
        have hq'Q : (0 : ℚ) < ((q * m : ℕ) : ℚ) := by exact_mod_cast hq'pos
        have hident : ((p * m - q : ℕ) : ℚ) / ((q * m : ℕ) : ℚ) = (p : ℚ) / q - (m : ℚ)⁻¹ := by
          have hc : ((p * m - q : ℕ) : ℚ) = (p : ℚ) * m - q := by
            rw [Nat.cast_sub hnat.le]; push_cast; ring
          rw [hc]; push_cast; field_simp
        have hcard' : (s.erase m).card ≤ k := by
          have h := Finset.card_erase_of_mem hm
          have hpos : 1 ≤ s.card := Finset.card_pos.2 hne
          omega
        have h2' : ∀ n ∈ s.erase m, 2 ≤ n := fun n hn => h2 n (Finset.mem_of_mem_erase hn)
        have hsum' : ∑ n ∈ s.erase m, (n : ℚ)⁻¹ = (∑ n ∈ s, (n : ℚ)⁻¹) - (m : ℚ)⁻¹ :=
          Finset.sum_erase_eq_sub hm
        have hlt' : ∑ n ∈ s.erase m, (n : ℚ)⁻¹ < ((p * m - q : ℕ) : ℚ) / ((q * m : ℕ) : ℚ) := by
          rw [hsum', hident]; linarith
        have hIH := IH (p * m - q) (q * m) (s.erase m) hp'pos hq'pos h2' hcard' hlt'
        rw [hsum', hident] at hIH
        refine le_trans ?_ (by linarith [hIH] :
            (1 : ℚ) / (2 * ((k : ℚ) + 1) * ((q * m : ℕ) : ℚ)) ^ (4 ^ k)
              ≤ (p : ℚ) / q - ∑ n ∈ s, (n : ℚ)⁻¹)
        apply one_div_le_one_div_of_le (by positivity)
        have hbb : 2 * ((k : ℚ) + 1) * ((q * m : ℕ) : ℚ) ≤ D ^ 4 := by
          have hq'cast : ((q * m : ℕ) : ℚ) = (q : ℚ) * m := by push_cast; ring
          have hD2 : D ^ 2 ≤ D ^ 4 := pow_le_pow_right₀ hD1 (by norm_num)
          have hstep : 2 * ((k : ℚ) + 1) * ((q : ℚ) * m) ≤ D * D := by
            have h1 : 2 * ((k : ℚ) + 1) * (q : ℚ) ≤ D := by rw [hD]; nlinarith
            nlinarith [hmQ, hmDlt, hDpos]
          rw [hq'cast]
          nlinarith [hstep, hD2]
        have hfinal : (2 * ((k : ℚ) + 1) * ((q * m : ℕ) : ℚ)) ^ (4 ^ k) ≤ (D ^ 4) ^ (4 ^ k) :=
          pow_le_pow_left₀ (by positivity) hbb _
        have hexp : (D ^ 4) ^ (4 ^ k) = D ^ (4 ^ (k + 1)) := by
          rw [← pow_mul]
          congr 1
          rw [pow_succ]
          ring
        rw [hexp] at hfinal
        exact hfinal

/-- If `3 ≤ b ≤ (2 (k+1)) ^ (4 ^ k)`, then `log log b ≤ 6 k`. -/
theorem log_log_le_of_le_tower (b k : ℕ) (hb : 3 ≤ b) (h : b ≤ (2 * (k + 1)) ^ (4 ^ k)) :
    Real.log (Real.log b) ≤ 6 * k := by
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp at h; omega
    · exact hk
  have hbR : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hlogb1 : 1 < Real.log b := by
    have he : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
      _ < Real.log b := Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le he hbR)
  have hlogbase : 0 < Real.log (2 * ((k : ℝ) + 1)) := Real.log_pos (by linarith)
  have hstep1 : Real.log b ≤ (4 : ℝ) ^ k * Real.log (2 * ((k : ℝ) + 1)) := by
    have hcast : (b : ℝ) ≤ ((2 * ((k : ℝ) + 1)) ^ (4 ^ k)) := by
      have hc : ((b : ℕ) : ℝ) ≤ (((2 * (k + 1)) ^ (4 ^ k) : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at hc
      convert hc using 2
    calc Real.log b ≤ Real.log ((2 * ((k : ℝ) + 1)) ^ (4 ^ k)) :=
          Real.log_le_log (by linarith) hcast
      _ = (4 ^ k : ℕ) * Real.log (2 * ((k : ℝ) + 1)) := by rw [Real.log_pow]
      _ = (4 : ℝ) ^ k * Real.log (2 * ((k : ℝ) + 1)) := by push_cast; ring
  have hstep2 : Real.log (Real.log b) ≤ Real.log ((4 : ℝ) ^ k * Real.log (2 * ((k : ℝ) + 1))) :=
    Real.log_le_log (by linarith) hstep1
  rw [Real.log_mul (by positivity) (ne_of_gt hlogbase), Real.log_pow] at hstep2
  have h3 : Real.log (Real.log (2 * ((k : ℝ) + 1))) ≤ Real.log (2 * ((k : ℝ) + 1)) - 1 :=
    Real.log_le_sub_one_of_pos hlogbase
  have h4 : Real.log (2 * ((k : ℝ) + 1)) ≤ 2 * ((k : ℝ) + 1) - 1 :=
    Real.log_le_sub_one_of_pos (by linarith)
  have h5 : Real.log 4 ≤ 1.4 := by
    have hl4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
    have := Real.log_two_lt_d9
    linarith
  nlinarith [hstep2, h3, h4, h5]

end Erdos304Aux


namespace erdos_304.variants.lower_1950_candidate
open Erdos304
open Asymptotics Filter

theorem erdos_304.variants.lower_1950 :
    (fun b : ℕ => Real.log (Real.log b)) =O[atTop]
      (fun b => (smallestCollectionTo b : ℝ)) := by
  rw [Asymptotics.isBigO_iff]
  refine ⟨6, ?_⟩
  filter_upwards [Filter.eventually_ge_atTop 3] with b hb
  have hb2 : 2 ≤ b := by omega
  have hbQ : (0 : ℚ) < (b : ℚ) := by positivity
  -- The fraction `(b-1)/b` is representable as a sum of distinct unit fractions.
  have hfrac : ((b - 1 : ℕ) : ℚ) / (b : ℚ) < 1 / ((1 : ℕ) : ℚ) := by
    have h1 : ((b - 1 : ℕ) : ℚ) < (b : ℚ) := by
      have : (b - 1 : ℕ) < b := by omega
      exact_mod_cast this
    rw [Nat.cast_one, div_one, div_lt_one hbQ]
    exact h1
  obtain ⟨s0, hs0mem, hs0sum⟩ :=
    Erdos304Aux.exists_unitFraction_repr (b - 1) b 1 (by omega) one_pos (by omega) hfrac
  have hne : (unitFractionExpressible (b - 1) b).Nonempty :=
    ⟨s0.card, s0, rfl, fun n hn => hs0mem n hn, hs0sum⟩
  -- The minimal number of terms in such a representation
  obtain ⟨s, hcard, hgt, hsum⟩ :
      ∃ s : Finset ℕ, s.card = smallestCollection (b - 1) b ∧ (∀ n ∈ s, n > 1) ∧
        ((b - 1 : ℕ) : ℚ) / (b : ℚ) = ∑ n ∈ s, (n : ℚ)⁻¹ :=
    Nat.sInf_mem hne
  set k := smallestCollection (b - 1) b with hkdef
  have hsumval : (∑ n ∈ s, (n : ℚ)⁻¹) = 1 - 1 / (b : ℚ) := by
    rw [← hsum, Nat.cast_sub (by omega : 1 ≤ b)]
    push_cast
    field_simp
  have hsum1 : (∑ n ∈ s, (n : ℚ)⁻¹) < ((1 : ℕ) : ℚ) / ((1 : ℕ) : ℚ) := by
    rw [hsumval]
    have : (0 : ℚ) < 1 / (b : ℚ) := by positivity
    push_cast
    linarith
  have hkey := Erdos304Aux.key_bound k 1 1 s one_pos one_pos
    (fun n hn => hgt n hn) hcard.le hsum1
  rw [hsumval] at hkey
  -- Hence `b ≤ (2 (k+1)) ^ (4 ^ k)`
  push_cast at hkey
  rw [mul_one] at hkey
  have hXpos : (0 : ℚ) < (2 * ((k : ℚ) + 1)) ^ (4 ^ k) := by positivity
  have h1 : (1 : ℚ) / (2 * ((k : ℚ) + 1)) ^ (4 ^ k) ≤ 1 / (b : ℚ) := by linarith
  rw [div_le_div_iff₀ hXpos hbQ] at h1
  have hbnat : b ≤ (2 * (k + 1)) ^ (4 ^ k) := by
    have h2 : ((b : ℕ) : ℚ) ≤ (((2 * (k + 1)) ^ (4 ^ k) : ℕ) : ℚ) := by push_cast; linarith
    exact_mod_cast h2
  have hloglog : Real.log (Real.log b) ≤ 6 * k :=
    Erdos304Aux.log_log_le_of_le_tower b k hb hbnat
  -- `k` is at most the maximum `N(b)`
  have hkle : k ≤ smallestCollectionTo b := by
    have hfin : {x | ∃ a ∈ Finset.Ico 1 b, smallestCollection a b = x} =
        ↑((Finset.Ico 1 b).image (fun a => smallestCollection a b)) := by
      ext x
      simp [eq_comm]
    have hbdd : BddAbove {x | ∃ a ∈ Finset.Ico 1 b, smallestCollection a b = x} := by
      rw [hfin]
      exact (Finset.finite_toSet _).bddAbove
    have hmem : k ∈ {x | ∃ a ∈ Finset.Ico 1 b, smallestCollection a b = x} :=
      ⟨b - 1, by simp only [Finset.mem_Ico]; omega, rfl⟩
    exact le_csSup hbdd hmem
  -- Conclusion
  have hlognonneg : 0 ≤ Real.log (Real.log b) := by
    have hbR : (3 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
    have he : Real.exp 1 < 3 := by
      have := Real.exp_one_lt_d9
      linarith
    have h1 : 1 < Real.log b := by
      calc (1 : ℝ) = Real.log (Real.exp 1) := by rw [Real.log_exp]
        _ < Real.log b := Real.log_lt_log (Real.exp_pos 1) (lt_of_lt_of_le he hbR)
    exact Real.log_nonneg h1.le
  have hkleR : (k : ℝ) ≤ (smallestCollectionTo b : ℝ) := by exact_mod_cast hkle
  have hNnonneg : (0 : ℝ) ≤ (smallestCollectionTo b : ℝ) := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlognonneg, abs_of_nonneg hNnonneg]
  linarith

end erdos_304.variants.lower_1950_candidate

#print axioms erdos_304.variants.lower_1950_candidate.erdos_304.variants.lower_1950
