import RequestProject.NesterenkoWeightedBridge
import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Cleared polynomial form of the Nesterenko partial fractions

The definitions here contain no division.  In particular, coefficient
comparison at degree `6n+1` proves `sum A₁ = 0` as soon as the cleared finite
partial-fraction identity is established.
-/

namespace Catalan

open scoped BigOperators
open Polynomial

noncomputable def nestPFLin (j : ℕ) : ℚ[X] :=
  X + C ((j : ℚ) + 1 / 2)

noncomputable def nestPFNum (j : ℕ) : ℚ[X] :=
  ∏ r ∈ Finset.range j, (X + C ((r : ℚ) + 1))

noncomputable def nestPFPrefix (j : ℕ) : ℚ[X] :=
  ∏ r ∈ Finset.range j, nestPFLin r

noncomputable def nestPFTailSq (n j : ℕ) : ℚ[X] :=
  ∏ r ∈ Finset.range (3 * n - j), (nestPFLin (j + 1 + r)) ^ 2

/-- The monic polynomial left after clearing denominators in an `A₁` term. -/
noncomputable def nestPFShape1 (n j : ℕ) : ℚ[X] :=
  nestPFNum j * nestPFPrefix (j + 1) * nestPFTailSq n j

/-- The monic polynomial left after clearing denominators in an `A₂` term. -/
noncomputable def nestPFShape2 (n j : ℕ) : ℚ[X] :=
  nestPFNum j * nestPFPrefix j * nestPFTailSq n j

noncomputable def nestPFClearedR (n : ℕ) : ℚ[X] :=
  C ((Nat.factorial (3 * n) : ℚ) *
      nestPochhammerThreeHalves (3 * n - 1) /
      (Nat.factorial (4 * n) : ℚ)) *
    ∏ r ∈ Finset.range (4 * n), (X - C (r : ℚ))

noncomputable def nestPFClearedRHS (n : ℕ) : ℚ[X] :=
  ∑ j ∈ Finset.range (3 * n + 1),
    (C (nestA1 n j) * nestPFShape1 n j +
      C (nestA2 n j) * nestPFShape2 n j)

lemma nestPFLin_monic (j : ℕ) : (nestPFLin j).Monic := by
  exact monic_X_add_C _

lemma nestPFLin_natDegree (j : ℕ) : (nestPFLin j).natDegree = 1 := by
  exact natDegree_X_add_C _

lemma nestPFNum_monic (j : ℕ) : (nestPFNum j).Monic := by
  unfold nestPFNum
  exact monic_prod_of_monic _ _ fun _ _ => monic_X_add_C _

lemma nestPFPrefix_monic (j : ℕ) : (nestPFPrefix j).Monic := by
  unfold nestPFPrefix
  exact monic_prod_of_monic _ _ fun r _ => nestPFLin_monic r

lemma nestPFTailSq_monic (n j : ℕ) : (nestPFTailSq n j).Monic := by
  unfold nestPFTailSq
  exact monic_prod_of_monic _ _ fun r _ => (nestPFLin_monic _).pow _

lemma nestPFNum_natDegree (j : ℕ) : (nestPFNum j).natDegree = j := by
  unfold nestPFNum
  rw [natDegree_prod_of_monic]
  · simp only [natDegree_X_add_C]
    simp
  · exact fun _ _ => monic_X_add_C _

lemma nestPFPrefix_natDegree (j : ℕ) : (nestPFPrefix j).natDegree = j := by
  unfold nestPFPrefix
  rw [natDegree_prod_of_monic]
  · simp only [nestPFLin_natDegree]
    simp
  · exact fun r _ => nestPFLin_monic r

lemma nestPFTailSq_natDegree (n j : ℕ) :
    (nestPFTailSq n j).natDegree = 2 * (3 * n - j) := by
  unfold nestPFTailSq
  rw [natDegree_prod_of_monic]
  · simp only [(nestPFLin_monic _).natDegree_pow, nestPFLin_natDegree,
      mul_one]
    simp
    omega
  · exact fun r _ => (nestPFLin_monic _).pow _

lemma nestPFShape1_monic (n j : ℕ) : (nestPFShape1 n j).Monic := by
  unfold nestPFShape1
  exact ((nestPFNum_monic j).mul (nestPFPrefix_monic (j + 1))).mul
    (nestPFTailSq_monic n j)

lemma nestPFShape2_monic (n j : ℕ) : (nestPFShape2 n j).Monic := by
  unfold nestPFShape2
  exact ((nestPFNum_monic j).mul (nestPFPrefix_monic j)).mul
    (nestPFTailSq_monic n j)

lemma nestPFShape1_natDegree (n j : ℕ) (hj : j ≤ 3 * n) :
    (nestPFShape1 n j).natDegree = 6 * n + 1 := by
  rw [nestPFShape1,
    ((nestPFNum_monic j).mul (nestPFPrefix_monic (j + 1))).natDegree_mul
      (nestPFTailSq_monic n j),
    (nestPFNum_monic j).natDegree_mul (nestPFPrefix_monic (j + 1)),
    nestPFNum_natDegree, nestPFPrefix_natDegree, nestPFTailSq_natDegree]
  omega

lemma nestPFShape2_natDegree (n j : ℕ) (hj : j ≤ 3 * n) :
    (nestPFShape2 n j).natDegree = 6 * n := by
  rw [nestPFShape2,
    ((nestPFNum_monic j).mul (nestPFPrefix_monic j)).natDegree_mul
      (nestPFTailSq_monic n j),
    (nestPFNum_monic j).natDegree_mul (nestPFPrefix_monic j),
    nestPFNum_natDegree, nestPFPrefix_natDegree, nestPFTailSq_natDegree]
  omega

lemma nestPFClearedR_top_coeff (n : ℕ) (hn : 1 ≤ n) :
    (nestPFClearedR n).coeff (6 * n + 1) = 0 := by
  rw [nestPFClearedR, coeff_C_mul]
  have hmonic :
      (∏ r ∈ Finset.range (4 * n), (X - C (r : ℚ))).Monic :=
    monic_prod_of_monic _ _ fun r _ => monic_X_sub_C _
  have hdeg :
      (∏ r ∈ Finset.range (4 * n), (X - C (r : ℚ))).natDegree = 4 * n := by
    rw [natDegree_prod_of_monic]
    · simp only [natDegree_X_sub_C]
      simp
    · exact fun r _ => monic_X_sub_C _
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; omega), mul_zero]

/-! ### Values at the double poles -/

lemma eval_nestPFLin_at_pole (j r : ℕ) :
    (nestPFLin r).eval (-((j : ℚ) + 1 / 2)) = (r : ℚ) - j := by
  simp [nestPFLin]
  ring

lemma eval_nestPFPrefix_at_pole (j : ℕ) :
    (nestPFPrefix j).eval (-((j : ℚ) + 1 / 2)) =
      (-1 : ℚ) ^ j * (Nat.factorial j : ℚ) := by
  rw [nestPFPrefix, eval_prod]
  simp_rw [eval_nestPFLin_at_pole]
  have heq :
      (∏ r ∈ Finset.range j, ((r : ℚ) - j)) =
        ∏ r ∈ Finset.range j,
          (-(((j - 1 - r) + 1 : ℕ) : ℚ)) := by
    apply Finset.prod_congr rfl
    intro r hr
    have hrj : r < j := Finset.mem_range.mp hr
    rw [show j - 1 - r + 1 = j - r by omega,
      Nat.cast_sub (by omega : r ≤ j)]
    push_cast
    ring
  rw [heq]
  calc
    (∏ r ∈ Finset.range j, (-(((j - 1 - r) + 1 : ℕ) : ℚ))) =
        ∏ r ∈ Finset.range j, (-(((r + 1 : ℕ) : ℚ))) :=
      Finset.prod_range_reflect (fun r : ℕ => (-(((r + 1 : ℕ) : ℚ)))) j
    _ = _ := by
      rw [Finset.prod_neg]
      have hfacQ :
          (∏ r ∈ Finset.range j, (((r + 1 : ℕ) : ℚ))) =
            (Nat.factorial j : ℚ) := by
        exact_mod_cast Finset.prod_range_add_one_eq_factorial j
      rw [Finset.card_range, hfacQ]

lemma eval_nestPFNum_at_pole (j : ℕ) :
    (nestPFNum j).eval (-((j : ℚ) + 1 / 2)) =
      (-1 : ℚ) ^ j * nestPochhammer (1 / 2) j := by
  rw [nestPFNum, eval_prod]
  simp only [eval_add, eval_X, eval_C]
  have heq :
      (∏ r ∈ Finset.range j,
        (-((j : ℚ) + 1 / 2) + ((r : ℚ) + 1))) =
        ∏ r ∈ Finset.range j,
          (-(((j - 1 - r : ℕ) : ℚ) + 1 / 2)) := by
    apply Finset.prod_congr rfl
    intro r hr
    have hrj : r < j := Finset.mem_range.mp hr
    rw [Nat.cast_sub (by omega : r ≤ j - 1)]
    push_cast
    have hjcast : (j : ℚ) = ((j - 1 : ℕ) : ℚ) + 1 := by
      exact_mod_cast (show j = j - 1 + 1 by omega)
    rw [hjcast]
    ring
  rw [heq]
  calc
    (∏ r ∈ Finset.range j, (-(((j - 1 - r : ℕ) : ℚ) + 1 / 2))) =
        ∏ r ∈ Finset.range j, (-((r : ℚ) + 1 / 2)) :=
      Finset.prod_range_reflect (fun r : ℕ => (-((r : ℚ) + 1 / 2))) j
    _ = _ := by
      rw [Finset.prod_neg]
      rw [Finset.card_range, nestPochhammer]
      congr 1
      apply Finset.prod_congr rfl
      intro r _
      ring

lemma eval_nestPFTailSq_at_pole (n j : ℕ) (hj : j ≤ 3 * n) :
    (nestPFTailSq n j).eval (-((j : ℚ) + 1 / 2)) =
      (Nat.factorial (3 * n - j) : ℚ) ^ 2 := by
  rw [nestPFTailSq, eval_prod]
  simp_rw [eval_pow, eval_nestPFLin_at_pole]
  have heq :
      (∏ r ∈ Finset.range (3 * n - j),
        (((j + 1 + r : ℕ) : ℚ) - j) ^ 2) =
        ∏ r ∈ Finset.range (3 * n - j), (((r + 1 : ℕ) : ℚ) ^ 2) := by
    apply Finset.prod_congr rfl
    intro r _
    push_cast
    ring
  rw [heq]
  calc
    (∏ r ∈ Finset.range (3 * n - j), (((r + 1 : ℕ) : ℚ) ^ 2)) =
        (∏ r ∈ Finset.range (3 * n - j), (((r + 1 : ℕ) : ℚ))) ^ 2 := by
      rw [Finset.prod_pow]
    _ = _ := by
      have hfacQ :
          (∏ r ∈ Finset.range (3 * n - j), (((r + 1 : ℕ) : ℚ))) =
            (Nat.factorial (3 * n - j) : ℚ) := by
        exact_mod_cast Finset.prod_range_add_one_eq_factorial (3 * n - j)
      rw [hfacQ]

lemma eval_nestPFShape2_at_pole (n j : ℕ) (hj : j ≤ 3 * n) :
    (nestPFShape2 n j).eval (-((j : ℚ) + 1 / 2)) =
      nestPochhammer (1 / 2) j * (Nat.factorial j : ℚ) *
        (Nat.factorial (3 * n - j) : ℚ) ^ 2 := by
  rw [nestPFShape2, eval_mul, eval_mul, eval_nestPFNum_at_pole,
    eval_nestPFPrefix_at_pole, eval_nestPFTailSq_at_pole n j hj]
  have hs : (-1 : ℚ) ^ j * (-1 : ℚ) ^ j = 1 := by
    rw [← pow_add]
    norm_num
  calc
    ((-1 : ℚ) ^ j * nestPochhammer (1 / 2) j) *
          ((-1 : ℚ) ^ j * (Nat.factorial j : ℚ)) *
          (Nat.factorial (3 * n - j) : ℚ) ^ 2 =
        ((-1 : ℚ) ^ j * (-1 : ℚ) ^ j) * nestPochhammer (1 / 2) j *
          (Nat.factorial j : ℚ) * (Nat.factorial (3 * n - j) : ℚ) ^ 2 := by ring
    _ = _ := by rw [hs, one_mul]

lemma eval_nestPFClearedR_at_pole (n j : ℕ) :
    (nestPFClearedR n).eval (-((j : ℚ) + 1 / 2)) =
      ((Nat.factorial (3 * n) : ℚ) *
        nestPochhammerThreeHalves (3 * n - 1) /
        (Nat.factorial (4 * n) : ℚ)) *
        nestPochhammer ((j : ℚ) + 1 / 2) (4 * n) := by
  rw [nestPFClearedR, eval_mul, eval_C, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  have heq :
      (∏ r ∈ Finset.range (4 * n),
        (-((j : ℚ) + 1 / 2) - (r : ℚ))) =
        ∏ r ∈ Finset.range (4 * n), (((j : ℚ) + 1 / 2) + r) := by
    simp_rw [show ∀ r : ℕ,
        -((j : ℚ) + 1 / 2) - (r : ℚ) =
          (-1 : ℚ) * (((j : ℚ) + 1 / 2) + r) by intro r; ring,
      Finset.prod_mul_distrib]
    have hneg : (∏ _r ∈ Finset.range (4 * n), (-1 : ℚ)) = 1 := by
      simp [show 4 * n = 2 * (2 * n) by omega, pow_mul]
    rw [hneg, one_mul]
  rw [heq]
  rfl

lemma nestPochhammer_nat_add_half_eq (j k : ℕ) :
    nestPochhammer ((j : ℚ) + 1 / 2) k =
      (Nat.factorial (2 * (j + k)) : ℚ) * (4 : ℚ) ^ j *
          (Nat.factorial j : ℚ) /
        ((4 : ℚ) ^ (j + k) * (Nat.factorial (j + k) : ℚ) *
          (Nat.factorial (2 * j) : ℚ)) := by
  have hsplit := nestPochhammer_add (1 / 2 : ℚ) j k
  rw [show (1 / 2 : ℚ) + (j : ℕ) = (j : ℚ) + 1 / 2 by
    push_cast; ring, nestPochhammer_one_half_eq,
    nestPochhammer_one_half_eq] at hsplit
  field_simp at hsplit ⊢
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hsplit.symm

/-- Direct extraction of the audited positive double-pole coefficient. -/
theorem nestA2_double_pole_value (n j : ℕ) (hn : 1 ≤ n)
    (hj : j ≤ 3 * n) :
    (nestPFClearedR n).eval (-((j : ℚ) + 1 / 2)) =
      nestA2 n j *
        (nestPFShape2 n j).eval (-((j : ℚ) + 1 / 2)) := by
  rw [eval_nestPFClearedR_at_pole, eval_nestPFShape2_at_pole n j hj,
    nestPochhammer_nat_add_half_eq, nestPochhammer_one_half_eq,
    nestPochhammerThreeHalves_eq, nestA2]
  rw [show 2 * (j + 4 * n) = 8 * n + 2 * j by omega,
    show j + 4 * n = 4 * n + j by omega]
  have hpow :
      (2 : ℚ) ^ (-14 * (n : ℤ) + 2 * (j : ℤ) + 1) =
        2 * (4 : ℚ) ^ j / (4 : ℚ) ^ (7 * n) := by
    rw [show (4 : ℚ) = (2 : ℚ) ^ 2 by norm_num, ← pow_mul, ← pow_mul,
      ← zpow_natCast, ← zpow_natCast, div_eq_mul_inv, ← zpow_neg]
    change (2 : ℚ) ^ (-14 * (n : ℤ) + 2 * (j : ℤ) + 1) =
      (2 : ℚ) ^ (1 : ℤ) * (2 : ℚ) ^ ((2 * j : ℕ) : ℤ) *
        (2 : ℚ) ^ (-((2 * (7 * n) : ℕ) : ℤ))
    rw [← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0),
      ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
    push_cast
    congr 1
    ring
  rw [hpow]
  have hfac3 : Nat.factorial (3 * n) =
      (3 * n) * Nat.factorial (3 * n - 1) := by
    calc
      Nat.factorial (3 * n) = Nat.factorial ((3 * n - 1) + 1) := by
        congr 2 <;> omega
      _ = ((3 * n - 1) + 1) * Nat.factorial (3 * n - 1) :=
        Nat.factorial_succ _
      _ = _ := by congr 1 <;> omega
  have hfac6 : Nat.factorial (6 * n) =
      (6 * n) * Nat.factorial (6 * n - 1) := by
    calc
      Nat.factorial (6 * n) = Nat.factorial ((6 * n - 1) + 1) := by
        congr 2 <;> omega
      _ = ((6 * n - 1) + 1) * Nat.factorial (6 * n - 1) :=
        Nat.factorial_succ _
      _ = _ := by congr 1 <;> omega
  rw [hfac3, hfac6]
  push_cast
  field_simp
  rw [show 2 * (3 * n - 1) + 1 = 6 * n - 1 by omega,
    show 7 * n = 4 * n + 3 * n by omega, pow_add,
    show 4 * n + j = 4 * n + j by rfl, pow_add,
    show 3 * n = (3 * n - 1) + 1 by omega, pow_succ]
  rw [show 3 * n - 1 + 1 - 1 = 3 * n - 1 by omega]
  ring

lemma nestPFShape1_top_coeff (n j : ℕ) (hj : j ≤ 3 * n) :
    (C (nestA1 n j) * nestPFShape1 n j).coeff (6 * n + 1) =
      nestA1 n j := by
  rw [coeff_C_mul, ← nestPFShape1_natDegree n j hj,
    (nestPFShape1_monic n j).coeff_natDegree, mul_one]

lemma nestPFShape2_top_coeff (n j : ℕ) (hj : j ≤ 3 * n) :
    (C (nestA2 n j) * nestPFShape2 n j).coeff (6 * n + 1) = 0 := by
  rw [coeff_C_mul, Polynomial.coeff_eq_zero_of_natDegree_lt (by
    rw [nestPFShape2_natDegree n j hj]
    omega), mul_zero]

/-- Equation (2.4) of the handoff: coefficient comparison in any proved
cleared PF identity forces the sum of the simple-pole row to vanish. -/
theorem nest_sum_A1_eq_zero_of_cleared (n : ℕ) (hn : 1 ≤ n)
    (hcleared : nestPFClearedR n = nestPFClearedRHS n) :
    ∑ j ∈ Finset.range (3 * n + 1), nestA1 n j = 0 := by
  have hcoeff := congrArg (fun p : ℚ[X] => p.coeff (6 * n + 1)) hcleared
  rw [nestPFClearedR_top_coeff n hn, nestPFClearedRHS,
    Polynomial.finsetSum_coeff] at hcoeff
  simp_rw [coeff_add] at hcoeff
  have hterms : ∀ j ∈ Finset.range (3 * n + 1),
      (C (nestA1 n j) * nestPFShape1 n j).coeff (6 * n + 1) +
          (C (nestA2 n j) * nestPFShape2 n j).coeff (6 * n + 1) =
        nestA1 n j := by
    intro j hj
    have hjle : j ≤ 3 * n := by
      have := Finset.mem_range.mp hj
      omega
    rw [nestPFShape1_top_coeff n j hjle,
      nestPFShape2_top_coeff n j hjle, add_zero]
  calc
    (∑ j ∈ Finset.range (3 * n + 1), nestA1 n j) =
        ∑ j ∈ Finset.range (3 * n + 1),
          ((C (nestA1 n j) * nestPFShape1 n j).coeff (6 * n + 1) +
            (C (nestA2 n j) * nestPFShape2 n j).coeff (6 * n + 1)) := by
      apply Finset.sum_congr rfl
      intro j hj
      exact (hterms j hj).symm
    _ = 0 := hcoeff.symm

end Catalan
