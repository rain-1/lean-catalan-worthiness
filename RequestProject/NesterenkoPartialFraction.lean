import RequestProject.NesterenkoCoefficients
import RequestProject.NesterenkoPeriod

/-!
# The concrete Nesterenko partial-fraction bridge

This file follows Sections 1--2 of
`CATALAN_LEAN_NESTERENKO_GAP_CLOSURE_HANDOFF_20260821.txt`.  It isolates the
two rational sequences occurring in the weighted partial-fraction sum and the
finite correction terms.  The eventual central theorem in this file is the
cleared-denominator partial-fraction identity for the concrete `nestA1` and
`nestA2` rows.
-/

namespace Catalan

open Filter Topology
open scoped BigOperators

/-- `a_m = m! / (3/2)_m`. -/
noncomputable def nestPFa (m : ℕ) : ℚ :=
  (Nat.factorial m : ℚ) / nestPochhammerThreeHalves m

/-- `b_m = a_m / (m+1/2)`, the Nielsen special-value summand. -/
noncomputable def nestPFb (m : ℕ) : ℚ :=
  nestPFa m / ((m : ℚ) + 1 / 2)

/-- The finite `a`-correction attached to the `j`-th simple pole. -/
noncomputable def nestPFc1 (j : ℕ) : ℚ :=
  ∑ m ∈ Finset.range j, nestPFa m

/-- The finite `b`-correction attached to the `j`-th double pole. -/
noncomputable def nestPFc2 (j : ℕ) : ℚ :=
  ∑ m ∈ Finset.range j, nestPFb m

@[simp] lemma nestPFb_eq_nestF2Term (m : ℕ) :
    nestPFb m = nestF2Term m := by
  rfl

lemma nestRWeight_eq (m : ℕ) :
    nestRWeight m = ((m : ℚ) + 1 / 2) * nestPFa m := by
  rw [nestRWeight, nestPFa]
  ring

/-- Natural-evaluation form of Nesterenko's basis function
`F_j(t)=(t+1)_j/(t+1/2)_(j+1)`.  This quotient form makes its interaction
with the weight exact without introducing rational functions prematurely. -/
noncomputable def nestPFBaseAt (t j : ℕ) : ℚ :=
  nestPFa (t + j) / nestRWeight t

lemma nestPFa_ne_zero (m : ℕ) : nestPFa m ≠ 0 := by
  unfold nestPFa
  apply div_ne_zero
  · positivity
  · rw [nestPochhammerThreeHalves_eq]
    positivity

lemma nestPFb_ne_zero (m : ℕ) : nestPFb m ≠ 0 := by
  rw [nestPFb]
  exact div_ne_zero (nestPFa_ne_zero m) (by positivity)

/-- Equation (2.2): multiplying a basis term by the Nesterenko weight shifts
the `a` sequence. -/
theorem nestRWeight_mul_nestPFBaseAt (t j : ℕ) :
    nestRWeight t * nestPFBaseAt t j = nestPFa (t + j) := by
  rw [nestPFBaseAt]
  field_simp [nestRWeight_ne_zero]

/-- Equation (2.3): the corresponding double-pole term shifts `b`. -/
theorem nestRWeight_mul_nestPFBaseAt_div (t j : ℕ) :
    nestRWeight t *
        (nestPFBaseAt t j / (((t + j : ℕ) : ℚ) + 1 / 2)) =
      nestPFb (t + j) := by
  rw [nestPFb, nestPFBaseAt]
  field_simp [nestRWeight_ne_zero]

/-- Multiplying a pointwise partial-fraction identity by the Nesterenko
weight puts it in the shifted `a,b` form required by the universal summation
lemma. -/
theorem nest_weighted_eq_shifted_of_pf (n t : ℕ)
    (hPF : nestRAt n t =
      ∑ j ∈ Finset.range (3 * n + 1),
        nestPFBaseAt t j *
          (nestA1 n j + nestA2 n j / (((t + j : ℕ) : ℚ) + 1 / 2))) :
    nestRWeight t * nestRAt n t =
      ∑ j ∈ Finset.range (3 * n + 1),
        (nestA1 n j * nestPFa (t + j) +
          nestA2 n j * nestPFb (t + j)) := by
  rw [hPF, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  calc
    nestRWeight t *
        (nestPFBaseAt t j *
          (nestA1 n j + nestA2 n j / (((t + j : ℕ) : ℚ) + 1 / 2))) =
      nestA1 n j * (nestRWeight t * nestPFBaseAt t j) +
        nestA2 n j * (nestRWeight t *
          (nestPFBaseAt t j / (((t + j : ℕ) : ℚ) + 1 / 2))) := by ring
    _ = _ := by
      rw [nestRWeight_mul_nestPFBaseAt,
        nestRWeight_mul_nestPFBaseAt_div]

/-- The nested audited definition of `C_n` is exactly the finite correction
`sum_j (c1(j) A1_j + c2(j) A2_j)`. -/
theorem nestCConcrete_eq_corrections (n : ℕ) :
    nestCConcrete n =
      ∑ j ∈ Finset.range (3 * n + 1),
        (nestPFc1 j * nestA1 n j + nestPFc2 j * nestA2 n j) := by
  rw [nestCConcrete_eq]
  apply Finset.sum_congr rfl
  intro j _
  rw [nestPFc1, nestPFc2, Finset.sum_mul, Finset.sum_mul]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  simp only [nestPFa, nestPFb]
  ring

end Catalan
