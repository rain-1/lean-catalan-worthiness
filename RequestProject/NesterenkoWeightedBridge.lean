import RequestProject.WeightedPFSum
import RequestProject.NesterenkoSpecialValue
import RequestProject.CatalanIntegral

/-!
# Analytic specializations of the weighted partial-fraction lemma

This file identifies the two elementary coefficient sequences over `ℝ` and
`ℚ_[2]`.  The final concrete bridge will only need the finite rational
partial-fraction identity and `sum A₁ = 0` from the algebraic module.
-/

namespace Catalan

open Filter Topology
open scoped BigOperators

lemma nestPFa_cast_real_eq_uR (m : ℕ) :
    ((nestPFa m : ℚ) : ℝ) = uR m := by
  rw [nestPFa_factorial]
  unfold uR Nat.centralBinom
  have hfac := Nat.choose_mul_factorial_mul_factorial
    (n := 2 * m) (k := m) (by omega)
  have hfacR := congrArg (fun z : ℕ => (z : ℝ)) hfac
  push_cast at hfacR
  rw [show 2 * m - m = m by omega] at hfacR
  rw [show Nat.factorial (2 * m + 1) =
      (2 * m + 1) * Nat.factorial (2 * m) by
    exact Nat.factorial_succ (2 * m)]
  have hchoose : (((2 * m).choose m : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (by omega : m ≤ 2 * m)
  push_cast
  field_simp [hchoose]
  nlinarith [hfacR]

lemma nestPFb_cast_real_eq_two_mul_wR (m : ℕ) :
    ((nestPFb m : ℚ) : ℝ) = 2 * wR m := by
  rw [nestPFb]
  push_cast
  change ((nestPFa m : ℚ) : ℝ) / ((m : ℝ) + 1 / 2) = 2 * wR m
  rw [nestPFa_cast_real_eq_uR, wR_eq_uR_div]
  push_cast
  field_simp

lemma summable_nestPFb_real :
    Summable (fun m : ℕ => ((nestPFb m : ℚ) : ℝ)) := by
  have h := summable_wR.mul_left 2
  exact h.congr fun m => (nestPFb_cast_real_eq_two_mul_wR m).symm

theorem tsum_nestPFb_real :
    (∑' m : ℕ, ((nestPFb m : ℚ) : ℝ)) = 4 * catalanReal := by
  rw [show (∑' m : ℕ, ((nestPFb m : ℚ) : ℝ)) =
      ∑' m : ℕ, 2 * wR m by
    apply tsum_congr
    exact nestPFb_cast_real_eq_two_mul_wR]
  rw [tsum_mul_left, tsum_wR]
  ring

lemma tendsto_nestPFa_real :
    Tendsto (fun m : ℕ => ((nestPFa m : ℚ) : ℝ)) atTop (𝓝 0) := by
  rw [show (fun m : ℕ => ((nestPFa m : ℚ) : ℝ)) = uR by
    funext m
    exact nestPFa_cast_real_eq_uR m]
  have hbound (m : ℕ) :
      0 ≤ uR m ∧ uR m ≤ Real.sqrt (4 * (m : ℝ) + 1) / (2 * m + 1) := by
    constructor
    · exact (uR_pos m).le
    · have hs := sixteen_pow_le_centralBinom_sq m
      have hc := centralBinom_cast_pos m
      have hp : (0 : ℝ) < (4 : ℝ) ^ m := by positivity
      have hroot : (4 : ℝ) ^ m ≤
          (Nat.centralBinom m : ℝ) * Real.sqrt (4 * (m : ℝ) + 1) := by
        have hsqrt : 0 ≤ Real.sqrt (4 * (m : ℝ) + 1) := Real.sqrt_nonneg _
        have hsq : ((4 : ℝ) ^ m) ^ 2 ≤
            ((Nat.centralBinom m : ℝ) * Real.sqrt (4 * (m : ℝ) + 1)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt (by positivity)]
          rw [show (16 : ℝ) ^ m = ((4 : ℝ) ^ m) ^ 2 by
            calc
              (16 : ℝ) ^ m = ((4 : ℝ) ^ 2) ^ m := by norm_num
              _ = (4 : ℝ) ^ (2 * m) := by rw [pow_mul]
              _ = (4 : ℝ) ^ (m * 2) := by rw [Nat.mul_comm]
              _ = ((4 : ℝ) ^ m) ^ 2 := by rw [pow_mul]] at hs
          exact hs
        exact (sq_le_sq₀ hp.le (mul_nonneg hc.le hsqrt)).mp hsq
      unfold uR
      rw [div_le_div_iff₀ (by positivity :
        0 < (2 * (m : ℝ) + 1) * (Nat.centralBinom m : ℝ))
        (by positivity : 0 < 2 * (m : ℝ) + 1)]
      nlinarith [hroot]
  have hsqrt : Tendsto (fun m : ℕ =>
      Real.sqrt (4 * (m : ℝ) + 1) / (2 * m + 1)) atTop (𝓝 0) := by
    let g : ℕ → ℝ := fun m =>
      Real.sqrt (4 / (m : ℝ) + 1 / (m : ℝ) ^ 2) /
        (2 + 1 / (m : ℝ))
    have hrewrite : (fun m : ℕ =>
        Real.sqrt (4 * (m : ℝ) + 1) / (2 * m + 1)) =ᶠ[atTop] g := by
      filter_upwards [Filter.eventually_gt_atTop 0] with m hm
      have hm0 : m ≠ 0 := Nat.ne_of_gt hm
      have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
      dsimp [g]
      rw [show Real.sqrt (4 * (m : ℝ) + 1) =
          (m : ℝ) * Real.sqrt (4 / (m : ℝ) + 1 / (m : ℝ) ^ 2) by
        rw [show 4 * (m : ℝ) + 1 = (m : ℝ) ^ 2 *
            (4 / (m : ℝ) + 1 / (m : ℝ) ^ 2) by
          field_simp,
          Real.sqrt_mul (sq_nonneg (m : ℝ)), Real.sqrt_sq_eq_abs,
          abs_of_pos (by exact_mod_cast hm)]]
      field_simp
    have hone : Tendsto (fun m : ℕ => (1 : ℝ) / m) atTop (𝓝 0) :=
      tendsto_one_div_atTop_nhds_zero_nat
    have hins : Tendsto (fun m : ℕ =>
        4 / (m : ℝ) + 1 / (m : ℝ) ^ 2) atTop (𝓝 0) := by
      convert (hone.const_mul 4).add (hone.pow 2) using 1 <;>
        simp [div_eq_mul_inv]
    have hg : Tendsto g atTop (𝓝 0) := by
      change Tendsto
        ((fun m : ℕ => Real.sqrt (4 / (m : ℝ) + 1 / (m : ℝ) ^ 2)) /
          (fun m : ℕ => 2 + 1 / (m : ℝ))) atTop (𝓝 0)
      have htwo : (2 : ℝ) ≠ 0 := by norm_num
      have hden : Tendsto (fun m : ℕ => 2 + 1 / (m : ℝ)) atTop (𝓝 (2 : ℝ)) := by
        simpa using
          ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).add hone)
      simpa [Function.comp_def] using
        (((Real.continuous_sqrt.tendsto 0).comp hins).div hden htwo)
    exact hg.congr' hrewrite.symm
  exact squeeze_zero' (Eventually.of_forall fun m => (hbound m).1)
    (Eventually.of_forall fun m => (hbound m).2) hsqrt

lemma hasSum_nestPFb_padic :
    HasSum (fun m : ℕ => ((nestPFb m : ℚ) : ℚ_[2])) (4 * GZ2) := by
  rw [show (fun m : ℕ => ((nestPFb m : ℚ) : ℚ_[2])) =
      fun m : ℕ => ((nestF2Term m : ℚ) : ℚ_[2]) by
    funext m
    rw [nestPFb_eq_nestF2Term]]
  rw [← nestF2Padic_eq_four_mul_GZ2]
  exact summable_nestF2Term.hasSum

lemma hasSum_nest_weighted_R_padic (n : ℕ) (hn : 1 ≤ n) :
    HasSum (fun t : ℕ =>
      (((nestRWeight t * nestRAt n t : ℚ) : ℚ_[2]))) (nestJ2 n) := by
  have hshift : HasSum (fun k : ℕ =>
      (((nestRWeight (4 * n + k) * nestRAt n (4 * n + k) : ℚ) : ℚ_[2])))
      (nestJ2 n) := by
    have hs : HasSum (fun k : ℕ => ((nestRSeriesTerm n k : ℚ) : ℚ_[2]))
        (nestJ2 n) := by
      rw [nestJ2_eq_tsum_R n hn]
      exact (summable_nestRSeriesTerm n hn).hasSum
    exact hs.congr_fun fun k => by
      rw [nestRSeriesTerm_eq_weight_mul_R]
  let f : ℕ → ℚ_[2] := fun t =>
    (((nestRWeight t * nestRAt n t : ℚ) : ℚ_[2]))
  have hshift' : HasSum (fun k => f (k + 4 * n)) (nestJ2 n) := by
    convert hshift using 1
    funext k
    dsimp [f]
    rw [Nat.add_comm k]
  have hfull := (hasSum_nat_add_iff (f := f) (4 * n)).1 hshift'
  simpa only [f, show (∑ t ∈ Finset.range (4 * n),
      (((nestRWeight t * nestRAt n t : ℚ) : ℚ_[2]))) = 0 by
    apply Finset.sum_eq_zero
    intro t ht
    rw [nestRAt_eq_zero_of_lt n t (Finset.mem_range.mp ht)]
    norm_num, add_zero] using hfull

/-- Conditional only on the finite rational PF algebra, the `2`-adic period
bridge is forced by the universal summation lemma and the internally proved
Nielsen special value. -/
theorem nestJ2_eq_form_of_partial_fraction (n : ℕ) (hn : 1 ≤ n)
    (hPF : ∀ t, nestRAt n t =
      ∑ j ∈ Finset.range (3 * n + 1),
        nestPFBaseAt t j *
          (nestA1 n j + nestA2 n j / (((t + j : ℕ) : ℚ) + 1 / 2)))
    (hA1 : ∑ j ∈ Finset.range (3 * n + 1), nestA1 n j = 0) :
    nestJ2 n =
      ((4 * nestB n : ℚ) : ℚ_[2]) * GZ2 -
        ((nestCConcrete n : ℚ) : ℚ_[2]) := by
  let a : ℕ → ℚ_[2] := fun m => ((nestPFa m : ℚ) : ℚ_[2])
  let b : ℕ → ℚ_[2] := fun m => ((nestPFb m : ℚ) : ℚ_[2])
  let term : ℕ → ℚ_[2] := fun t =>
    ((nestRWeight t * nestRAt n t : ℚ) : ℚ_[2])
  let A1 : ℕ → ℚ_[2] := fun j => ((nestA1 n j : ℚ) : ℚ_[2])
  let A2 : ℕ → ℚ_[2] := fun j => ((nestA2 n j : ℚ) : ℚ_[2])
  have ha : Tendsto a atTop (𝓝 0) := tendsto_nestPFa_padic
  have hb : HasSum b (4 * GZ2) := hasSum_nestPFb_padic
  have hA1' : ∑ j ∈ Finset.range (3 * n + 1), A1 j = 0 := by
    dsimp [A1]
    exact_mod_cast hA1
  have hterm : ∀ t, term t =
      ∑ j ∈ Finset.range (3 * n + 1),
        (A1 j * a (t + j) + A2 j * b (t + j)) := by
    intro t
    dsimp [term, A1, A2, a, b]
    rw [nest_weighted_eq_shifted_of_pf n t (hPF t)]
    push_cast
    rfl
  have hlim := pf_weighted_partial_sums (3 * n + 1) a b term A1 A2
    (4 * GZ2) ha hb hA1' hterm
  have heq := tendsto_nhds_unique (hasSum_nest_weighted_R_padic n hn).tendsto_sum_nat hlim
  dsimp [term, A1, A2, a, b] at heq
  have hBcast :
      (∑ j ∈ Finset.range (3 * n + 1), ((nestA2 n j : ℚ) : ℚ_[2])) =
        ((nestB n : ℚ) : ℚ_[2]) := by
    rw [nestB]
    push_cast
    rfl
  have hCcast :
      (∑ j ∈ Finset.range (3 * n + 1),
        ((∑ m ∈ Finset.range j, ((nestPFa m : ℚ) : ℚ_[2])) *
            ((nestA1 n j : ℚ) : ℚ_[2]) +
          (∑ m ∈ Finset.range j, ((nestPFb m : ℚ) : ℚ_[2])) *
            ((nestA2 n j : ℚ) : ℚ_[2]))) =
        ((nestCConcrete n : ℚ) : ℚ_[2]) := by
    rw [nestCConcrete_eq_corrections]
    unfold nestPFc1 nestPFc2
    push_cast
    rfl
  rw [hBcast, hCcast] at heq
  push_cast
  linear_combination heq

end Catalan
