import RequestProject.NesterenkoPartialFraction
import RequestProject.Beukers

/-!
# The 2-adic Nielsen special value

This file formalizes Section 5 of the Nesterenko gap-closure handoff.  The
starting sequence is `a_n=n!/(3/2)_n`; its elementary recurrence gives the
first telescoping identity and the convergence needed for the later binomial
adjoint calculation.
-/

namespace Catalan

open Filter Topology
open scoped BigOperators

lemma nestPFa_succ (n : ℕ) :
    nestPFa (n + 1) =
      (2 * ((n : ℚ) + 1) / (2 * (n : ℚ) + 3)) * nestPFa n := by
  change (Nat.factorial (n + 1) : ℚ) / nestPochhammer (3 / 2) (n + 1) =
    (2 * ((n : ℚ) + 1) / (2 * (n : ℚ) + 3)) *
      ((Nat.factorial n : ℚ) / nestPochhammer (3 / 2) n)
  rw [nestPochhammer_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

lemma nestPFa_zero : nestPFa 0 = 1 := by
  norm_num [nestPFa, nestPochhammerThreeHalves, nestPochhammer]

lemma nestPFa_factorial (n : ℕ) :
    nestPFa n =
      (4 : ℚ) ^ n * (Nat.factorial n : ℚ) ^ 2 /
        (Nat.factorial (2 * n + 1) : ℚ) := by
  exact factorial_div_nestPochhammerThreeHalves n

lemma nestPFa_v2 (n : ℕ) :
    padicValRat 2 (nestPFa n) = 2 * (n : ℤ) - (s2 n : ℤ) := by
  rw [show nestPFa n = nestF2Term n * (((n : ℚ) + 1 / 2)) by
    rw [nestF2Term, nestPFa]
    field_simp,
    padicValRat.mul (nestF2Term_ne_zero n) (by positivity), nestF2Term_v2]
  have hhalf : padicValRat 2 ((n : ℚ) + 1 / 2) = -1 := by
    have hodd : Odd (2 * (n : ℤ) + 1) := ⟨n, by ring⟩
    rw [show (n : ℚ) + 1 / 2 = ((2 * (n : ℤ) + 1 : ℤ) : ℚ) / 2 by
      push_cast
      ring,
      padicValRat.div (by
        exact_mod_cast (show (2 * (n : ℤ) + 1) ≠ 0 by omega)) (by norm_num),
      padicValRat_two_of_odd_int hodd]
    have h2 : padicValRat 2 (2 : ℚ) = 1 :=
      padicValRat.self (p := 2) (by norm_num)
    rw [h2]
    norm_num
  rw [hhalf]
  ring

lemma norm_nestPFa_le (n : ℕ) :
    ‖((nestPFa n : ℚ) : ℚ_[2])‖ ≤ (1 / 2 : ℝ) ^ n := by
  rw [norm_ratCast_padic2 (nestPFa_ne_zero n), nestPFa_v2]
  have hs : (s2 n : ℤ) ≤ (n : ℤ) := by exact_mod_cast s2_le n
  rw [show (1 / 2 : ℝ) ^ n = 2 ^ (-(n : ℤ)) by
    rw [div_pow, one_pow, ← zpow_natCast, zpow_neg]
    norm_num]
  exact zpow_le_zpow_right₀ (by norm_num) (by omega)

lemma summable_nestPFa_padic :
    Summable (fun n : ℕ => ((nestPFa n : ℚ) : ℚ_[2])) := by
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact Summable.of_norm_bounded hgeom norm_nestPFa_le

lemma tendsto_nestPFa_padic :
    Tendsto (fun n : ℕ => ((nestPFa n : ℚ) : ℚ_[2])) atTop (𝓝 0) :=
  summable_nestPFa_padic.tendsto_atTop_zero

/-- The first finite telescope from Section 5.1. -/
lemma sum_range_nestPFa (N : ℕ) :
    (∑ n ∈ Finset.range N, nestPFa n) =
      (2 * (N : ℚ) + 1) * nestPFa N - 1 := by
  induction N with
  | zero => simp [nestPFa_zero]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, nestPFa_succ]
      push_cast
      field_simp
      ring

/-- Equation (5.3): `sum a_n=-1` in `Q_2`. -/
theorem tsum_nestPFa_padic :
    (∑' n : ℕ, ((nestPFa n : ℚ) : ℚ_[2])) = -1 := by
  have hpartial := summable_nestPFa_padic.hasSum.tendsto_sum_nat
  have hfactor : Tendsto
      (fun N : ℕ => (((2 * (N : ℚ) + 1) * nestPFa N : ℚ) : ℚ_[2]))
      atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (g := fun N : ℕ => (1 / 2 : ℝ) ^ N)
      (fun N => norm_nonneg _) (fun N => ?_) ?_
    · rw [show ((((2 * (N : ℚ) + 1) * nestPFa N : ℚ) : ℚ_[2])) =
          ((2 * (N : ℚ) + 1 : ℚ) : ℚ_[2]) * ((nestPFa N : ℚ) : ℚ_[2]) by
            push_cast
            ring,
        norm_mul]
      have hodd : Odd (2 * (N : ℤ) + 1) := ⟨N, by ring⟩
      have hnormodd :
          ‖((((2 * (N : ℤ) + 1 : ℤ) : ℚ) : ℚ_[2]))‖ = 1 := by
        rw [norm_ratCast_padic2 (by
            exact_mod_cast (show (2 * (N : ℤ) + 1) ≠ 0 by omega)),
          padicValRat_two_of_odd_int hodd]
        norm_num
      rw [show ((2 * (N : ℚ) + 1 : ℚ) : ℚ_[2]) =
          ((((2 * (N : ℤ) + 1 : ℤ) : ℚ) : ℚ_[2])) by push_cast; ring,
        hnormodd, one_mul]
      exact norm_nestPFa_le N
    · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlimit : Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, ((nestPFa n : ℚ) : ℚ_[2]))
      atTop (𝓝 (-1)) := by
    convert hfactor.sub_const (1 : ℚ_[2]) using 1
    · ext N
      rw [← Rat.cast_sum, sum_range_nestPFa]
      push_cast
      ring
    · norm_num
  exact tendsto_nhds_unique hpartial hlimit

/-! ### Adjoint binomial sums -/

/-- The term `choose(m,r) a_m` in the adjoint tail `S_r`. -/
noncomputable def nestAdjointTerm (r m : ℕ) : ℚ :=
  (Nat.choose m r : ℚ) * nestPFa m

lemma norm_choose_cast_padic_le_one (m r : ℕ) :
    ‖(((Nat.choose m r : ℚ) : ℚ_[2]))‖ ≤ 1 := by
  rw [show (((Nat.choose m r : ℚ) : ℚ_[2])) =
      ((Nat.choose m r : ℤ) : ℚ_[2]) by push_cast; rfl]
  exact Padic.norm_int_le_one _

lemma norm_nestAdjointTerm_le (r m : ℕ) :
    ‖((nestAdjointTerm r m : ℚ) : ℚ_[2])‖ ≤ (1 / 2 : ℝ) ^ m := by
  rw [nestAdjointTerm]
  have hcast : ((((Nat.choose m r : ℚ) * nestPFa m : ℚ) : ℚ_[2])) =
      ((Nat.choose m r : ℚ) : ℚ_[2]) * ((nestPFa m : ℚ) : ℚ_[2]) := by
    push_cast
    ring
  rw [hcast, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (norm_choose_cast_padic_le_one m r)).trans (norm_nestPFa_le m)

lemma summable_nestAdjointTerm (r : ℕ) :
    Summable (fun m : ℕ => ((nestAdjointTerm r m : ℚ) : ℚ_[2])) := by
  have hgeom : Summable (fun m : ℕ => (1 / 2 : ℝ) ^ m) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact Summable.of_norm_bounded hgeom (norm_nestAdjointTerm_le r)

/-- `S_r=sum_m choose(m,r)a_m`; terms below `r` vanish automatically. -/
noncomputable def nestAdjointS (r : ℕ) : ℚ_[2] :=
  ∑' m : ℕ, ((nestAdjointTerm r m : ℚ) : ℚ_[2])

lemma nestAdjointS_zero : nestAdjointS 0 = -1 := by
  rw [nestAdjointS]
  convert tsum_nestPFa_padic using 1
  apply tsum_congr
  intro m
  simp [nestAdjointTerm]

/-- The finite telescoper used for the recurrence of the `S_r`. -/
noncomputable def nestAdjointG (r m : ℕ) : ℚ :=
  (2 * (m : ℚ) + 1) * (Nat.choose m (r + 1) : ℚ) * nestPFa m

lemma nestAdjointG_step (r m : ℕ) :
    nestAdjointG r (m + 1) - nestAdjointG r m =
      ((2 * (r : ℚ) + 3) * Nat.choose m (r + 1) +
        2 * ((r : ℚ) + 1) * Nat.choose m r) * nestPFa m := by
  by_cases hrm : r ≤ m
  · have hpascal := Nat.choose_succ_succ' m r
    have hshift := Nat.choose_succ_right_eq m r
    have hpascalQ := congrArg (fun z : ℕ => (z : ℚ)) hpascal
    have hshiftQ := congrArg (fun z : ℕ => (z : ℚ)) hshift
    push_cast at hpascalQ hshiftQ
    rw [Nat.cast_sub hrm] at hshiftQ
    have hcancel :
        (2 * (((m + 1 : ℕ) : ℚ)) + 1) *
            (2 * ((m : ℚ) + 1) / (2 * (m : ℚ) + 3)) =
          2 * ((m : ℚ) + 1) := by
      push_cast
      field_simp
      ring
    have hGnext : nestAdjointG r (m + 1) =
        2 * ((m : ℚ) + 1) * (Nat.choose (m + 1) (r + 1) : ℚ) * nestPFa m := by
      rw [nestAdjointG, nestPFa_succ]
      push_cast
      calc
        (2 * ((m : ℚ) + 1) + 1) * (Nat.choose (m + 1) (r + 1) : ℚ) *
              (2 * ((m : ℚ) + 1) / (2 * (m : ℚ) + 3) * nestPFa m) =
            ((2 * (((m + 1 : ℕ) : ℚ)) + 1) *
              (2 * ((m : ℚ) + 1) / (2 * (m : ℚ) + 3))) *
              (Nat.choose (m + 1) (r + 1) : ℚ) * nestPFa m := by
                push_cast
                ring
        _ = _ := by rw [hcancel]
    have hcoef :
        2 * ((m : ℚ) + 1) *
              ((Nat.choose m r : ℚ) + Nat.choose m (r + 1)) -
            (2 * (m : ℚ) + 1) * Nat.choose m (r + 1) =
          (2 * (r : ℚ) + 3) * Nat.choose m (r + 1) +
            2 * ((r : ℚ) + 1) * Nat.choose m r := by
      linear_combination -2 * hshiftQ
    rw [hGnext, nestAdjointG, hpascalQ]
    rw [← sub_mul, hcoef]
  · have hmr : m < r := Nat.lt_of_not_ge hrm
    simp only [nestAdjointG, Nat.choose_eq_zero_of_lt hmr,
      Nat.choose_eq_zero_of_lt (by omega : m < r + 1),
      Nat.choose_eq_zero_of_lt (by omega : m + 1 < r + 1),
      Nat.cast_zero, mul_zero, zero_mul, sub_zero, add_zero]

lemma tendsto_nestAdjointG (r : ℕ) :
    Tendsto (fun m : ℕ => ((nestAdjointG r m : ℚ) : ℚ_[2])) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (g := fun m : ℕ => (1 / 2 : ℝ) ^ m)
    (fun m => norm_nonneg _) (fun m => ?_) ?_
  · rw [nestAdjointG]
    have hcast :
        ((((2 * (m : ℚ) + 1) * (Nat.choose m (r + 1) : ℚ) * nestPFa m : ℚ) : ℚ_[2])) =
          ((2 * (m : ℚ) + 1 : ℚ) : ℚ_[2]) *
            ((Nat.choose m (r + 1) : ℚ) : ℚ_[2]) *
              ((nestPFa m : ℚ) : ℚ_[2]) := by
      push_cast
      ring
    rw [hcast, norm_mul, norm_mul]
    have hodd : Odd (2 * (m : ℤ) + 1) := ⟨m, by ring⟩
    have hnormodd : ‖((2 * (m : ℚ) + 1 : ℚ) : ℚ_[2])‖ = 1 := by
      rw [show ((2 * (m : ℚ) + 1 : ℚ) : ℚ_[2]) =
          ((((2 * (m : ℤ) + 1 : ℤ) : ℚ) : ℚ_[2])) by push_cast; ring,
        norm_ratCast_padic2 (by
          exact_mod_cast (show (2 * (m : ℤ) + 1) ≠ 0 by omega)),
        padicValRat_two_of_odd_int hodd]
      norm_num
    rw [hnormodd, one_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (norm_choose_cast_padic_le_one m (r + 1))).trans (norm_nestPFa_le m)
  · exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

/-- Equation (5.6), obtained by summing `nestAdjointG_step`. -/
theorem nestAdjointS_recurrence (r : ℕ) :
    ((2 * (r : ℚ) + 3 : ℚ) : ℚ_[2]) * nestAdjointS (r + 1) +
      ((2 * ((r : ℚ) + 1) : ℚ) : ℚ_[2]) * nestAdjointS r = 0 := by
  let f : ℕ → ℚ_[2] := fun m =>
    ((2 * (r : ℚ) + 3 : ℚ) : ℚ_[2]) *
        ((nestAdjointTerm (r + 1) m : ℚ) : ℚ_[2]) +
      ((2 * ((r : ℚ) + 1) : ℚ) : ℚ_[2]) *
        ((nestAdjointTerm r m : ℚ) : ℚ_[2])
  have hf : Summable f :=
    ((summable_nestAdjointTerm (r + 1)).mul_left _).add
      ((summable_nestAdjointTerm r).mul_left _)
  have hterm (m : ℕ) : f m =
      ((nestAdjointG r (m + 1) : ℚ) : ℚ_[2]) -
        ((nestAdjointG r m : ℚ) : ℚ_[2]) := by
    have h := congrArg (fun z : ℚ => ((z : ℚ) : ℚ_[2])) (nestAdjointG_step r m)
    dsimp [f, nestAdjointTerm]
    push_cast at h ⊢
    rw [h]
    ring
  have htel (N : ℕ) :
      (∑ m ∈ Finset.range N, f m) =
        ((nestAdjointG r N : ℚ) : ℚ_[2]) -
          ((nestAdjointG r 0 : ℚ) : ℚ_[2]) := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih, hterm]
        ring
  have hG0 : nestAdjointG r 0 = 0 := by
    simp [nestAdjointG]
  have hlimit : Tendsto (fun N : ℕ => ∑ m ∈ Finset.range N, f m)
      atTop (𝓝 0) := by
    simp only [htel, hG0, Rat.cast_zero, sub_zero]
    exact tendsto_nestAdjointG r
  have htsum : (∑' m : ℕ, f m) = 0 :=
    tendsto_nhds_unique hf.hasSum.tendsto_sum_nat hlimit
  have hf1 := (summable_nestAdjointTerm (r + 1)).mul_left
    ((2 * (r : ℚ) + 3 : ℚ) : ℚ_[2])
  have hf2 := (summable_nestAdjointTerm r).mul_left
    ((2 * ((r : ℚ) + 1) : ℚ) : ℚ_[2])
  rw [show (∑' m : ℕ, f m) =
      ((2 * (r : ℚ) + 3 : ℚ) : ℚ_[2]) * nestAdjointS (r + 1) +
        ((2 * ((r : ℚ) + 1) : ℚ) : ℚ_[2]) * nestAdjointS r by
    rw [nestAdjointS, nestAdjointS, hf1.tsum_add hf2,
      tsum_mul_left, tsum_mul_left]] at htsum
  exact htsum

/-- Equation (5.7): the closed form of the adjoint binomial sums. -/
theorem nestAdjointS_eq (r : ℕ) :
    nestAdjointS r = (-1 : ℚ_[2]) ^ (r + 1) * ((nestPFa r : ℚ) : ℚ_[2]) := by
  induction r with
  | zero => simp [nestAdjointS_zero, nestPFa_zero]
  | succ r ih =>
      have hrec := nestAdjointS_recurrence r
      have ha := congrArg (fun z : ℚ => ((z : ℚ) : ℚ_[2])) (nestPFa_succ r)
      push_cast at ha
      rw [ih] at hrec
      have hden : ((2 * (r : ℚ_[2]) + 3)) ≠ 0 := by
        have hq : (2 * (r : ℚ) + 3 : ℚ) ≠ 0 := by positivity
        exact_mod_cast hq
      rw [show r + 1 + 1 = (r + 1) + 1 by omega, pow_succ,
        show (-1 : ℚ_[2]) ^ (r + 1) * -1 * ((nestPFa (r + 1) : ℚ) : ℚ_[2]) =
          -((-1 : ℚ_[2]) ^ (r + 1) * ((nestPFa (r + 1) : ℚ) : ℚ_[2])) by ring,
        ha]
      push_cast at hrec ⊢
      field_simp
      linear_combination hrec

/-! ### The finite binomial transform -/

noncomputable def nestBinomialTerm (m r : ℕ) : ℚ :=
  (-1 : ℚ) ^ r * Nat.choose m r * nestPFa r

noncomputable def nestBinomialH (m r : ℕ) : ℚ :=
  -((2 * (r : ℚ) + 1) / (2 * (m : ℚ) + 1)) * nestBinomialTerm m r

lemma nestBinomialH_step (m r : ℕ) (hr : r ≤ m) :
    nestBinomialH m (r + 1) - nestBinomialH m r = nestBinomialTerm m r := by
  have hchoose := Nat.choose_succ_right_eq m r
  have hchooseQ := congrArg (fun z : ℕ => (z : ℚ)) hchoose
  push_cast at hchooseQ
  rw [Nat.cast_sub hr] at hchooseQ
  have hmden : (2 * (m : ℚ) + 1) ≠ 0 := by positivity
  have hrden : (2 * (r : ℚ) + 3) ≠ 0 := by positivity
  have hHnext : nestBinomialH m (r + 1) =
      ((-1 : ℚ) ^ r *
        (2 * ((r : ℚ) + 1) * Nat.choose m (r + 1) * nestPFa r)) /
          (2 * (m : ℚ) + 1) := by
    rw [nestBinomialH, nestBinomialTerm, nestPFa_succ, pow_succ]
    push_cast
    field_simp [hmden, hrden]
    ring
  have hcoef :
      2 * ((r : ℚ) + 1) * Nat.choose m (r + 1) +
          (2 * (r : ℚ) + 1) * Nat.choose m r =
        (2 * (m : ℚ) + 1) * Nat.choose m r := by
    linear_combination 2 * hchooseQ
  rw [hHnext, nestBinomialH, nestBinomialTerm]
  push_cast
  calc
    (-1 : ℚ) ^ r * (2 * ((r : ℚ) + 1) * Nat.choose m (r + 1) * nestPFa r) /
          (2 * (m : ℚ) + 1) -
        (-((2 * (r : ℚ) + 1) / (2 * (m : ℚ) + 1))) *
          ((-1 : ℚ) ^ r * Nat.choose m r * nestPFa r) =
      ((-1 : ℚ) ^ r * nestPFa r / (2 * (m : ℚ) + 1)) *
        (2 * ((r : ℚ) + 1) * Nat.choose m (r + 1) +
          (2 * (r : ℚ) + 1) * Nat.choose m r) := by ring
    _ = ((-1 : ℚ) ^ r * nestPFa r / (2 * (m : ℚ) + 1)) *
        ((2 * (m : ℚ) + 1) * Nat.choose m r) := by rw [hcoef]
    _ = (-1 : ℚ) ^ r * Nat.choose m r * nestPFa r := by
      field_simp [hmden]

lemma nestBinomialH_zero (m : ℕ) :
    nestBinomialH m 0 = -(1 / (2 * (m : ℚ) + 1)) := by
  simp [nestBinomialH, nestBinomialTerm, nestPFa_zero]

lemma nestBinomialH_top (m : ℕ) : nestBinomialH m (m + 1) = 0 := by
  simp [nestBinomialH, nestBinomialTerm]

/-- Equation (5.8), the finite binomial transform of `a`. -/
theorem sum_nestBinomialTerm (m : ℕ) :
    (∑ r ∈ Finset.range (m + 1), nestBinomialTerm m r) =
      1 / (2 * (m : ℚ) + 1) := by
  have htel (N : ℕ) (hN : N ≤ m + 1) :
      (∑ r ∈ Finset.range N, nestBinomialTerm m r) =
        nestBinomialH m N - nestBinomialH m 0 := by
    induction N with
    | zero => simp
    | succ N ih =>
        rw [Finset.sum_range_succ, ih (by omega),
          ← nestBinomialH_step m N (by omega)]
        ring
  rw [htel (m + 1) le_rfl, nestBinomialH_top, nestBinomialH_zero]
  ring

/-! ### The absolutely summable triangular double family -/

noncomputable def nestDoubleTerm (r m : ℕ) : ℚ_[2] :=
  if r ≤ m then
    (-1 : ℚ_[2]) ^ r * ((nestPFa r : ℚ) : ℚ_[2]) *
      ((Nat.choose m r : ℚ) : ℚ_[2]) * ((nestPFa m : ℚ) : ℚ_[2])
  else 0

lemma norm_nestDoubleTerm_le (r m : ℕ) :
    ‖nestDoubleTerm r m‖ ≤ (1 / 2 : ℝ) ^ r * (1 / 2 : ℝ) ^ m := by
  by_cases hrm : r ≤ m
  · rw [nestDoubleTerm, if_pos hrm, norm_mul, norm_mul, norm_mul]
    simp only [norm_pow, norm_neg, norm_one, one_pow, one_mul]
    have hleft :
        ‖((nestPFa r : ℚ) : ℚ_[2])‖ * ‖((Nat.choose m r : ℚ) : ℚ_[2])‖ ≤
          (1 / 2 : ℝ) ^ r := by
      exact (mul_le_of_le_one_right (norm_nonneg _)
        (norm_choose_cast_padic_le_one m r)).trans (norm_nestPFa_le r)
    exact mul_le_mul hleft (norm_nestPFa_le m) (norm_nonneg _) (by positivity)
  · rw [nestDoubleTerm, if_neg hrm, norm_zero]
    positivity

lemma summable_nestDoubleTerm :
    Summable (fun p : ℕ × ℕ => nestDoubleTerm p.1 p.2) := by
  have hg : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hprod : Summable (fun p : ℕ × ℕ =>
      (1 / 2 : ℝ) ^ p.1 * (1 / 2 : ℝ) ^ p.2) :=
    hg.mul_of_nonneg hg (fun _ => by positivity) (fun _ => by positivity)
  exact Summable.of_norm_bounded hprod fun p => norm_nestDoubleTerm_le p.1 p.2

lemma tsum_nestDoubleTerm_left (m : ℕ) :
    (∑' r : ℕ, nestDoubleTerm r m) =
      (((nestPFa m / (2 * (m : ℚ) + 1) : ℚ)) : ℚ_[2]) := by
  rw [tsum_eq_sum (s := Finset.range (m + 1)) (fun r hr => by
    rw [Finset.mem_range, not_lt] at hr
    simp [nestDoubleTerm, show ¬r ≤ m by omega])]
  have hfinite :
      (∑ r ∈ Finset.range (m + 1), nestDoubleTerm r m) =
        (((∑ r ∈ Finset.range (m + 1), nestBinomialTerm m r) * nestPFa m : ℚ) : ℚ_[2]) := by
    push_cast
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro r hr
    have hrm : r ≤ m := by simpa using Finset.mem_range.mp hr
    rw [nestDoubleTerm, if_pos hrm, nestBinomialTerm]
    push_cast
    ring
  rw [hfinite, sum_nestBinomialTerm]
  push_cast
  ring

lemma tsum_nestDoubleTerm_right (r : ℕ) :
    (∑' m : ℕ, nestDoubleTerm r m) =
      -(((nestPFa r : ℚ) : ℚ_[2]) ^ 2) := by
  have heq (m : ℕ) : nestDoubleTerm r m =
      (-1 : ℚ_[2]) ^ r * ((nestPFa r : ℚ) : ℚ_[2]) *
        ((nestAdjointTerm r m : ℚ) : ℚ_[2]) := by
    by_cases hrm : r ≤ m
    · rw [nestDoubleTerm, if_pos hrm, nestAdjointTerm]
      push_cast
      ring
    · have hchoose : Nat.choose m r = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [nestDoubleTerm, if_neg hrm, nestAdjointTerm, hchoose]
      simp
  rw [show (∑' m : ℕ, nestDoubleTerm r m) =
      (-1 : ℚ_[2]) ^ r * ((nestPFa r : ℚ) : ℚ_[2]) * nestAdjointS r by
    rw [nestAdjointS, ← tsum_mul_left]
    apply tsum_congr
    exact heq]
  rw [nestAdjointS_eq]
  have hsign : (-1 : ℚ_[2]) ^ r * (-1 : ℚ_[2]) ^ (r + 1) = -1 := by
    rw [← pow_add, show r + (r + 1) = 2 * r + 1 by omega, pow_add, pow_mul]
    norm_num
  calc
    _ =
        ((-1 : ℚ_[2]) ^ r * (-1 : ℚ_[2]) ^ (r + 1)) *
          ((nestPFa r : ℚ) : ℚ_[2]) ^ 2 := by ring
    _ = -(((nestPFa r : ℚ) : ℚ_[2]) ^ 2) := by rw [hsign]; ring

lemma summable_nestPFa_square :
    Summable (fun r : ℕ => ((nestPFa r : ℚ) : ℚ_[2]) ^ 2) := by
  have hg : Summable (fun r : ℕ => (1 / 4 : ℝ) ^ r) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine Summable.of_norm_bounded hg fun r => ?_
  rw [norm_pow]
  calc
    ‖((nestPFa r : ℚ) : ℚ_[2])‖ ^ 2 ≤ ((1 / 2 : ℝ) ^ r) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_nestPFa_le r) 2
    _ = (1 / 4 : ℝ) ^ r := by
      rw [← pow_mul, show r * 2 = 2 * r by omega, pow_mul]
      norm_num

set_option maxHeartbeats 3000000 in
/-- Equation (5.9): the Nielsen series is `-2 sum a_m^2`. -/
theorem nestF2Padic_eq_neg_two_tsum_square :
    nestF2Padic = -2 *
      (∑' r : ℕ, ((nestPFa r : ℚ) : ℚ_[2]) ^ 2) := by
  have hdouble : Summable (Function.uncurry nestDoubleTerm) := by
    change Summable (fun p : ℕ × ℕ => nestDoubleTerm p.1 p.2)
    exact summable_nestDoubleTerm
  have hcomm := hdouble.tsum_comm
  have hleft :
      (∑' m : ℕ, ∑' r : ℕ, nestDoubleTerm r m) = nestF2Padic / 2 := by
    rw [nestF2Padic]
    have hb : Summable (fun m : ℕ => ((nestF2Term m : ℚ) : ℚ_[2])) :=
      summable_nestF2Term
    rw [show (∑' m : ℕ, ∑' r : ℕ, nestDoubleTerm r m) =
        ∑' m : ℕ, ((nestF2Term m : ℚ) : ℚ_[2]) / 2 by
      apply tsum_congr
      intro m
      rw [tsum_nestDoubleTerm_left, nestF2Term, nestPFa]
      push_cast
      field_simp,
      tsum_div_const, div_eq_mul_inv]
  have hright :
      (∑' r : ℕ, ∑' m : ℕ, nestDoubleTerm r m) =
        -(∑' r : ℕ, ((nestPFa r : ℚ) : ℚ_[2]) ^ 2) := by
    rw [show (∑' r : ℕ, ∑' m : ℕ, nestDoubleTerm r m) =
        ∑' r : ℕ, -(((nestPFa r : ℚ) : ℚ_[2]) ^ 2) by
      apply tsum_congr
      exact tsum_nestDoubleTerm_right]
    rw [tsum_neg]
  rw [hleft, hright] at hcomm
  linear_combination 2 * hcomm

/-! ### Identification with Beukers' canonical Catalan period -/

lemma brkDen_one_half (r : ℕ) :
    brkDen (1 / 2) r = (1 / 2 : ℚ) * nestPochhammerThreeHalves r := by
  rw [brkDen, Finset.prod_range_succ', nestPochhammerThreeHalves]
  have hprod :
      (∏ j ∈ Finset.range r, ((1 / 2 : ℚ) + ((j + 1 : ℕ) : ℚ))) =
        ∏ j ∈ Finset.range r, ((3 / 2 : ℚ) + (j : ℚ)) := by
    apply Finset.prod_congr rfl
    intro j _
    push_cast
    ring
  rw [hprod]
  norm_num
  ring

lemma brk_one_half (r : ℕ) : brk (1 / 2) r = 2 * nestPFa r := by
  rw [brk, brkDen_one_half, nestPFa]
  field_simp

lemma xiTerm_one_half (r : ℕ) :
    xiTerm (1 / 2) r = 4 * nestPFa r ^ 2 := by
  rw [xiTerm, show (1 : ℚ) - 1 / 2 = 1 / 2 by norm_num,
    brk_one_half]
  ring

theorem xiCat_eq_neg_four_tsum_square :
    xiCat = -4 * (∑' r : ℕ, ((nestPFa r : ℚ) : ℚ_[2]) ^ 2) := by
  rw [xiCat, XiPade]
  have hs := summable_nestPFa_square.mul_left (4 : ℚ_[2])
  rw [show (∑' r : ℕ, ((xiTerm (1 / 2) r : ℚ) : ℚ_[2])) =
      4 * (∑' r : ℕ, ((nestPFa r : ℚ) : ℚ_[2]) ^ 2) by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro r
    rw [xiTerm_one_half]
    push_cast
    ring]
  ring

/-- Equations (5.10)--(5.11): the Nielsen series is half of `Xi(1/2)` and
four times the project's canonical `2`-adic Catalan period. -/
theorem nestF2Padic_eq_xiCat_div_two : nestF2Padic = xiCat / 2 := by
  rw [nestF2Padic_eq_neg_two_tsum_square, xiCat_eq_neg_four_tsum_square]
  ring

theorem nestF2Padic_div_four_eq_GZ2 : nestF2Padic / 4 = GZ2 := by
  rw [nestF2Padic_eq_xiCat_div_two, GZ2_eq_xi_div_eight]
  ring

theorem nestF2Padic_eq_four_mul_GZ2 : nestF2Padic = 4 * GZ2 := by
  linear_combination 4 * nestF2Padic_div_four_eq_GZ2

end Catalan
