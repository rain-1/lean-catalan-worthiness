import RequestProject.Assembly
import RequestProject.Rows58
import RequestProject.Constant58

/-!
# The improved `0.9025…` worthiness theorem

This file assembles the `5 : 8` construction:

* the Zudilin row sampled at index `5n` and the modular `E`-row at index `8n`, over the common
  lcm square `S_n = D_{10n}²` (`Rows58.lean`);
* the dyadic divisor `T_n = 2^{40n - 3 - 2⌊log₂(5n)⌋}` of the reduced cross determinant, which
  comes from the off-diagonal `2`-adic cross bound of `Plucker58.lean`;
* the abstract geometry-of-numbers selection `lattice_selection` of `GeometrySelection.lean`,
  applied at the rates

  `A₁ = 20 + 24 log 2`, `E₁ = 20 + 16 log 2`,
  `A₂ = 20 + 20 log 2 + 25 log φ`, `E₂ = 20 + 20 log 2 - 25 log φ`,
  `σ = 20 + 40 log 2`,

  which give `H = 10 - 2 log 2 + (75/2) log φ` and `F = 10 - 2 log 2 - (25/2) log φ`.

The resulting worthiness is `1 - F/H = 50 log φ / H = 0.9025266…`, an improvement on the
`0.857914` of the `3 : 6` construction of `Assembly.lean`.  As there, the only hypothesis is the
archimedean input bundle `BaseNoteInputs`, and for Catalan's constant that reduces to the prime
number theorem `rate_D`.
-/

namespace Catalan

open Filter Topology

/-! ### The rates of the `5 : 8` construction -/

/-- `A₁ = 20 + 24 log 2`, the rate of `X₁ n = D_{10n}² A_{8n}`. -/
noncomputable def A1rate58 : ℝ := 20 + 24 * Real.log 2

/-- `E₁ = 20 + 16 log 2`, the rate of the modular linear form. -/
noncomputable def E1rate58 : ℝ := 20 + 16 * Real.log 2

/-- `A₂ = 20 + 20 log 2 + 25 log φ`, the rate of `X₂ n = 2^{e_{5n}} D_{10n}² Q_{5n}`. -/
noncomputable def A2rate58 : ℝ := 20 + 20 * Real.log 2 + 25 * Real.log Real.goldenRatio

/-- `E₂ = 20 + 20 log 2 - 25 log φ`, the rate of the Zudilin linear form. -/
noncomputable def E2rate58 : ℝ := 20 + 20 * Real.log 2 - 25 * Real.log Real.goldenRatio

/-- `σ = 20 + 40 log 2`, the rate of the division modulus `M_n = S_n T_n`. -/
noncomputable def sigmaRate58 : ℝ := 20 + 40 * Real.log 2

/-- The balancing parameter `x = (σ + E₂ - E₁)/2`. -/
noncomputable def xBal58 : ℝ := (sigmaRate58 + E2rate58 - E1rate58) / 2

/-- The denominator rate `H = A₂ - x`. -/
noncomputable def Hrate58 : ℝ := A2rate58 - xBal58

/-- The linear-form rate `F = x + E₁ - σ`. -/
noncomputable def Frate58 : ℝ := xBal58 + E1rate58 - sigmaRate58

lemma xBal58_eq : xBal58 = 10 + 22 * Real.log 2 - 25 / 2 * Real.log Real.goldenRatio := by
  unfold xBal58 sigmaRate58 E2rate58 E1rate58; ring

theorem Hrate58_eq :
    Hrate58 = 10 - 2 * Real.log 2 + 75 / 2 * Real.log Real.goldenRatio := by
  unfold Hrate58 A2rate58; rw [xBal58_eq]; ring

theorem Frate58_eq :
    Frate58 = 10 - 2 * Real.log 2 - 25 / 2 * Real.log Real.goldenRatio := by
  unfold Frate58 E1rate58 sigmaRate58; rw [xBal58_eq]; ring

theorem Hrate58_pos : 0 < Hrate58 := by
  rw [Hrate58_eq]
  exact worthinessConstant58_den_pos

theorem Frate58_pos : 0 < Frate58 := by
  rw [Frate58_eq]
  have hup := log_golden_lt_sharp
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  linarith

/-- `H - F = 50 log φ`. -/
theorem Hrate58_sub_Frate58 : Hrate58 - Frate58 = 50 * Real.log Real.goldenRatio := by
  rw [Hrate58_eq, Frate58_eq]; ring

/-- `1 - F/H` is exactly the improved worthiness constant. -/
theorem one_sub_ratio58_eq : 1 - Frate58 / Hrate58 = worthinessConstant58 := by
  have hH : Hrate58 ≠ 0 := ne_of_gt Hrate58_pos
  rw [worthinessConstant58, ← Hrate58_eq]
  field_simp
  linarith [Hrate58_sub_Frate58]

/-- The crossed gap `A₁ + E₂ < A₂ + E₁`, equivalent to `8 log 2 < 50 log φ`. -/
theorem crossed_gap58 : A1rate58 + E2rate58 < A2rate58 + E1rate58 := by
  have h1 : (0.4812117 : ℝ) < Real.log Real.goldenRatio := log_golden_gt
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [A1rate58, E2rate58, A2rate58, E1rate58]
  linarith

/-! ### Auxiliary rate computations -/

/-- The rate of a dyadic power `2^{k n}` with `k n / n → c`. -/
lemma logRate_two_pow {k : ℕ → ℕ} {c : ℝ}
    (h : Tendsto (fun n : ℕ => (k n : ℝ) / n) atTop (𝓝 c)) :
    LogRate (fun n => (2 : ℝ) ^ (k n)) (c * Real.log 2) := by
  have h2 := h.mul_const (Real.log 2)
  refine h2.congr' ?_
  filter_upwards with n
  rw [abs_of_pos (by positivity), Real.log_pow]
  ring

/-- `e_{5n} = 20n + o(n)`. -/
theorem tendsto_eZud_five_mul :
    Tendsto (fun n : ℕ => (eZud (5 * n) : ℝ) / n) atTop (𝓝 20) := by
  have hlow : Tendsto (fun n : ℕ => 20 + 3 / (n : ℝ)) atTop (𝓝 20) := by
    simpa using (tendsto_const_nhds (x := (20 : ℝ)) (f := atTop (α := ℕ))).add
      (tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ))
  have hupp : Tendsto
      (fun n : ℕ => 20 + 3 / (n : ℝ) + (Nat.log 2 (10 * n - 1) : ℝ) / n) atTop (𝓝 20) := by
    simpa using hlow.add (tendsto_natLog_div 10 (by norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hle : 20 * n + 3 ≤ eZud (5 * n) := by
      have := eZud_five_mul_ge n (by omega)
      omega
    have hleR : (20 : ℝ) * n + 3 ≤ (eZud (5 * n) : ℝ) := by exact_mod_cast hle
    rw [le_div_iff₀ hnR]
    have hexp : (20 + 3 / (n : ℝ)) * n = 20 * n + 3 := by field_simp
    rw [hexp]
    exact hleR
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hle : eZud (5 * n) ≤ 20 * n + 3 + Nat.log 2 (10 * n - 1) := by
      have h : eZud (5 * n) ≤ 4 * (5 * n) + 3 + Nat.log 2 (2 * (5 * n) - 1) := min_le_right _ _
      have h10 : 2 * (5 * n) = 10 * n := by ring
      rw [h10] at h
      omega
    have hleR : (eZud (5 * n) : ℝ) ≤ 20 * n + 3 + (Nat.log 2 (10 * n - 1) : ℝ) := by
      exact_mod_cast hle
    rw [div_le_iff₀ hnR]
    have hexp : (20 + 3 / (n : ℝ) + (Nat.log 2 (10 * n - 1) : ℝ) / n) * n
        = 20 * n + 3 + (Nat.log 2 (10 * n - 1) : ℝ) := by field_simp
    rw [hexp]
    exact hleR

/-- `T_n`'s exponent satisfies `(40n - 3 - 2⌊log₂(5n)⌋)/n → 40`. -/
theorem tendsto_Texp58 : Tendsto (fun n : ℕ => (Texp58 n : ℝ) / n) atTop (𝓝 40) := by
  have hupp : Tendsto (fun _ : ℕ => (40 : ℝ)) atTop (𝓝 40) := tendsto_const_nhds
  have hlow : Tendsto
      (fun n : ℕ => 40 - 3 / (n : ℝ) - 2 * ((Nat.log 2 (10 * n - 1) : ℝ) / n)) atTop (𝓝 40) := by
    have h1 : Tendsto (fun n : ℕ => (3 : ℝ) / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ)
    have h2 := (tendsto_natLog_div 10 (by norm_num)).const_mul (2 : ℝ)
    simpa using ((tendsto_const_nhds (x := (40 : ℝ)) (f := atTop (α := ℕ))).sub h1).sub h2
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hmono : Nat.log 2 (5 * n) ≤ Nat.log 2 (10 * n - 1) :=
      Nat.log_mono_right (by omega)
    have hT := Texp58_le n (by omega)
    have hTR : (40 : ℝ) * n - 3 - 2 * (Nat.log 2 (10 * n - 1) : ℝ) ≤ (Texp58 n : ℝ) := by
      have h1 : ((Texp58 n : ℤ) : ℝ) = 40 * (n : ℝ) - 3 - 2 * (Nat.log 2 (5 * n) : ℝ) := by
        exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hT
      have h2 : ((Nat.log 2 (5 * n) : ℝ)) ≤ (Nat.log 2 (10 * n - 1) : ℝ) := by
        exact_mod_cast hmono
      push_cast at h1
      linarith
    rw [le_div_iff₀ hnR]
    have hexp : (40 - 3 / (n : ℝ) - 2 * ((Nat.log 2 (10 * n - 1) : ℝ) / n)) * n
        = 40 * n - 3 - 2 * (Nat.log 2 (10 * n - 1) : ℝ) := by field_simp
    rw [hexp]
    exact hTR
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hle : Texp58 n ≤ 40 * n := by unfold Texp58; omega
    have hleR : (Texp58 n : ℝ) ≤ 40 * n := by exact_mod_cast hle
    rw [div_le_iff₀ hnR]
    linarith

lemma Sfac58_ne_zero (n : ℕ) : ((Sfac58 n : ℕ) : ℝ) ≠ 0 := by
  have := Sfac58_pos n
  positivity

lemma rate_pow_two_eZud5 :
    LogRate (fun n : ℕ => (2 : ℝ) ^ (eZud (5 * n))) (20 * Real.log 2) :=
  logRate_two_pow tendsto_eZud_five_mul

lemma rate_pow_two_Texp58 :
    LogRate (fun n : ℕ => (2 : ℝ) ^ (Texp58 n)) (40 * Real.log 2) :=
  logRate_two_pow tendsto_Texp58

lemma rate_Ae_eight : LogRate (fun n => ((Ae (8 * n) : ℚ) : ℝ)) (8 * Real.log 8) :=
  LogRate.comp_mul 8 (by norm_num) Catalan.rate_Ae

lemma rate_Qz_five :
    LogRate (fun n => ((Qz (5 * n) : ℚ) : ℝ)) (5 * (5 * Real.log Real.goldenRatio)) :=
  LogRate.comp_mul 5 (by norm_num) Catalan.rate_Qz

lemma Ae_eight_ne_zero : ∀ᶠ n in atTop, ((Ae (8 * n) : ℚ) : ℝ) ≠ 0 := by
  filter_upwards with n
  exact_mod_cast Rat.cast_ne_zero.mpr (Ae_ne_zero (8 * n))

lemma Be_eight_ne_zero : ∀ᶠ n in atTop, ((Be (8 * n) : ℚ) : ℝ) ≠ 0 := by
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have h8 : 8 * n = (8 * n - 1) + 1 := by omega
  rw [h8]
  exact_mod_cast Rat.cast_ne_zero.mpr (Be_ne_zero_and_val (8 * n - 1)).1

lemma Qz_five_ne_zero : ∀ᶠ n in atTop, ((Qz (5 * n) : ℚ) : ℝ) ≠ 0 := by
  filter_upwards with n
  exact_mod_cast Rat.cast_ne_zero.mpr (Qz_ne_zero (5 * n))

lemma Pz_five_ne_zero : ∀ᶠ n in atTop, ((Pz (5 * n) : ℚ) : ℝ) ≠ 0 := by
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  exact_mod_cast Rat.cast_ne_zero.mpr (Pz_ne_zero (5 * n) (by omega))

namespace BaseNoteInputs

variable {α : ℝ} (i : BaseNoteInputs α)

include i in
lemma rate_Sfac58 : LogRate (fun n => ((Sfac58 n : ℕ) : ℝ)) 20 := by
  have hD : LogRate (fun n => ((Dlcm (10 * n) : ℕ) : ℝ)) (10 * 1) :=
    LogRate.comp_mul 10 (by norm_num) i.rate_D
  have hne : ∀ᶠ n in atTop, ((Dlcm (10 * n) : ℕ) : ℝ) ≠ 0 := by
    filter_upwards with n
    have := Dlcm_pos (10 * n)
    positivity
  have hmul := hD.mul hD hne hne
  have h20 : (10 : ℝ) * 1 + 10 * 1 = 20 := by norm_num
  rw [h20] at hmul
  refine hmul.of_eq (fun n => ?_)
  unfold Sfac58
  push_cast
  ring

include i in
lemma rate_Be_eight : LogRate (fun n => ((Be (8 * n) : ℚ) : ℝ)) (8 * Real.log 8) :=
  LogRate.comp_mul 8 (by norm_num) i.rate_Be

include i in
lemma rate_Pz_five :
    LogRate (fun n => ((Pz (5 * n) : ℚ) : ℝ)) (5 * (5 * Real.log Real.goldenRatio)) :=
  LogRate.comp_mul 5 (by norm_num) i.rate_Pz

include i in
lemma rate_lE_eight :
    LogRate (fun n => α / 2 * ((Ae (8 * n) : ℚ) : ℝ) - ((Be (8 * n) : ℚ) : ℝ))
      (8 * Real.log 4) :=
  LogRate.comp_mul (f := fun N => α / 2 * ((Ae N : ℚ) : ℝ) - ((Be N : ℚ) : ℝ))
    8 (by norm_num) i.rate_lE

include i in
lemma rate_lZ_five :
    LogRate (fun n => ((Qz (5 * n) : ℚ) : ℝ) * α - ((Pz (5 * n) : ℚ) : ℝ))
      (5 * -(5 * Real.log Real.goldenRatio)) :=
  LogRate.comp_mul (f := fun N => ((Qz N : ℚ) : ℝ) * α - ((Pz N : ℚ) : ℝ))
    5 (by norm_num) i.rate_lZ

include i in
lemma lE_eight_ne_zero :
    ∀ᶠ n in atTop, α / 2 * ((Ae (8 * n) : ℚ) : ℝ) - ((Be (8 * n) : ℚ) : ℝ) ≠ 0 := by
  refine eventually_comp_mul (P := fun N => α / 2 * ((Ae N : ℚ) : ℝ) - ((Be N : ℚ) : ℝ) ≠ 0)
    8 (by norm_num) ?_
  refine LogRate.eventually_ne_zero ?_ i.rate_lE
  have : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  linarith

include i in
lemma lZ_five_ne_zero :
    ∀ᶠ n in atTop, ((Qz (5 * n) : ℚ) : ℝ) * α - ((Pz (5 * n) : ℚ) : ℝ) ≠ 0 := by
  refine eventually_comp_mul (P := fun N => ((Qz N : ℚ) : ℝ) * α - ((Pz N : ℚ) : ℝ) ≠ 0)
    5 (by norm_num) ?_
  refine LogRate.eventually_ne_zero ?_ i.rate_lZ
  have hpos := log_golden_pos
  intro hc
  linarith

/-! ### The rates of the four rows and of the modulus -/

include i in
theorem rate_X1_58 :
    LogRate (fun n : ℕ => (((Sfac58 n : ℤ) * a1row58 n : ℤ) : ℝ)) A1rate58 := by
  have h := (i.rate_Sfac58).mul rate_Ae_eight
    (Eventually.of_forall (fun n => Sfac58_ne_zero n)) Ae_eight_ne_zero
  have hval : (20 : ℝ) + 8 * Real.log 8 = A1rate58 := by
    rw [A1rate58, log_eight_eq]; ring
  rw [hval] at h
  refine h.of_eq (fun n => ?_)
  have := a1row58_cast n
  push_cast [← this]
  ring

include i in
theorem rate_Y1_58 : LogRate (fun n : ℕ => ((y1row58 n : ℤ) : ℝ)) A1rate58 := by
  have h := ((LogRate.const (2 : ℝ)).mul i.rate_Sfac58 (Eventually.of_forall (by norm_num))
    (Eventually.of_forall (fun n => Sfac58_ne_zero n))).mul (i.rate_Be_eight)
      (by filter_upwards with n; exact mul_ne_zero (by norm_num) (Sfac58_ne_zero n))
      Be_eight_ne_zero
  have hval : ((0 : ℝ) + 20) + 8 * Real.log 8 = A1rate58 := by
    rw [A1rate58, log_eight_eq]; ring
  rw [hval] at h
  refine h.of_eq (fun n => ?_)
  have hY := congrArg (fun z : ℚ => (z : ℝ)) (y1row58_cast n)
  push_cast at hY ⊢
  rw [hY]

include i in
theorem rate_l1_58 :
    LogRate (fun n : ℕ => (((Sfac58 n : ℤ) * a1row58 n : ℤ) : ℝ) * α - ((y1row58 n : ℤ) : ℝ))
      E1rate58 := by
  have h := ((LogRate.const (2 : ℝ)).mul i.rate_Sfac58 (Eventually.of_forall (by norm_num))
    (Eventually.of_forall (fun n => Sfac58_ne_zero n))).mul i.rate_lE_eight
      (by filter_upwards with n; exact mul_ne_zero (by norm_num) (Sfac58_ne_zero n))
      i.lE_eight_ne_zero
  have hval : ((0 : ℝ) + 20) + 8 * Real.log 4 = E1rate58 := by
    rw [E1rate58, log_four_eq]; ring
  rw [hval] at h
  refine h.of_eq (fun n => ?_)
  have hA := congrArg (fun z : ℚ => (z : ℝ)) (a1row58_cast n)
  have hY := congrArg (fun z : ℚ => (z : ℝ)) (y1row58_cast n)
  push_cast at hA hY ⊢
  rw [hA, hY]
  ring

include i in
theorem rate_X2_58 :
    LogRate (fun n : ℕ => (((Sfac58 n : ℤ) * a2row58 n : ℤ) : ℝ)) A2rate58 := by
  have h := (rate_pow_two_eZud5.mul i.rate_Sfac58
    (Eventually.of_forall (fun n => by positivity))
    (Eventually.of_forall (fun n => Sfac58_ne_zero n))).mul rate_Qz_five
      (by filter_upwards with n; exact mul_ne_zero (by positivity) (Sfac58_ne_zero n))
      Qz_five_ne_zero
  have hval : (20 * Real.log 2 + 20) + 5 * (5 * Real.log Real.goldenRatio) = A2rate58 := by
    rw [A2rate58]; ring
  rw [hval] at h
  refine h.of_eq (fun n => ?_)
  have hA := congrArg (fun z : ℚ => (z : ℝ)) (a2row58_cast n)
  push_cast at hA ⊢
  rw [hA]
  ring

include i in
theorem rate_Y2_58 : LogRate (fun n : ℕ => ((y2row58 n : ℤ) : ℝ)) A2rate58 := by
  have h := (rate_pow_two_eZud5.mul i.rate_Sfac58
    (Eventually.of_forall (fun n => by positivity))
    (Eventually.of_forall (fun n => Sfac58_ne_zero n))).mul i.rate_Pz_five
      (by filter_upwards with n; exact mul_ne_zero (by positivity) (Sfac58_ne_zero n))
      Pz_five_ne_zero
  have hval : (20 * Real.log 2 + 20) + 5 * (5 * Real.log Real.goldenRatio) = A2rate58 := by
    rw [A2rate58]; ring
  rw [hval] at h
  refine h.of_eq (fun n => ?_)
  have hY := congrArg (fun z : ℚ => (z : ℝ)) (y2row58_cast n)
  push_cast at hY ⊢
  rw [hY]

include i in
theorem rate_l2_58 :
    LogRate (fun n : ℕ => (((Sfac58 n : ℤ) * a2row58 n : ℤ) : ℝ) * α - ((y2row58 n : ℤ) : ℝ))
      E2rate58 := by
  have h := (rate_pow_two_eZud5.mul i.rate_Sfac58
    (Eventually.of_forall (fun n => by positivity))
    (Eventually.of_forall (fun n => Sfac58_ne_zero n))).mul i.rate_lZ_five
      (by filter_upwards with n; exact mul_ne_zero (by positivity) (Sfac58_ne_zero n))
      i.lZ_five_ne_zero
  have hval : (20 * Real.log 2 + 20) + 5 * -(5 * Real.log Real.goldenRatio) = E2rate58 := by
    rw [E2rate58]; ring
  rw [hval] at h
  refine h.of_eq (fun n => ?_)
  have hA := congrArg (fun z : ℚ => (z : ℝ)) (a2row58_cast n)
  have hY := congrArg (fun z : ℚ => (z : ℝ)) (y2row58_cast n)
  push_cast at hA hY ⊢
  rw [hA, hY]
  ring

include i in
theorem rate_M_58 :
    LogRate (fun n : ℕ => (((Sfac58 n : ℤ) * (2 : ℤ) ^ (Texp58 n) : ℤ) : ℝ)) sigmaRate58 := by
  have h := (i.rate_Sfac58).mul rate_pow_two_Texp58
    (Eventually.of_forall (fun n => Sfac58_ne_zero n))
    (Eventually.of_forall (fun n => by positivity))
  have hval : (20 : ℝ) + 40 * Real.log 2 = sigmaRate58 := by rw [sigmaRate58]
  rw [hval] at h
  refine h.of_eq (fun n => ?_)
  push_cast
  ring

end BaseNoteInputs

/-! ### The improved theorem -/

/-- **The `5 : 8` worthiness theorem.**  Relative to the archimedean input bundle
`BaseNoteInputs`, there is an admissible approximation sequence to `α` of worthiness at least

`50 log φ / (10 - 2 log 2 + (75/2) log φ) = 0.9025266…`. -/
theorem catalan_worthiness58 {α : ℝ} (i : BaseNoteInputs α) :
    ∃ q p : ℕ → ℤ, IsAdmissible α q p ∧
      ((worthinessConstant58 : ℝ) : EReal) ≤ worthiness α q p := by
  have hA2 : A2rate58 ≠ 0 := by
    have h1 := log_golden_pos
    have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [A2rate58]
    linarith
  have hE1 : E1rate58 ≠ 0 := by
    have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [E1rate58]
    linarith
  have hX2ne : ∀ᶠ n in atTop, (((Sfac58 n : ℤ) * a2row58 n : ℤ) : ℝ) ≠ 0 :=
    LogRate.eventually_ne_zero hA2 i.rate_X2_58
  have hl1ne : ∀ᶠ n in atTop,
      (((Sfac58 n : ℤ) * a1row58 n : ℤ) : ℝ) * α - ((y1row58 n : ℤ) : ℝ) ≠ 0 :=
    LogRate.eventually_ne_zero hE1 i.rate_l1_58
  obtain ⟨d⟩ := lattice_selection α A1rate58 E1rate58 A2rate58 E2rate58 sigmaRate58
    a1row58 a2row58 y1row58 y2row58
    (fun n => (Sfac58 n : ℤ)) (fun n => (2 : ℤ) ^ (Texp58 n))
    (fun n => show (0:ℤ) < (Sfac58 n : ℤ) from Int.natCast_pos.mpr (Sfac58_pos n))
    (fun n => by positivity)
    i.rate_X1_58 i.rate_l1_58 i.rate_X2_58 i.rate_l2_58 i.rate_M_58
    dvd_reduced_cross58 crossed_gap58 hX2ne hl1ne
  have hH : A2rate58 - (sigmaRate58 + E2rate58 - E1rate58) / 2 = Hrate58 := by
    rw [Hrate58, xBal58]
  have hF : (sigmaRate58 + E2rate58 - E1rate58) / 2 + E1rate58 - sigmaRate58 = Frate58 := by
    rw [Frate58, xBal58]
  rw [hH, hF] at d
  obtain ⟨q, p, hadm, hge⟩ := worthiness_ge_of_balancedMinimaData Hrate58_pos Frate58_pos d
  exact ⟨q, p, hadm, by rwa [one_sub_ratio58_eq] at hge⟩

/-- The numerical form of the improved theorem: worthiness at least `0.9`. -/
theorem catalan_worthiness58_gt {α : ℝ} (i : BaseNoteInputs α) :
    ∃ q p : ℕ → ℤ, IsAdmissible α q p ∧ ((0.9 : ℝ) : EReal) ≤ worthiness α q p := by
  obtain ⟨q, p, hadm, hge⟩ := catalan_worthiness58 i
  refine ⟨q, p, hadm, le_trans ?_ hge⟩
  exact_mod_cast EReal.coe_le_coe_iff.mpr worthinessConstant58_gt_nine_tenths.le

/-- **The improved theorem for Catalan's constant itself.**  Both `2`-adic and archimedean
identifications of the two rows with `G` are proved in the project, so the prime number theorem
`rate_D` is the only hypothesis. -/
theorem catalan_worthiness58_catalan_exact
    (rate_D : LogRate (fun N => ((Dlcm N : ℕ) : ℝ)) 1) :
    ∃ q p : ℕ → ℤ, IsAdmissible catalanReal q p ∧
      ((worthinessConstant58 : ℝ) : EReal) ≤ worthiness catalanReal q p :=
  catalan_worthiness58
    ⟨GEreal_eq_catalanReal.symm, GZreal_eq_catalanReal.symm, rate_D⟩

/-- The numerical form for Catalan's constant: worthiness at least `0.9`. -/
theorem catalan_worthiness58_catalan
    (rate_D : LogRate (fun N => ((Dlcm N : ℕ) : ℝ)) 1) :
    ∃ q p : ℕ → ℤ, IsAdmissible catalanReal q p ∧
      ((0.9 : ℝ) : EReal) ≤ worthiness catalanReal q p :=
  catalan_worthiness58_gt
    ⟨GEreal_eq_catalanReal.symm, GZreal_eq_catalanReal.symm, rate_D⟩

/-- The sharper numerical form for Catalan's constant: worthiness at least `0.9025`. -/
theorem catalan_worthiness58_catalan_gt_9025
    (rate_D : LogRate (fun N => ((Dlcm N : ℕ) : ℝ)) 1) :
    ∃ q p : ℕ → ℤ, IsAdmissible catalanReal q p ∧
      ((0.9025 : ℝ) : EReal) ≤ worthiness catalanReal q p := by
  obtain ⟨q, p, hadm, hge⟩ := catalan_worthiness58_catalan_exact rate_D
  refine ⟨q, p, hadm, le_trans ?_ hge⟩
  exact_mod_cast EReal.coe_le_coe_iff.mpr worthinessConstant58_gt.le

end Catalan
