import RequestProject.Final
import RequestProject.EIntegrality
import RequestProject.ERate
import RequestProject.RateTools
import RequestProject.ZudilinExponent
import RequestProject.GeometrySelection
import RequestProject.LinearForms
import RequestProject.ZIntegrality
import RequestProject.EIntegralityB
import RequestProject.ZudilinLimit
import RequestProject.EAbelLimit
import RequestProject.Y2Integrality
import RequestProject.PNT

/-!
# Assembling the unconditional theorem

This file puts the whole argument together.

Two kinds of data are quoted from the literature and from the base note; both are packaged as
structures, so that no axiom is introduced and every theorem that uses them carries them as an
explicit hypothesis.

* `BaseNoteInputs α` collects the archimedean data: the identification of `α` with the two
  limits `G_E`, `G_Z`, and `log D_N = N + o(N)`.  Both identifications are now *proved* for
  `α = G` (Catalan's constant): `G_Z = G` in `ZudilinLimit.lean` and `G_E = G` in
  `EAbelLimit.lean`, so for the headline theorem
  `catalan_worthiness_uncond_catalan` receives its prime-number-theorem input from PNT+
  (`rate_Dlcm`). The integrality of both rows is now proved:
  the Zudilin numerator row `Y₂ n = 2^{e_{3n}} S n P_{3n}` is the explicit integer sequence
  `y2row` (`Y2Integrality.lean`).  The clearing
  exponents themselves are the explicit sequence `eZud` of equation (5.1), whose two required
  properties (`e_{3n} ≥ 12n + 1` and `e_{3n}/n → 12`) are proved in `ZudilinExponent.lean`.

  Neither half of the first row is imported: `A_n ∈ ℕ` is proved in
  `EIntegrality.lean` from the closed form `A_n = ∑_k C(n,k) C(2k,k) C(2n-2k, n-k)`, and the
  integer row itself is the explicit sequence `a1row n = A_{6n}`; the integrality
  `D_n² B_n ∈ ℤ` of the first-row numerator (Imported Theorem E) is proved in
  `EIntegralityB.lean`, and the integer numerator row is the explicit sequence `y1row`.
  The closed form of `A_n` also gives the archimedean rate `(1/n) log A_n → log 8` (`Catalan.rate_Ae`, in `ERate.lean`).  Nor are
  the archimedean rates imported any more: `(1/m) log Q_m → 5 log φ` is proved in
  `ZRatio.lean`, and both rows are shown to converge in `LinearForms.lean`, with the rates
  `(1/n) log |G_E A_n/2 - B_n| → log 4` and `(1/m) log |Q_m G_Z - P_m| → -5 log φ` of their
  linear forms.  All that survives of this material is therefore the identification of the
  approximated number `α` with the two limits `G_E` and `G_Z` (in the intended application
  both are Catalan's constant); the rates `rate_lE`, `rate_lZ`, `rate_Qz` and `α ≠ 0` are
  derived from it below, and the rates of `B_n` and of `P_m` in turn from those.

The *geometry of numbers* step of the base note (Sections 19–22: the double-congruence lattice,
the covolume normalization, and Minkowski's second theorem applied to the balanced rectangle) is
not imported: it is proved in `GeometrySelection.lean` as `lattice_selection`.

Everything else is proved:

* `BaseNoteInputs.rate_X1`, …, `rate_M` are Lemma 16.1 of the base note, the archimedean rates
  of the two rows `X₁ = S A_{6n}`, `Y₁ = 2 S B_{6n}`, `X₂ = 2^{e_{3n}} S Q_{3n}`,
  `Y₂ = 2^{e_{3n}} S P_{3n}` and of the modulus `M_n = D_{6n}² 2^{24n}`;
* `dvd_reduced_cross` is the unconditional divisor `T_n = 2^{24n} ∣ h_n / S_n` of Section 9,
  which rests on the exact Plücker valuation `val_plucker_uncond`;
* `catalan_worthiness_uncond` is Theorem 10.1.
-/

namespace Catalan

open Filter Topology

/-! ### The integer second row -/

lemma four_mul_le_eZud (m : ℕ) : 4 * m ≤ eZud m := by
  simp only [eZud]
  omega

/-- The integer second row `a₂(n) = 2^{e_{3n}} Q_{3n}` of Definition 15.2.  That this is an
integer is Lemma 5.1 of the base note, proved in `ZIntegrality.lean`. -/
noncomputable def a2row (n : ℕ) : ℤ :=
  Classical.choose (two_pow_mul_Qz_isInt (3 * n) (eZud (3 * n)) (four_mul_le_eZud (3 * n)))

lemma a2row_eq (n : ℕ) : ((a2row n : ℤ) : ℚ) = 2 ^ (eZud (3 * n)) * Qz (3 * n) :=
  Classical.choose_spec (two_pow_mul_Qz_isInt (3 * n) (eZud (3 * n)) (four_mul_le_eZud (3 * n)))

/-- The integer first-row numerator `Y₁ n = 2 S n B_{6n}` of Definition 15.2.  That this is an
integer is the integrality half of Imported Theorem E, proved in `EIntegralityB.lean`. -/
noncomputable def y1row (n : ℕ) : ℤ := Classical.choose (Y1row_isInt n)

lemma y1row_eq (n : ℕ) : ((y1row n : ℤ) : ℚ) = Y1row n := by
  rw [Y1row]
  exact Classical.choose_spec (Y1row_isInt n)

/-- The integer second-row numerator `Y₂ n = 2^{e_{3n}} S n P_{3n}` of Definition 15.2.  That
this is an integer is Lemma 5.1 for the numerator row, proved in `Y2Integrality.lean`. -/
noncomputable def y2row (n : ℕ) : ℤ := Classical.choose (Y2row_isInt n)

lemma y2row_eq (n : ℕ) : ((y2row n : ℤ) : ℚ) = Y2row eZud n :=
  Classical.choose_spec (Y2row_isInt n)

/-! ### The imported archimedean data -/

/-- The archimedean material imported from the literature and from the base note. -/
structure BaseNoteInputs (α : ℝ) where
  /-- The approximated number is the limit of the modular row `2 B_n / A_n`
  (Catalan's constant, in the intended application). -/
  alpha_eq_E : α = GEreal
  /-- The approximated number is also the limit of the Zudilin row `P_m / Q_m`. -/
  alpha_eq_Z : α = GZreal
  /-- `log D_N = N + o(N)`. -/
  rate_D : LogRate (fun N => ((Dlcm N : ℕ) : ℝ)) 1

namespace BaseNoteInputs

variable {α : ℝ} (i : BaseNoteInputs α)

/-! ### The rates that were previously imported, now derived -/

include i in
/-- The approximated number is nonzero: it is at least `1/2`. -/
lemma alpha_ne_zero : α ≠ 0 := by
  rw [i.alpha_eq_E]
  exact GEreal_pos.ne'

include i in
/-- Equation (9.3): `(1/n) log |α A_n/2 - B_n| → log 4`. -/
lemma rate_lE : LogRate (fun n => α / 2 * ((Ae n : ℚ) : ℝ) - ((Be n : ℚ) : ℝ)) (Real.log 4) := by
  have h := Catalan.rate_linE
  refine h.of_eq (fun n => ?_)
  rw [i.alpha_eq_E]
  rfl

/-- Imported Theorem Z, first half: `(1/m) log |Q_m| → 5 log φ`. -/
lemma rate_Qz : LogRate (fun m => ((Qz m : ℚ) : ℝ)) (5 * Real.log Real.goldenRatio) :=
  Catalan.rate_Qz

include i in
/-- Imported Theorem Z, second half: `(1/m) log |Q_m α - P_m| → -5 log φ`. -/
lemma rate_lZ : LogRate (fun m => ((Qz m : ℚ) : ℝ) * α - ((Pz m : ℚ) : ℝ))
    (-(5 * Real.log Real.goldenRatio)) := by
  have h := Catalan.rate_linZ
  refine h.of_eq (fun m => ?_)
  rw [i.alpha_eq_Z]
  rfl

/-! ### Lemma 16.1: the archimedean rates of the two rows -/

lemma Sfac_ne_zero (n : ℕ) : ((Sfac n : ℕ) : ℝ) ≠ 0 := by
  have := Sfac_pos n
  positivity

include i in
lemma rate_Sfac : LogRate (fun n => ((Sfac n : ℕ) : ℝ)) 12 := by
  have hD6 : LogRate (fun n => ((Dlcm (6 * n) : ℕ) : ℝ)) (6 * 1) :=
    LogRate.comp_mul 6 (by norm_num) i.rate_D
  have hne : ∀ᶠ n in atTop, ((Dlcm (6 * n) : ℕ) : ℝ) ≠ 0 := by
    filter_upwards with n
    have := Dlcm_pos (6 * n)
    positivity
  have hmul := hD6.mul hD6 hne hne
  have : (6 : ℝ) * 1 + 6 * 1 = 12 := by norm_num
  rw [this] at hmul
  refine hmul.of_eq (fun n => ?_)
  unfold Sfac
  push_cast
  ring

lemma rate_pow_two_eZud : LogRate (fun n => (2 : ℝ) ^ (eZud (3 * n))) (12 * Real.log 2) := by
  have h := tendsto_eZud_three_mul.mul_const (Real.log 2)
  refine h.congr' ?_
  filter_upwards with n
  rw [abs_of_pos (by positivity), Real.log_pow]
  ring

lemma rate_pow_two_24 : LogRate (fun n : ℕ => (2 : ℝ) ^ (24 * n)) (24 * Real.log 2) := by
  refine Filter.Tendsto.congr' ?_ (tendsto_const_nhds (x := 24 * Real.log 2) (f := atTop (α := ℕ)))
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [abs_of_pos (by positivity), Real.log_pow]
  push_cast
  field_simp

lemma Ae_six_ne_zero : ∀ᶠ n in atTop, ((Ae (6 * n) : ℚ) : ℝ) ≠ 0 := by
  filter_upwards with n
  exact_mod_cast Rat.cast_ne_zero.mpr (Ae_ne_zero (6 * n))

lemma Be_six_ne_zero : ∀ᶠ n in atTop, ((Be (6 * n) : ℚ) : ℝ) ≠ 0 := by
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have h6 : 6 * n = (6 * n - 1) + 1 := by omega
  rw [h6]
  exact_mod_cast Rat.cast_ne_zero.mpr (Be_ne_zero_and_val (6 * n - 1)).1

lemma Qz_three_ne_zero : ∀ᶠ n in atTop, ((Qz (3 * n) : ℚ) : ℝ) ≠ 0 := by
  filter_upwards with n
  exact_mod_cast Rat.cast_ne_zero.mpr (Qz_ne_zero (3 * n))

lemma Pz_three_ne_zero : ∀ᶠ n in atTop, ((Pz (3 * n) : ℚ) : ℝ) ≠ 0 := by
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  exact_mod_cast Rat.cast_ne_zero.mpr (Pz_ne_zero (3 * n) (by omega))

lemma rate_Ae_six : LogRate (fun n => ((Ae (6 * n) : ℚ) : ℝ)) (6 * Real.log 8) :=
  LogRate.comp_mul 6 (by norm_num) Catalan.rate_Ae

include i in
/-- Imported Theorem E gives `(1/n) log |B_n| → log 8`; here it is derived from the proved rate
of `A_n` together with `(1/n) log |α A_n/2 - B_n| → log 4 < log 8`. -/
lemma rate_Be : LogRate (fun n => ((Be n : ℚ) : ℝ)) (Real.log 8) := by
  have hhalf : α / 2 ≠ 0 := div_ne_zero i.alpha_ne_zero (by norm_num)
  have hA : LogRate (fun n => α / 2 * ((Ae n : ℚ) : ℝ)) (0 + Real.log 8) :=
    (LogRate.const (α / 2)).mul Catalan.rate_Ae (Eventually.of_forall (fun _ => hhalf))
      (Eventually.of_forall (fun n => by exact_mod_cast Rat.cast_ne_zero.mpr (Ae_ne_zero n)))
  rw [zero_add] at hA
  have hlt : Real.log 4 < Real.log 8 := Real.log_lt_log (by norm_num) (by norm_num)
  have hne : ∀ᶠ n : ℕ in atTop, α / 2 * ((Ae n : ℚ) : ℝ) ≠ 0 := by
    filter_upwards with n
    exact mul_ne_zero hhalf (by exact_mod_cast Rat.cast_ne_zero.mpr (Ae_ne_zero n))
  have h := (hA.sub_dominant i.rate_lE.toLE hlt hne).1
  exact h.of_eq (fun n => by ring)

include i in
lemma rate_Be_six : LogRate (fun n => ((Be (6 * n) : ℚ) : ℝ)) (6 * Real.log 8) :=
  LogRate.comp_mul 6 (by norm_num) i.rate_Be

lemma rate_Qz_three :
    LogRate (fun n => ((Qz (3 * n) : ℚ) : ℝ)) (3 * (5 * Real.log Real.goldenRatio)) :=
  LogRate.comp_mul 3 (by norm_num) rate_Qz

include i in
/-- Imported Theorem Z gives `(1/m) log |P_m| → 5 log φ`; here it is derived from the rate of
`Q_m` together with `(1/m) log |Q_m α - P_m| → -5 log φ < 5 log φ`. -/
lemma rate_Pz : LogRate (fun m => ((Pz m : ℚ) : ℝ)) (5 * Real.log Real.goldenRatio) := by
  have hpos := log_golden_pos
  have hQ : LogRate (fun m => ((Qz m : ℚ) : ℝ) * α) (5 * Real.log Real.goldenRatio + 0) :=
    rate_Qz.mul (LogRate.const α)
      (Eventually.of_forall (fun m => by exact_mod_cast Rat.cast_ne_zero.mpr (Qz_ne_zero m)))
      (Eventually.of_forall (fun _ => i.alpha_ne_zero))
  rw [add_zero] at hQ
  have hlt : -(5 * Real.log Real.goldenRatio) < 5 * Real.log Real.goldenRatio := by linarith
  have hne : ∀ᶠ m : ℕ in atTop, ((Qz m : ℚ) : ℝ) * α ≠ 0 := by
    filter_upwards with m
    exact mul_ne_zero (by exact_mod_cast Rat.cast_ne_zero.mpr (Qz_ne_zero m)) i.alpha_ne_zero
  have h := (hQ.sub_dominant i.rate_lZ.toLE hlt hne).1
  exact h.of_eq (fun m => by ring)

include i in
lemma rate_Pz_three :
    LogRate (fun n => ((Pz (3 * n) : ℚ) : ℝ)) (3 * (5 * Real.log Real.goldenRatio)) :=
  LogRate.comp_mul 3 (by norm_num) i.rate_Pz

include i in
lemma rate_lE_six :
    LogRate (fun n => α / 2 * ((Ae (6 * n) : ℚ) : ℝ) - ((Be (6 * n) : ℚ) : ℝ))
      (6 * Real.log 4) :=
  LogRate.comp_mul (f := fun N => α / 2 * ((Ae N : ℚ) : ℝ) - ((Be N : ℚ) : ℝ))
    6 (by norm_num) i.rate_lE

include i in
lemma rate_lZ_three :
    LogRate (fun n => ((Qz (3 * n) : ℚ) : ℝ) * α - ((Pz (3 * n) : ℚ) : ℝ))
      (3 * -(5 * Real.log Real.goldenRatio)) :=
  LogRate.comp_mul (f := fun N => ((Qz N : ℚ) : ℝ) * α - ((Pz N : ℚ) : ℝ))
    3 (by norm_num) i.rate_lZ

include i in
lemma lE_six_ne_zero :
    ∀ᶠ n in atTop, α / 2 * ((Ae (6 * n) : ℚ) : ℝ) - ((Be (6 * n) : ℚ) : ℝ) ≠ 0 := by
  refine eventually_comp_mul (P := fun N => α / 2 * ((Ae N : ℚ) : ℝ) - ((Be N : ℚ) : ℝ) ≠ 0)
    6 (by norm_num) ?_
  refine LogRate.eventually_ne_zero ?_ i.rate_lE
  have : (0 : ℝ) < Real.log 4 := Real.log_pos (by norm_num)
  linarith

include i in
lemma lZ_three_ne_zero :
    ∀ᶠ n in atTop, ((Qz (3 * n) : ℚ) : ℝ) * α - ((Pz (3 * n) : ℚ) : ℝ) ≠ 0 := by
  refine eventually_comp_mul (P := fun N => ((Qz N : ℚ) : ℝ) * α - ((Pz N : ℚ) : ℝ) ≠ 0)
    3 (by norm_num) ?_
  refine LogRate.eventually_ne_zero ?_ i.rate_lZ
  have hpos := log_golden_pos
  intro hc
  linarith

include i in
/-- Equation (16.5): `log |X_{1,n}| = A_E n + o(n)`. -/
theorem rate_X1 : LogRate (fun n : ℕ => (((Sfac n : ℤ) * a1row n : ℤ) : ℝ)) AErate := by
  have h := (i.rate_Sfac).mul rate_Ae_six
    (Eventually.of_forall (fun n => Sfac_ne_zero n)) Ae_six_ne_zero
  have hval : (12 : ℝ) + 6 * Real.log 8 = AErate := by
    rw [AErate, log_eight_eq]; ring
  rw [hval] at h
  refine h.of_eq (fun n => ?_)
  have := a1row_cast n
  push_cast [← this]
  ring

include i in
/-- Equation (16.6): `log |Y_{1,n}| = A_E n + o(n)`. -/
theorem rate_Y1 : LogRate (fun n : ℕ => ((y1row n : ℤ) : ℝ)) AErate := by
  have h := ((LogRate.const (2 : ℝ)).mul i.rate_Sfac (Eventually.of_forall (by norm_num))
    (Eventually.of_forall (fun n => Sfac_ne_zero n))).mul (i.rate_Be_six)
      (by filter_upwards with n; exact mul_ne_zero (by norm_num) (Sfac_ne_zero n))
      Be_six_ne_zero
  have hval : ((0 : ℝ) + 12) + 6 * Real.log 8 = AErate := by
    rw [AErate, log_eight_eq]; ring
  rw [hval] at h
  refine h.of_eq (fun n => ?_)
  have hY := y1row_eq n
  rw [Y1row] at hY
  have : ((y1row n : ℤ) : ℝ) = 2 * ((Sfac n : ℕ) : ℝ) * ((Be (6 * n) : ℚ) : ℝ) := by
    have := congrArg (fun z : ℚ => (z : ℝ)) hY
    push_cast at this ⊢
    linarith [this]
  rw [this]

include i in
/-- Equation (16.7): `log |λ_{1,n}| = E_E n + o(n)`. -/
theorem rate_l1 :
    LogRate (fun n : ℕ => (((Sfac n : ℤ) * a1row n : ℤ) : ℝ) * α - ((y1row n : ℤ) : ℝ)) EErate := by
  have h := ((LogRate.const (2 : ℝ)).mul i.rate_Sfac (Eventually.of_forall (by norm_num))
    (Eventually.of_forall (fun n => Sfac_ne_zero n))).mul i.rate_lE_six
      (by filter_upwards with n; exact mul_ne_zero (by norm_num) (Sfac_ne_zero n))
      i.lE_six_ne_zero
  have hval : ((0 : ℝ) + 12) + 6 * Real.log 4 = EErate := by
    rw [EErate, log_four_eq]; ring
  rw [hval] at h
  refine h.of_eq (fun n => ?_)
  have hA := congrArg (fun z : ℚ => (z : ℝ)) (a1row_cast n)
  have hY := congrArg (fun z : ℚ => (z : ℝ)) (y1row_eq n)
  rw [Y1row] at hY
  push_cast at hA hY ⊢
  rw [hA, hY]
  ring

include i in
/-- Equation (16.8): `log |X_{2,n}| = A_Z n + o(n)`. -/
theorem rate_X2 : LogRate (fun n : ℕ => (((Sfac n : ℤ) * a2row n : ℤ) : ℝ)) AZrate := by
  have h := (rate_pow_two_eZud.mul i.rate_Sfac
    (Eventually.of_forall (fun n => by positivity))
    (Eventually.of_forall (fun n => Sfac_ne_zero n))).mul rate_Qz_three
      (by filter_upwards with n; exact mul_ne_zero (by positivity) (Sfac_ne_zero n))
      Qz_three_ne_zero
  have hval : (12 * Real.log 2 + 12) + 3 * (5 * Real.log Real.goldenRatio) = AZrate := by
    rw [AZrate]; ring
  rw [hval] at h
  refine h.of_eq (fun n => ?_)
  have hA := congrArg (fun z : ℚ => (z : ℝ)) (a2row_eq n)
  push_cast at hA ⊢
  rw [hA]
  ring

include i in
/-- Equation (16.9): `log |Y_{2,n}| = A_Z n + o(n)`. -/
theorem rate_Y2 : LogRate (fun n : ℕ => ((y2row n : ℤ) : ℝ)) AZrate := by
  have h := (rate_pow_two_eZud.mul i.rate_Sfac
    (Eventually.of_forall (fun n => by positivity))
    (Eventually.of_forall (fun n => Sfac_ne_zero n))).mul i.rate_Pz_three
      (by filter_upwards with n; exact mul_ne_zero (by positivity) (Sfac_ne_zero n))
      Pz_three_ne_zero
  have hval : (12 * Real.log 2 + 12) + 3 * (5 * Real.log Real.goldenRatio) = AZrate := by
    rw [AZrate]; ring
  rw [hval] at h
  refine h.of_eq (fun n => ?_)
  have hY := congrArg (fun z : ℚ => (z : ℝ)) (y2row_eq n)
  rw [Y2row] at hY
  push_cast at hY ⊢
  rw [hY]

include i in
/-- Equation (16.10): `log |λ_{2,n}| = E_Z n + o(n)`. -/
theorem rate_l2 :
    LogRate (fun n : ℕ => (((Sfac n : ℤ) * a2row n : ℤ) : ℝ) * α - ((y2row n : ℤ) : ℝ)) EZrate := by
  have h := (rate_pow_two_eZud.mul i.rate_Sfac
    (Eventually.of_forall (fun n => by positivity))
    (Eventually.of_forall (fun n => Sfac_ne_zero n))).mul i.rate_lZ_three
      (by filter_upwards with n; exact mul_ne_zero (by positivity) (Sfac_ne_zero n))
      i.lZ_three_ne_zero
  have hval : (12 * Real.log 2 + 12) + 3 * -(5 * Real.log Real.goldenRatio) = EZrate := by
    rw [EZrate]; ring
  rw [hval] at h
  refine h.of_eq (fun n => ?_)
  have hA := congrArg (fun z : ℚ => (z : ℝ)) (a2row_eq n)
  have hY := congrArg (fun z : ℚ => (z : ℝ)) (y2row_eq n)
  rw [Y2row] at hY
  push_cast at hA hY ⊢
  rw [hA, hY]
  ring

include i in
/-- Equations (10.3) and (18.6): the division modulus `M_n = D_{6n}² 2^{24n}` has rate
`σ = 12 + 24 log 2`. -/
theorem rate_M :
    LogRate (fun n : ℕ => (((Sfac n : ℤ) * (2 : ℤ) ^ (24 * n) : ℤ) : ℝ)) sigmaRate := by
  have h := (i.rate_Sfac).mul rate_pow_two_24
    (Eventually.of_forall (fun n => Sfac_ne_zero n))
    (Eventually.of_forall (fun n => by positivity))
  have hval : (12 : ℝ) + 24 * Real.log 2 = sigmaRate := by rw [sigmaRate]
  rw [hval] at h
  refine h.of_eq (fun n => ?_)
  push_cast
  ring

/-! ### The unconditional divisor -/

/-- Equation (18.5): `T_n = 2^{24n}` divides the reduced cross determinant
`a₁ Y₂ - a₂ Y₁ = h_n / S_n`.  This is where the exact Plücker valuation enters. -/
theorem dvd_reduced_cross (n : ℕ) :
    (2 : ℤ) ^ (24 * n) ∣ a1row n * y2row n - a2row n * y1row n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  refine two_pow_dvd_hRed eZud n hn (eZud_three_mul_lb n hn) _ ?_
  rw [hRed]
  push_cast [a1row_cast n, a2row_eq n, y1row_eq n, y2row_eq n]
  ring

end BaseNoteInputs

/-- The crossed gap (22.1) for the two Catalan rows: `A_E + E_Z < A_Z + E_E`, equivalent to
`log 2 < 5 log φ`. -/
theorem crossed_gap : AErate + EZrate < AZrate + EErate := by
  have h1 : (0.4812117 : ℝ) < Real.log Real.goldenRatio := log_golden_gt
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  rw [AErate, EZrate, AZrate, EErate]
  linarith

/-! ### Theorem 10.1 -/

/-- Theorem 10.1, the unconditional Catalan worthiness theorem.  Relative to the imported
archimedean data of the base note (`BaseNoteInputs`), there is an admissible approximation
sequence to `α` whose worthiness is at least

`30 log φ / (6 + (45/2) log φ) = 0.8579144524…`. -/
theorem catalan_worthiness_uncond {α : ℝ} (i : BaseNoteInputs α) :
    ∃ q p : ℕ → ℤ, IsAdmissible α q p ∧
      ((worthinessConstant : ℝ) : EReal) ≤ worthiness α q p := by
  have hAZ : AZrate ≠ 0 := by
    have h1 := log_golden_pos
    have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [AZrate]
    linarith
  have hEE : EErate ≠ 0 := by
    have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    rw [EErate]
    linarith
  have hX2ne : ∀ᶠ n in atTop, (((Sfac n : ℤ) * a2row n : ℤ) : ℝ) ≠ 0 :=
    LogRate.eventually_ne_zero hAZ i.rate_X2
  have hl1ne : ∀ᶠ n in atTop,
      (((Sfac n : ℤ) * a1row n : ℤ) : ℝ) * α - ((y1row n : ℤ) : ℝ) ≠ 0 :=
    LogRate.eventually_ne_zero hEE i.rate_l1
  obtain ⟨d⟩ := lattice_selection α AErate EErate AZrate EZrate sigmaRate a1row a2row y1row y2row
    (fun n => (Sfac n : ℤ)) (fun n => (2 : ℤ) ^ (24 * n))
    (fun n => show (0:ℤ) < (Sfac n : ℤ) from Int.natCast_pos.mpr (Sfac_pos n))
    (fun n => by positivity)
    i.rate_X1 i.rate_l1 i.rate_X2 i.rate_l2 i.rate_M
    BaseNoteInputs.dvd_reduced_cross crossed_gap hX2ne hl1ne
  have hH : AZrate - (sigmaRate + EZrate - EErate) / 2 = Hrate := by rw [Hrate, xBal]
  have hF : (sigmaRate + EZrate - EErate) / 2 + EErate - sigmaRate = Frate := by rw [Frate, xBal]
  rw [hH, hF] at d
  exact catalan_worthiness_of_balancedMinimaData d

/-- Equation (10.8): the numerical form of Theorem 10.1. -/
theorem catalan_worthiness_uncond_gt {α : ℝ} (i : BaseNoteInputs α) :
    ∃ q p : ℕ → ℤ, IsAdmissible α q p ∧ ((0.857914 : ℝ) : EReal) ≤ worthiness α q p := by
  obtain ⟨q, p, hadm, hge⟩ := catalan_worthiness_uncond i
  refine ⟨q, p, hadm, le_trans ?_ hge⟩
  exact_mod_cast EReal.coe_le_coe_iff.mpr worthinessConstant_gt.le

/-- Theorem 10.1 stated for the limit `G_E` of the modular row.

That the two constructions converge to the same number, `G_E = G_Z`, is now proved:  both are
Catalan's constant (`GEreal_eq_catalanReal`, `GZreal_eq_catalanReal`). -/
theorem catalan_worthiness_uncond_GEreal
    (rate_D : LogRate (fun N => ((Dlcm N : ℕ) : ℝ)) 1) :
    ∃ q p : ℕ → ℤ, IsAdmissible GEreal q p ∧
      ((0.857914 : ℝ) : EReal) ≤ worthiness GEreal q p :=
  catalan_worthiness_uncond_gt
    ⟨rfl, GEreal_eq_catalanReal.trans GZreal_eq_catalanReal.symm, rate_D⟩

/-- **Theorem 10.1 for Catalan's constant itself.**

Both limits are now identified with Catalan's constant — the Zudilin row in `ZudilinLimit.lean`
(from Rivoal's identity) and the modular row in `EAbelLimit.lean` (from the accelerated series
`∑_j 4^j/(C(2j,j)(2j+1)²) = 2G` and an Abel-type argument) — and PNT+ supplies the required
prime number theorem. -/
theorem catalan_worthiness_uncond_catalan :
    ∃ q p : ℕ → ℤ, IsAdmissible catalanReal q p ∧
      ((0.857914 : ℝ) : EReal) ≤ worthiness catalanReal q p :=
  catalan_worthiness_uncond_gt
    ⟨GEreal_eq_catalanReal.symm, GZreal_eq_catalanReal.symm, rate_Dlcm⟩

end Catalan
