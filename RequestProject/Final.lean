import RequestProject.TwoRow
import RequestProject.Constant
import RequestProject.Rows

/-!
# The `0.857914` worthiness theorem

Section 10 of the unconditional note (Theorem 10.1), assembled from

* the archimedean rates (10.1)–(10.2) of the two rows and the rate (10.3) of the division
  modulus, which are the *imported* estimates of the base note;
* the balanced two-row selection `two_row_selection` (Theorem 11.1), proved in `TwoRow.lean`;
* the numerical certification of the constant in `Constant.lean`.

The data produced by the base note's lattice construction (Sections 15–22 there: the divided
successive-minima rows coming from Minkowski's second theorem applied to the balanced rectangle,
i.e. estimates (22.20)–(22.23) and (22.25)) is packaged in the structure `BalancedMinimaData`.
No axiom is introduced: `worthiness_ge_of_balancedMinimaData` and
`catalan_worthiness_of_balancedMinimaData` take such a term as a hypothesis.
-/

namespace Catalan

open Filter Topology

/-! ### The archimedean rates -/

/-- `A_E = 12 + 18 log 2`, equation (10.1). -/
noncomputable def AErate : ℝ := 12 + 18 * Real.log 2

/-- `E_E = 12 + 12 log 2`, equation (10.1). -/
noncomputable def EErate : ℝ := 12 + 12 * Real.log 2

/-- `A_Z = 12 + 12 log 2 + 15 log φ`, equation (10.2). -/
noncomputable def AZrate : ℝ := 12 + 12 * Real.log 2 + 15 * Real.log Real.goldenRatio

/-- `E_Z = 12 + 12 log 2 - 15 log φ`, equation (10.2). -/
noncomputable def EZrate : ℝ := 12 + 12 * Real.log 2 - 15 * Real.log Real.goldenRatio

/-- The rate `σ = 12 + 24 log 2` of the division modulus `M_n = D_{6n}² 2^{24n}`,
equation (10.3). -/
noncomputable def sigmaRate : ℝ := 12 + 24 * Real.log 2

/-- The balancing parameter `x = (σ + E_Z - E_E)/2`, equation (10.4). -/
noncomputable def xBal : ℝ := (sigmaRate + EZrate - EErate) / 2

/-- The denominator rate `H = A_Z - x`, equation (10.5). -/
noncomputable def Hrate : ℝ := AZrate - xBal

/-- The linear-form rate `F = x + E_E - σ`, equation (10.6). -/
noncomputable def Frate : ℝ := xBal + EErate - sigmaRate

lemma xBal_eq : xBal = 6 + 12 * Real.log 2 - 15 / 2 * Real.log Real.goldenRatio := by
  unfold xBal sigmaRate EZrate EErate; ring

/-- Equation (10.5): `H = 6 + (45/2) log φ`. -/
theorem Hrate_eq : Hrate = 6 + 45 / 2 * Real.log Real.goldenRatio := by
  unfold Hrate AZrate; rw [xBal_eq]; ring

/-- Equation (10.6): `F = 6 - (15/2) log φ`. -/
theorem Frate_eq : Frate = 6 - 15 / 2 * Real.log Real.goldenRatio := by
  unfold Frate EErate sigmaRate; rw [xBal_eq]; ring

theorem Hrate_pos : 0 < Hrate := by
  rw [Hrate_eq]
  have := log_golden_pos
  linarith

theorem Frate_pos : 0 < Frate := by
  rw [Frate_eq]
  have := log_golden_lt
  linarith

/-- `H - F = 30 log φ`, the crossed gap of equation (10.7). -/
theorem Hrate_sub_Frate : Hrate - Frate = 30 * Real.log Real.goldenRatio := by
  rw [Hrate_eq, Frate_eq]; ring

/-- Equation (10.7): `1 - F/H` is exactly the worthiness constant. -/
theorem one_sub_ratio_eq : 1 - Frate / Hrate = worthinessConstant := by
  have hH : Hrate ≠ 0 := ne_of_gt Hrate_pos
  rw [worthinessConstant, ← Hrate_eq]
  field_simp
  linarith [Hrate_sub_Frate]

/-! ### The balanced-minima data imported from the base note -/

/-- The output of the base note's lattice construction (Sections 15–22): for every `n` two
divided integer rows `(Q₁,P₁)`, `(Q₂,P₂)` coming from the two successive minima of the balanced
rectangle, together with the exponential estimates (22.20)–(22.23) and the determinant lower
bound (22.25).  Here `r n ≥ 0` is the imbalance `-(1/n) log μ₁,ₙ` and `ε n → 0` dominates all the
normalized rate errors. -/
structure BalancedMinimaData (α H F : ℝ) where
  /-- Denominator of the first divided row. -/
  Q1 : ℕ → ℤ
  /-- Denominator of the second divided row. -/
  Q2 : ℕ → ℤ
  /-- Numerator of the first divided row. -/
  P1 : ℕ → ℤ
  /-- Numerator of the second divided row. -/
  P2 : ℕ → ℤ
  /-- The imbalance `r n = -(1/n) log μ₁,ₙ ≥ 0` of the two successive minima. -/
  r : ℕ → ℝ
  /-- A positive sequence dominating all the normalized `o(n)` rate errors. -/
  eps : ℕ → ℝ
  r_nonneg : ∀ n, 0 ≤ r n
  eps_pos : ∀ n, 0 < eps n
  eps_tendsto : Tendsto eps atTop (𝓝 0)
  sqrt_eps_mul_tendsto : Tendsto (fun n : ℕ => Real.sqrt (eps n) * n) atTop atTop
  /-- Estimate (22.20), for all sufficiently large `n`. -/
  bound_Q1 : ∀ᶠ n in atTop, |(Q1 n : ℝ)| ≤ Real.exp ((H - r n + eps n) * n)
  /-- Estimate (22.21), for all sufficiently large `n`. -/
  bound_l1 : ∀ᶠ n in atTop, |(Q1 n : ℝ) * α - (P1 n : ℝ)| ≤ Real.exp ((F - r n + eps n) * n)
  /-- Estimate (22.23), for all sufficiently large `n`. -/
  bound_l2 : ∀ᶠ n in atTop, |(Q2 n : ℝ) * α - (P2 n : ℝ)| ≤ Real.exp ((F + r n + eps n) * n)
  /-- Estimate (22.25), for all sufficiently large `n`. -/
  bound_det : ∀ᶠ n in atTop,
    Real.exp ((H + F - eps n) * n) ≤ |((Q1 n * P2 n - Q2 n * P1 n : ℤ) : ℝ)|

/-- Theorem 11.1 applied to the balanced-minima data: worthiness at least `1 - F/H`. -/
theorem worthiness_ge_of_balancedMinimaData {α H F : ℝ} (hH : 0 < H) (hF : 0 < F)
    (d : BalancedMinimaData α H F) :
    ∃ q p : ℕ → ℤ, IsAdmissible α q p ∧ ((1 - F / H : ℝ) : EReal) ≤ worthiness α q p :=
  two_row_selection hH hF d.Q1 d.Q2 d.P1 d.P2 d.r d.eps d.r_nonneg d.eps_pos d.eps_tendsto
    d.sqrt_eps_mul_tendsto d.bound_Q1 d.bound_l1 d.bound_l2 d.bound_det

/-! ### Theorem 10.1 -/

/-- Theorem 10.1, the unconditional Catalan worthiness theorem.  Given the balanced-minima data
of the base note at the rates `H = 6 + (45/2) log φ` and `F = 6 - (15/2) log φ` produced by the
unconditional division modulus `M_n = D_{6n}² 2^{24n}` (whose `2^{24n}` factor is `val_hRow_ge`),
there is an admissible approximation sequence to `α` of worthiness at least

`30 log φ / (6 + (45/2) log φ) = 0.8579144524…`. -/
theorem catalan_worthiness_of_balancedMinimaData {α : ℝ} (d : BalancedMinimaData α Hrate Frate) :
    ∃ q p : ℕ → ℤ, IsAdmissible α q p ∧
      ((worthinessConstant : ℝ) : EReal) ≤ worthiness α q p := by
  obtain ⟨q, p, hadm, hge⟩ := worthiness_ge_of_balancedMinimaData Hrate_pos Frate_pos d
  exact ⟨q, p, hadm, by rwa [one_sub_ratio_eq] at hge⟩

/-- Equation (10.8): the numerical form of Theorem 10.1. -/
theorem catalan_worthiness_gt_857914 {α : ℝ} (d : BalancedMinimaData α Hrate Frate) :
    ∃ q p : ℕ → ℤ, IsAdmissible α q p ∧ ((0.857914 : ℝ) : EReal) ≤ worthiness α q p := by
  obtain ⟨q, p, hadm, hge⟩ := catalan_worthiness_of_balancedMinimaData d
  refine ⟨q, p, hadm, le_trans ?_ hge⟩
  exact_mod_cast EReal.coe_le_coe_iff.mpr worthinessConstant_gt.le

end Catalan
