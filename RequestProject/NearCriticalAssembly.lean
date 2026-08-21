import RequestProject.Assembly
import RequestProject.Assembly58
import RequestProject.NearCritical
import RequestProject.NesterenkoCross

/-!
# The near-critical (`1 - ε`) worthiness theorem

This file assembles the Zudilin × Nesterenko construction of the near-critical dossier.

* Row 1 is the Zudilin row already built in the project: `X₁ n = D_{6n}² · 2^{e_{3n}} Q_{3n}`,
  `Y₁ n = 2^{e_{3n}} D_{6n}² P_{3n}` (`a2row`, `y2row` of `Assembly.lean`), with the proved
  rates `A_Z = 12 + 12 log 2 + 15 log φ` and `E_Z = 12 + 12 log 2 - 15 log φ`.
* Row 2 is the Nesterenko `(4,7)` row, over the same lcm square `S n = D_{6n}²`.  Its two
  archimedean rates `A_N`, `E_N` (`NearCritical.lean`) and the `2`-adic cross divisibility
  `2^{24n} ∣ a₁ Y₂ - a₂ Y₁` are the imported Nesterenko package of the dossier; they are
  collected in the hypothesis structure `NesterenkoInputs` below, so that no axiom is
  introduced and every theorem carries them explicitly.
* The division modulus is `M_n = D_{6n}² · 2^{⌊k n⌋}` for a real parameter `0 ≤ k`, of rate
  `σ(k) = 12 + k log 2`.  Since `k < k_* < 24`, the factor `2^{⌊kn⌋}` divides `2^{24n}` and
  therefore divides the reduced cross determinant.

Feeding this into the abstract geometry-of-numbers selection `lattice_selection` gives, for
every `0 ≤ k < k_*`, an admissible approximation sequence of worthiness at least

`δ(k) = D / (D + F(k))`,  `D = A_N - E_N`,  `F(k) = (log 2/2)(k_* - k)`,

which is `> 0.99` already at `k = 22`, and which tends to `1` as `k ↑ k_*`.  The headline
result is therefore

`∀ ε > 0, ∃ an admissible construction of worthiness > 1 - ε`

(`worthiness_nearcritical_one_sub_eps`, and `catalan_worthiness_one_sub_eps` for Catalan's
constant itself).  No claim of irrationality follows: the constructions are a family, not a
single sequence of worthiness `1`.
-/

namespace Catalan

open Filter Topology

/-! ### The imported Nesterenko row -/

/-- The Nesterenko `(4,7)` data, imported from the literature exactly as in Section 37 of the
dossier: an integer row `(S · a, Y)` over the common lcm square `S n = D_{6n}²`, with the
archimedean rates `A_N` and `E_N`, and the `2`-adic cross divisibility `2^{24n} ∣ h_n / S_n`
against the Zudilin row. -/
structure NesterenkoInputs (α : ℝ) where
  /-- The reduced Nesterenko denominator row `a_n` (so that `X₂ n = S n · a_n`). -/
  aRow : ℕ → ℤ
  /-- The Nesterenko numerator row `Y₂ n`. -/
  yRow : ℕ → ℤ
  /-- `log |X₂ n| = A_N n + o(n)`. -/
  rate_X : LogRate (fun n : ℕ => (((Sfac n : ℤ) * aRow n : ℤ) : ℝ)) ANrate
  /-- `log |X₂ n α - Y₂ n| = E_N n + o(n)`. -/
  rate_l : LogRate
    (fun n : ℕ => (((Sfac n : ℤ) * aRow n : ℤ) : ℝ) * α - ((yRow n : ℤ) : ℝ)) ENrate
  /-- The normalized Plücker determinant is divisible by `2^{24n}`. -/
  cross : ∀ n : ℕ, (2 : ℤ) ^ (24 * n) ∣ a2row n * yRow n - aRow n * y2row n

/-- The cross divisibility does not have to be assumed: it follows from the imported `2`-adic
Nesterenko package through Sections 17–20 of the dossier (`NesterenkoCross.lean`).  Only the
two archimedean rates of the Nesterenko row are needed on top of it. -/
def NesterenkoInputs.ofPadic {α : ℝ} (N : NesterenkoPadicInputs)
    (rate_X : LogRate (fun n : ℕ => (((Sfac n : ℤ) * N.aN n : ℤ) : ℝ)) ANrate)
    (rate_l : LogRate
      (fun n : ℕ => (((Sfac n : ℤ) * N.aN n : ℤ) : ℝ) * α - ((N.yN n : ℤ) : ℝ)) ENrate) :
    NesterenkoInputs α where
  aRow := N.aN
  yRow := N.yN
  rate_X := rate_X
  rate_l := rate_l
  cross := dvd_reduced_cross_N N

/-! ### The division modulus `2^{⌊k n⌋}` -/

/-- The dyadic exponent `⌊k n⌋` of the division modulus. -/
noncomputable def TexpNC (k : ℝ) (n : ℕ) : ℕ := ⌊k * n⌋₊

lemma TexpNC_le {k : ℝ} (hk : k ≤ 24) (n : ℕ) : TexpNC k n ≤ 24 * n := by
  have hkn : k * n ≤ ((24 * n : ℕ) : ℝ) := by
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    push_cast
    nlinarith
  have := Nat.floor_le_of_le hkn
  simpa [TexpNC, Nat.floor_natCast] using this

lemma tendsto_TexpNC {k : ℝ} (hk : 0 ≤ k) :
    Tendsto (fun n : ℕ => (TexpNC k n : ℝ) / n) atTop (𝓝 k) := by
  have hupp : Tendsto (fun _ : ℕ => k) atTop (𝓝 k) := tendsto_const_nhds
  have hlow : Tendsto (fun n : ℕ => k - 1 / (n : ℝ)) atTop (𝓝 k) := by
    simpa using (tendsto_const_nhds (x := k) (f := atTop (α := ℕ))).sub
      (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hfl : k * n - 1 < (TexpNC k n : ℝ) := by
      have := Nat.lt_floor_add_one (k * (n : ℝ))
      simp only [TexpNC]
      linarith
    rw [le_div_iff₀ hnR]
    have : (k - 1 / (n : ℝ)) * n = k * n - 1 := by field_simp
    rw [this]
    linarith
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hfl : (TexpNC k n : ℝ) ≤ k * n := by
      simpa [TexpNC] using Nat.floor_le (by positivity : (0:ℝ) ≤ k * (n : ℝ))
    rw [div_le_iff₀ hnR]
    linarith

lemma rate_pow_two_TexpNC {k : ℝ} (hk : 0 ≤ k) :
    LogRate (fun n : ℕ => (2 : ℝ) ^ (TexpNC k n)) (k * Real.log 2) :=
  logRate_two_pow (tendsto_TexpNC hk)

/-! ### Positivity of the rates -/

theorem ANrate_pos : 0 < ANrate := by
  have h1 : 0 < Real.log TplusNC := by
    rw [log_TplusNC_eq]
    have h2 := log_TminusNC_lt
    have h3 : (0:ℝ) ≤ Real.log (32/27) := Real.log_nonneg (by norm_num)
    linarith
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [ANrate]
  linarith

theorem EZrate_pos : 0 < EZrate := by
  have h1 := log_golden_lt_tight
  have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  rw [EZrate]
  linarith

/-! ### The fixed-`k` theorem -/

namespace BaseNoteInputs

variable {α : ℝ} (i : BaseNoteInputs α)

include i in
/-- The rate of the division modulus `M_n = D_{6n}² 2^{⌊kn⌋}` is `σ(k) = 12 + k log 2`. -/
theorem rate_M_NC {k : ℝ} (hk : 0 ≤ k) :
    LogRate (fun n : ℕ => (((Sfac n : ℤ) * (2 : ℤ) ^ (TexpNC k n) : ℤ) : ℝ)) (sigmaNC k) := by
  have h := (i.rate_Sfac).mul (rate_pow_two_TexpNC hk)
    (Eventually.of_forall (fun n => Sfac_ne_zero n))
    (Eventually.of_forall (fun n => by positivity))
  have hval : (12 : ℝ) + k * Real.log 2 = sigmaNC k := by rw [sigmaNC]
  rw [hval] at h
  refine h.of_eq (fun n => ?_)
  push_cast
  ring

end BaseNoteInputs

/-- **The fixed-`k` near-critical theorem.**  For every modulus exponent `0 ≤ k < k_*` there is
an admissible approximation sequence to `α` of worthiness at least

`δ(k) = (A_N - E_N) / (A_N - E_N + F(k))`. -/
theorem worthiness_nearcritical {α : ℝ} (i : BaseNoteInputs α) (N : NesterenkoInputs α)
    {k : ℝ} (hk0 : 0 ≤ k) (hk : k < kstarNC) :
    ∃ q p : ℕ → ℤ, IsAdmissible α q p ∧ ((deltaNC k : ℝ) : EReal) ≤ worthiness α q p := by
  have hk24 : k ≤ 24 := le_of_lt (lt_trans hk kstarNC_lt_24)
  have hX2ne : ∀ᶠ n in atTop, (((Sfac n : ℤ) * N.aRow n : ℤ) : ℝ) ≠ 0 :=
    LogRate.eventually_ne_zero (ne_of_gt ANrate_pos) N.rate_X
  have hl1ne : ∀ᶠ n in atTop,
      (((Sfac n : ℤ) * a2row n : ℤ) : ℝ) * α - ((y2row n : ℤ) : ℝ) ≠ 0 :=
    LogRate.eventually_ne_zero (ne_of_gt EZrate_pos) i.rate_l2
  have hdvd : ∀ n : ℕ,
      (2 : ℤ) ^ (TexpNC k n) ∣ a2row n * N.yRow n - N.aRow n * y2row n := by
    intro n
    exact dvd_trans (pow_dvd_pow 2 (TexpNC_le hk24 n)) (N.cross n)
  obtain ⟨d⟩ := lattice_selection α AZrate EZrate ANrate ENrate (sigmaNC k)
    a2row N.aRow y2row N.yRow
    (fun n => (Sfac n : ℤ)) (fun n => (2 : ℤ) ^ (TexpNC k n))
    (fun n => show (0:ℤ) < (Sfac n : ℤ) from Int.natCast_pos.mpr (Sfac_pos n))
    (fun n => by positivity)
    i.rate_X2 i.rate_l2 N.rate_X N.rate_l (i.rate_M_NC hk0)
    hdvd crossed_gap_NC hX2ne hl1ne
  have hH : ANrate - (sigmaNC k + ENrate - EZrate) / 2 = HrateNC k := by
    rw [HrateNC, DgapNC, FrateNC, sigmaNC]; ring
  have hF : (sigmaNC k + ENrate - EZrate) / 2 + EZrate - sigmaNC k = FrateNC k := by
    rw [FrateNC, sigmaNC]; ring
  rw [hH, hF] at d
  obtain ⟨q, p, hadm, hge⟩ :=
    worthiness_ge_of_balancedMinimaData (HrateNC_pos hk) (FrateNC_pos hk) d
  exact ⟨q, p, hadm, by rwa [← deltaNC_eq_one_sub hk] at hge⟩

/-- The explicit `k = 22` construction: worthiness at least `0.99`. -/
theorem worthiness_nearcritical_k22 {α : ℝ} (i : BaseNoteInputs α) (N : NesterenkoInputs α) :
    ∃ q p : ℕ → ℤ, IsAdmissible α q p ∧ ((0.99 : ℝ) : EReal) ≤ worthiness α q p := by
  obtain ⟨q, p, hadm, hge⟩ := worthiness_nearcritical i N (by norm_num) kstarNC_gt_22
  refine ⟨q, p, hadm, le_trans ?_ hge⟩
  exact_mod_cast EReal.coe_le_coe_iff.mpr deltaNC_22_gt.le

/-- **The near-critical theorem.**  For every `ε > 0` there is an explicit admissible
approximation sequence to `α` whose worthiness exceeds `1 - ε`. -/
theorem worthiness_nearcritical_one_sub_eps {α : ℝ} (i : BaseNoteInputs α)
    (N : NesterenkoInputs α) {ε : ℝ} (hε : 0 < ε) :
    ∃ q p : ℕ → ℤ, IsAdmissible α q p ∧ ((1 - ε : ℝ) : EReal) < worthiness α q p := by
  obtain ⟨k, hk0, hk, hgt⟩ := exists_k_deltaNC_gt_one_sub hε
  obtain ⟨q, p, hadm, hge⟩ := worthiness_nearcritical i N hk0 hk
  refine ⟨q, p, hadm, lt_of_lt_of_le ?_ hge⟩
  exact_mod_cast EReal.coe_lt_coe_iff.mpr hgt

/-! ### The theorems for Catalan's constant -/

/-- The fixed-`k` near-critical theorem for Catalan's constant.  Besides the imported
Nesterenko package, the only hypothesis is the prime number theorem `rate_D`. -/
theorem catalan_worthiness_nearcritical (N : NesterenkoInputs catalanReal)
    (rate_D : LogRate (fun N => ((Dlcm N : ℕ) : ℝ)) 1)
    {k : ℝ} (hk0 : 0 ≤ k) (hk : k < kstarNC) :
    ∃ q p : ℕ → ℤ, IsAdmissible catalanReal q p ∧
      ((deltaNC k : ℝ) : EReal) ≤ worthiness catalanReal q p :=
  worthiness_nearcritical
    ⟨GEreal_eq_catalanReal.symm, GZreal_eq_catalanReal.symm, rate_D⟩ N hk0 hk

/-- The `k = 22` construction for Catalan's constant: worthiness at least `0.99`. -/
theorem catalan_worthiness_k22 (N : NesterenkoInputs catalanReal)
    (rate_D : LogRate (fun N => ((Dlcm N : ℕ) : ℝ)) 1) :
    ∃ q p : ℕ → ℤ, IsAdmissible catalanReal q p ∧
      ((0.99 : ℝ) : EReal) ≤ worthiness catalanReal q p :=
  worthiness_nearcritical_k22
    ⟨GEreal_eq_catalanReal.symm, GZreal_eq_catalanReal.symm, rate_D⟩ N

/-- **`1 - ε` worthiness for Catalan's constant.**  For every `ε > 0` there is an admissible
sequence of rational approximations to Catalan's constant whose worthiness exceeds `1 - ε`. -/
theorem catalan_worthiness_one_sub_eps (N : NesterenkoInputs catalanReal)
    (rate_D : LogRate (fun N => ((Dlcm N : ℕ) : ℝ)) 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ q p : ℕ → ℤ, IsAdmissible catalanReal q p ∧
      ((1 - ε : ℝ) : EReal) < worthiness catalanReal q p :=
  worthiness_nearcritical_one_sub_eps
    ⟨GEreal_eq_catalanReal.symm, GZreal_eq_catalanReal.symm, rate_D⟩ N hε

/-- **`1 - ε` worthiness for Catalan's constant, from the `2`-adic Nesterenko package.**  Here
the cross-determinant divisibility is *proved* (Sections 17–20) rather than assumed: what is
imported is the `2`-adic Nesterenko data (`NesterenkoPadicInputs`), the two archimedean rates of
the Nesterenko row, and the prime number theorem. -/
theorem catalan_worthiness_one_sub_eps_of_padic (N : NesterenkoPadicInputs)
    (rate_X : LogRate (fun n : ℕ => (((Sfac n : ℤ) * N.aN n : ℤ) : ℝ)) ANrate)
    (rate_l : LogRate (fun n : ℕ => (((Sfac n : ℤ) * N.aN n : ℤ) : ℝ) * catalanReal
      - ((N.yN n : ℤ) : ℝ)) ENrate)
    (rate_D : LogRate (fun N => ((Dlcm N : ℕ) : ℝ)) 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ q p : ℕ → ℤ, IsAdmissible catalanReal q p ∧
      ((1 - ε : ℝ) : EReal) < worthiness catalanReal q p :=
  catalan_worthiness_one_sub_eps (NesterenkoInputs.ofPadic N rate_X rate_l) rate_D hε

/-- The same statement from the linear-form version of the imported package, in which the
`2`-adic input is the valuation `v₂(4 B_n 𝒢₂ - C_n) = 14n + 2 - s₂(n) - s₂(3n)` of the Nesterenko
linear form; the slope-`28` tail theorem is then derived. -/
theorem catalan_worthiness_one_sub_eps_of_form (N : NesterenkoFormInputs)
    (rate_X : LogRate (fun n : ℕ => (((Sfac n : ℤ) * N.aN n : ℤ) : ℝ)) ANrate)
    (rate_l : LogRate (fun n : ℕ => (((Sfac n : ℤ) * N.aN n : ℤ) : ℝ) * catalanReal
      - ((N.yN n : ℤ) : ℝ)) ENrate)
    (rate_D : LogRate (fun N => ((Dlcm N : ℕ) : ℝ)) 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ q p : ℕ → ℤ, IsAdmissible catalanReal q p ∧
      ((1 - ε : ℝ) : EReal) < worthiness catalanReal q p :=
  catalan_worthiness_one_sub_eps_of_padic N.toPadic rate_X rate_l rate_D hε

end Catalan
