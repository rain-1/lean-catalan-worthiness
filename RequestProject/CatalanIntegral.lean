import RequestProject.CatalanBase

/-!
# The evaluation `∑_j 4^j/(C(2j,j)(2j+1)^2) = 2 G`

This file contains the analytic part of the accelerated series for Catalan's constant.

The chain of identities is:

* `uR n = ∫_0^1 (1-y^2)^n dy` (Wallis' integral, by the reduction formula for `∫ cos^{2n+1}`);
* the substitution `y = 2u/(1+u^2)` turns this into
  `uR n = ∫_0^1 2(1-u^2)/(1+u^2)^2 · ((1-u^2)/(1+u^2))^{2n} du`;
* dividing by `2n+1` and summing over `n` (all terms are nonnegative on `(0,1]`) the series
  `∑_n z^{2n+1}/(2n+1) = artanh z` at `z = (1-u^2)/(1+u^2)` gives
  `∑_n wR n = ∫_0^1 (-2 log u)/(1+u^2) du`;
* finally `∫_0^1 log u/(1+u^2) du = -G`, by expanding `1/(1+u^2)` in a geometric series and
  using `∫_0^1 u^{2k} log u du = -1/(2k+1)^2`.
-/

namespace Catalan

open Real MeasureTheory intervalIntegral Set Filter Topology Finset

/-! ### `∫_0^1 x^n log x dx = -1/(n+1)^2` -/

lemma intervalIntegrable_pow_mul_log (n : ℕ) :
    IntervalIntegrable (fun x : ℝ => x ^ n * Real.log x) volume 0 1 :=
  intervalIntegrable_log'.continuousOn_mul (by fun_prop)

lemma integral_pow_mul_log (n : ℕ) :
    (∫ x in (0 : ℝ)..1, x ^ n * Real.log x) = -1 / ((n : ℝ) + 1) ^ 2 := by
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hderiv : ∀ x ∈ Ioo (0 : ℝ) 1, HasDerivAt
      (fun t : ℝ => t ^ (n + 1) / ((n : ℝ) + 1) * Real.log t - t ^ (n + 1) / ((n : ℝ) + 1) ^ 2)
      (x ^ n * Real.log x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt hx.1
    have h1 : HasDerivAt (fun t : ℝ => t ^ (n + 1) / ((n : ℝ) + 1)) (x ^ n) x := by
      have h := (hasDerivAt_pow (n + 1) x).div_const ((n : ℝ) + 1)
      convert h using 1
      push_cast
      field_simp
    have h2 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx0
    have h4 : HasDerivAt (fun t : ℝ => t ^ (n + 1) / ((n : ℝ) + 1) ^ 2)
        (x ^ n / ((n : ℝ) + 1)) x := by
      have h := (hasDerivAt_pow (n + 1) x).div_const (((n : ℝ) + 1) ^ 2)
      convert h using 1
      push_cast
      field_simp
    have h5 := (h1.mul h2).sub h4
    convert h5 using 1
    field_simp
    ring
  have hzero : Tendsto
      (fun t : ℝ => t ^ (n + 1) / ((n : ℝ) + 1) * Real.log t - t ^ (n + 1) / ((n : ℝ) + 1) ^ 2)
      (𝓝[>] 0) (𝓝 0) := by
    have hr : Tendsto (fun x : ℝ => Real.log x * x ^ ((n : ℝ) + 1)) (𝓝[>] 0) (𝓝 0) :=
      tendsto_log_mul_rpow_nhdsGT_zero (by positivity)
    have hr' : Tendsto (fun x : ℝ => Real.log x * x ^ (n + 1)) (𝓝[>] 0) (𝓝 0) := by
      refine hr.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      rw [show ((n : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    have hp : Tendsto (fun x : ℝ => x ^ (n + 1)) (𝓝[>] 0) (𝓝 0) := by
      have hcp : Continuous (fun x : ℝ => x ^ (n + 1)) := by fun_prop
      have h := (hcp.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      simpa using h
    have hd := (hr'.div_const ((n : ℝ) + 1)).sub (hp.div_const (((n : ℝ) + 1) ^ 2))
    simp only [sub_zero, zero_div] at hd
    exact hd.congr (fun x => by ring)
  have hone : Tendsto
      (fun t : ℝ => t ^ (n + 1) / ((n : ℝ) + 1) * Real.log t - t ^ (n + 1) / ((n : ℝ) + 1) ^ 2)
      (𝓝[<] 1) (𝓝 (-1 / ((n : ℝ) + 1) ^ 2)) := by
    have hc : ContinuousAt
        (fun t : ℝ => t ^ (n + 1) / ((n : ℝ) + 1) * Real.log t - t ^ (n + 1) / ((n : ℝ) + 1) ^ 2)
        1 := by
      refine ContinuousAt.sub ?_ (continuousAt_pow _ _ |>.div_const _)
      exact (continuousAt_pow _ _ |>.div_const _).mul (Real.continuousAt_log (by norm_num))
    have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Iio (1 : ℝ)))
    have hval : (1 : ℝ) ^ (n + 1) / ((n : ℝ) + 1) * Real.log 1 - 1 ^ (n + 1) / ((n : ℝ) + 1) ^ 2
        = -1 / ((n : ℝ) + 1) ^ 2 := by
      rw [Real.log_one]
      ring
    rwa [hval] at h
  rw [integral_eq_sub_of_hasDerivAt_of_tendsto (by norm_num) hderiv
    (intervalIntegrable_pow_mul_log n) hzero hone]
  ring

/-! ### `∫_0^1 log x/(1+x^2) dx = -G` -/

/-- The `k`-th term of the expansion of `log x/(1+x^2)`. -/
noncomputable def logTerm (k : ℕ) (x : ℝ) : ℝ := (-1) ^ k * (x ^ (2 * k) * Real.log x)

lemma integrable_logTerm (k : ℕ) : Integrable (logTerm k) (volume.restrict (Ioc (0 : ℝ) 1)) := by
  have h := intervalIntegrable_pow_mul_log (2 * k)
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)] at h
  exact (h.const_mul ((-1) ^ k)).congr (by filter_upwards with x; rfl)

lemma integral_logTerm (k : ℕ) :
    ∫ x in Ioc (0 : ℝ) 1, logTerm k x = -((-1) ^ k / (2 * (k : ℝ) + 1) ^ 2) := by
  have h := integral_pow_mul_log (2 * k)
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
  unfold logTerm
  rw [MeasureTheory.integral_const_mul, h]
  push_cast
  ring

lemma integral_norm_logTerm (k : ℕ) :
    ∫ x in Ioc (0 : ℝ) 1, ‖logTerm k x‖ = 1 / (2 * (k : ℝ) + 1) ^ 2 := by
  have hae : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ‖logTerm k x‖ = -(x ^ (2 * k) * Real.log x) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    have hlog : Real.log x ≤ 0 := Real.log_nonpos hx.1.le hx.2
    have hp : (0 : ℝ) ≤ x ^ (2 * k) := pow_nonneg hx.1.le _
    rw [logTerm, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hp hlog)]
  rw [integral_congr_ae hae]
  have h := integral_pow_mul_log (2 * k)
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
  rw [MeasureTheory.integral_neg, h]
  push_cast
  ring

lemma summable_inv_odd_sq : Summable (fun k : ℕ => 1 / (2 * (k : ℝ) + 1) ^ 2) := by
  have hbase : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    simpa using (summable_nat_add_iff (f := fun k : ℕ => 1 / ((k : ℝ)) ^ 2) 1).2
      (Real.summable_one_div_nat_pow.mpr one_lt_two)
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hbase
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  apply one_div_le_one_div_of_le (by positivity)
  nlinarith

lemma tsum_logTerm {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1) :
    ∑' k, logTerm k x = Real.log x / (1 + x ^ 2) := by
  rcases eq_or_lt_of_le hx.2 with h1 | h1
  · subst h1
    simp [logTerm]
  · have hgeo : ∑' k : ℕ, (-x ^ 2) ^ k = (1 - (-x ^ 2))⁻¹ := by
      refine tsum_geometric_of_norm_lt_one ?_
      rw [Real.norm_eq_abs, abs_neg, abs_of_nonneg (sq_nonneg x)]
      nlinarith [hx.1]
    have hterm : ∀ k : ℕ, logTerm k x = (-x ^ 2) ^ k * Real.log x := by
      intro k
      have h2 : (-x ^ 2) ^ k = (-1) ^ k * x ^ (2 * k) := by rw [neg_pow, ← pow_mul]
      rw [logTerm, h2]
      ring
    rw [tsum_congr hterm, tsum_mul_right, hgeo, sub_neg_eq_add, div_eq_mul_inv]
    ring

lemma integral_log_div_one_add_sq :
    (∫ x in (0 : ℝ)..1, Real.log x / (1 + x ^ 2)) = -catalanReal := by
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hsum : Summable (fun k : ℕ => ∫ x in Ioc (0 : ℝ) 1, ‖logTerm k x‖) := by
    simpa only [integral_norm_logTerm] using summable_inv_odd_sq
  have hmain := integral_tsum_of_summable_integral_norm integrable_logTerm hsum
  have hae : ∀ᵐ x ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ∑' k, logTerm k x = Real.log x / (1 + x ^ 2) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    exact tsum_logTerm hx
  rw [integral_congr_ae hae] at hmain
  rw [← hmain]
  simp only [integral_logTerm]
  rw [tsum_neg]
  congr 1

/-! ### Wallis' integral -/

lemma integral_cos_pow_odd_half (n : ℕ) :
    (∫ x in (0 : ℝ)..(π / 2), Real.cos x ^ (2 * n + 1)) = uR n := by
  induction n with
  | zero => norm_num [uR, Nat.centralBinom]
  | succ n ih =>
      have h := integral_cos_pow (a := (0 : ℝ)) (b := π / 2) (n := 2 * n + 1)
      simp at h
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by ring, h, ih, uR_succ]
      have h3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
      field_simp
      ring

lemma integral_one_sub_sq_pow (n : ℕ) :
    (∫ y in (0 : ℝ)..1, (1 - y ^ 2) ^ n) = uR n := by
  have h := integral_sin_pow_mul_cos_pow_odd (a := (0 : ℝ)) (b := π / 2) 0 n
  simp at h
  rw [← h, integral_cos_pow_odd_half]

/-! ### The rational substitution `y = 2u/(1+u^2)` -/

lemma uR_eq_integral_rat (n : ℕ) :
    uR n = ∫ u in (0 : ℝ)..1,
      2 * (1 - u ^ 2) / (1 + u ^ 2) ^ 2 * ((1 - u ^ 2) / (1 + u ^ 2)) ^ (2 * n) := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun u : ℝ => 2 * u / (1 + u ^ 2))
      (2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2) x := by
    intro x _
    have hne : (1 + x ^ 2) ≠ 0 := by positivity
    have h1 : HasDerivAt (fun u : ℝ => 2 * u) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    have h2 : HasDerivAt (fun u : ℝ => 1 + u ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).const_add 1
    have h3 := h1.div h2 hne
    convert h3 using 1
    field_simp
    ring
  have hcont : ContinuousOn (fun x : ℝ => 2 * (1 - x ^ 2) / (1 + x ^ 2) ^ 2) (uIcc (0 : ℝ) 1) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro x _
    positivity
  have hg : Continuous (fun y : ℝ => (1 - y ^ 2) ^ n) := by fun_prop
  have hsub := intervalIntegral.integral_comp_smul_deriv hderiv hcont hg
  simp only [Function.comp, smul_eq_mul] at hsub
  norm_num at hsub
  have hpt : ∀ u : ℝ, 2 * (1 - u ^ 2) / (1 + u ^ 2) ^ 2 * ((1 - (2 * u / (1 + u ^ 2)) ^ 2) ^ n)
      = 2 * (1 - u ^ 2) / (1 + u ^ 2) ^ 2 * ((1 - u ^ 2) / (1 + u ^ 2)) ^ (2 * n) := by
    intro u
    have hne : (1 + u ^ 2) ≠ 0 := by positivity
    rw [pow_mul]
    congr 2
    field_simp
    ring
  simp only [hpt] at hsub
  rw [hsub, integral_one_sub_sq_pow]

/-! ### Summation -/

/-- The `j`-th integrand of the accelerated series. -/
noncomputable def wInt (j : ℕ) (u : ℝ) : ℝ :=
  2 * (1 - u ^ 2) / (1 + u ^ 2) ^ 2 * ((1 - u ^ 2) / (1 + u ^ 2)) ^ (2 * j) / (2 * (j : ℝ) + 1)

lemma continuous_wInt (j : ℕ) : Continuous (wInt j) := by
  unfold wInt
  refine Continuous.div_const (Continuous.mul ?_ ?_) _
  · exact Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)
  · exact (Continuous.div (by fun_prop) (by fun_prop) (fun x => by positivity)).pow _

lemma wInt_nonneg {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) (j : ℕ) : 0 ≤ wInt j u := by
  have h1 : (0 : ℝ) ≤ 1 - u ^ 2 := by nlinarith [hu.1, hu.2]
  have h2 : (0 : ℝ) < 1 + u ^ 2 := by positivity
  unfold wInt
  positivity

lemma integrable_wInt (j : ℕ) : Integrable (wInt j) (volume.restrict (Ioc (0 : ℝ) 1)) :=
  (continuous_wInt j).integrableOn_Ioc

lemma wR_eq_integral (j : ℕ) : wR j = ∫ u in Ioc (0 : ℝ) 1, wInt j u := by
  rw [wR_eq_uR_div, uR_eq_integral_rat j, ← intervalIntegral.integral_div,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rfl

lemma hasSum_wInt {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) :
    HasSum (fun j => wInt j u) (-2 * Real.log u / (1 + u ^ 2)) := by
  obtain ⟨hu0, hu1⟩ := hu
  have hden : (0 : ℝ) < 1 + u ^ 2 := by positivity
  set z : ℝ := (1 - u ^ 2) / (1 + u ^ 2) with hz
  have hznn : 0 ≤ z := by
    rw [hz]; exact div_nonneg (by nlinarith) hden.le
  have hzlt : z < 1 := by
    rw [hz, div_lt_one hden]; nlinarith
  have habs : |z| < 1 := by rw [abs_of_nonneg hznn]; exact hzlt
  have hs2 := (Real.hasSum_log_sub_log_of_abs_lt_one habs).mul_left (1 / (1 + u ^ 2))
  have hval : (1 / (1 + u ^ 2)) * (Real.log (1 + z) - Real.log (1 - z))
      = -2 * Real.log u / (1 + u ^ 2) := by
    have h1z : 1 + z = 2 / (1 + u ^ 2) := by rw [hz]; field_simp; ring
    have h2z : 1 - z = 2 * u ^ 2 / (1 + u ^ 2) := by rw [hz]; field_simp; ring
    rw [h1z, h2z, Real.log_div (by positivity) (by positivity),
      Real.log_div (by positivity) (by positivity), Real.log_mul (by norm_num) (by positivity),
      Real.log_pow]
    push_cast
    field_simp
    ring
  rw [hval] at hs2
  have hterm : ∀ k : ℕ, (1 / (1 + u ^ 2)) * (2 * (1 / (2 * (k : ℝ) + 1)) * z ^ (2 * k + 1))
      = wInt k u := by
    intro k
    have hzz : 2 * (1 - u ^ 2) / (1 + u ^ 2) ^ 2 = 2 * z / (1 + u ^ 2) := by
      rw [hz]; field_simp
    unfold wInt
    rw [← hz, hzz, pow_succ]
    field_simp
    ring
  have hfun : (fun k : ℕ => (1 / (1 + u ^ 2)) * (2 * (1 / (2 * (k : ℝ) + 1)) * z ^ (2 * k + 1)))
      = fun j => wInt j u := funext hterm
  rwa [hfun] at hs2

theorem tsum_wR : ∑' j, wR j = 2 * catalanReal := by
  have hnorm : ∀ j, ∫ u in Ioc (0 : ℝ) 1, ‖wInt j u‖ = wR j := by
    intro j
    rw [wR_eq_integral j]
    refine integral_congr_ae ((ae_restrict_iff' measurableSet_Ioc).2 ?_)
    filter_upwards with u hu
    exact Real.norm_of_nonneg (wInt_nonneg hu j)
  have hsum : Summable (fun j => ∫ u in Ioc (0 : ℝ) 1, ‖wInt j u‖) := by
    simpa only [hnorm] using summable_wR
  have hmain := integral_tsum_of_summable_integral_norm integrable_wInt hsum
  have hae : ∀ᵐ u ∂(volume.restrict (Ioc (0 : ℝ) 1)),
      ∑' j, wInt j u = -2 * Real.log u / (1 + u ^ 2) := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with u hu
    exact (hasSum_wInt hu).tsum_eq
  rw [integral_congr_ae hae] at hmain
  have hlhs : ∑' j, (∫ u in Ioc (0 : ℝ) 1, wInt j u) = ∑' j, wR j :=
    tsum_congr (fun j => (wR_eq_integral j).symm)
  rw [hlhs] at hmain
  rw [hmain]
  have h2 : ∀ u : ℝ, -2 * Real.log u / (1 + u ^ 2) = (-2) * (Real.log u / (1 + u ^ 2)) :=
    fun u => by ring
  simp only [h2]
  rw [MeasureTheory.integral_const_mul]
  have hint := integral_log_div_one_add_sq
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hint
  rw [hint]
  ring

end Catalan
