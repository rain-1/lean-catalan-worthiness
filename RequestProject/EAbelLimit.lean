import RequestProject.EGenFun

/-!
# The limit of the modular row is Catalan's constant

This is the analytic half of Imported Theorem E: `2 B_n / A_n → G`.

The argument is an Abel-summation argument.  In the Legendre variable the two generating
functions are `F(w) = ∑_k C(2k,k)^2 w^k` and `Γ(w) = ∑_k C(2k,k)^2 c_k w^k`, and

* `F(w) → ∞` as `w → 1/16⁻`, because `C(2k,k)^2 16^{-k} ≥ 1/(4k+1)`;
* hence `Γ(w)/F(w) → lim_k c_k = G/2` (a weighted average with nonnegative weights whose total
  mass diverges);
* on the other hand `B_n = (G_E/2) A_n - ℓ_n` where the linear form `ℓ_n` is `O(poly · 4^n)`, so
  the generating function of `ℓ` is bounded near `x = 1/8` while that of `A` diverges there;
  hence `f_B(x)/f_A(x) → G_E/2`.

Since `f_B/f_A = Γ/F` under the substitution `w = x(1-4x)`, the two limits agree: `G_E = G`.
-/

namespace Catalan

open Filter Topology Finset Set

/-! ### The generating function of the linear forms is bounded near `1/8` -/

/-- The generating function of the modular linear forms `ℓ_n = (G_E/2) A_n - B_n`. -/
noncomputable def Lser (x : ℝ) : ℝ := ∑' n, (GEreal / 2 * aRe n - bRe n) * x ^ n

/-- The majorant of the coefficients of `Lser`. -/
noncomputable def LserBound : ℝ :=
  ∑' n : ℕ, 512 * geomPoly4 * (((n : ℝ) + 1) ^ 5 * (1 / 2 : ℝ) ^ n)

lemma summable_LserBound :
    Summable (fun n : ℕ => 512 * geomPoly4 * (((n : ℝ) + 1) ^ 5 * (1 / 2 : ℝ) ^ n)) :=
  (summable_succ_pow_mul_geometric 5 (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left _

lemma linE_pow_le {x : ℝ} (hx : |x| ≤ 1 / 8) (n : ℕ) :
    |(GEreal / 2 * aRe n - bRe n) * x ^ n|
      ≤ 512 * geomPoly4 * (((n : ℝ) + 1) ^ 5 * (1 / 2 : ℝ) ^ n) := by
  rw [abs_mul, abs_pow]
  have h1 := linE_abs_le n
  have h2 : |x| ^ n ≤ (1 / 8 : ℝ) ^ n := pow_le_pow_left₀ (abs_nonneg x) hx n
  have hK := geomPoly4_pos
  calc |GEreal / 2 * aRe n - bRe n| * |x| ^ n
      ≤ (512 * geomPoly4 * ((n : ℝ) + 1) ^ 5 * 4 ^ n) * (1 / 8 : ℝ) ^ n :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 512 * geomPoly4 * (((n : ℝ) + 1) ^ 5 * (1 / 2 : ℝ) ^ n) := by
        rw [show ((1:ℝ) / 2) ^ n = 4 ^ n * (1 / 8 : ℝ) ^ n by rw [← mul_pow]; norm_num]
        ring

lemma summable_linE_pow {x : ℝ} (hx : |x| ≤ 1 / 8) :
    Summable (fun n => |(GEreal / 2 * aRe n - bRe n) * x ^ n|) :=
  Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (linE_pow_le hx) summable_LserBound

/-- The generating function of the linear forms is bounded on `[-1/8, 1/8]`. -/
lemma Lser_abs_le {x : ℝ} (hx : |x| ≤ 1 / 8) : |Lser x| ≤ LserBound := by
  have hs := summable_linE_pow hx
  have h1 : |Lser x| ≤ ∑' n, |(GEreal / 2 * aRe n - bRe n) * x ^ n| := by
    rw [Lser]
    have := norm_tsum_le_tsum_norm (f := fun n => (GEreal / 2 * aRe n - bRe n) * x ^ n)
      (by simpa [Real.norm_eq_abs] using hs)
    simpa [Real.norm_eq_abs] using this
  exact h1.trans (hs.tsum_le_tsum (linE_pow_le hx) summable_LserBound)

/-- `f_B = (G_E/2) f_A - L` on the interval of convergence. -/
lemma fB_eq_sub {x : ℝ} (hx : |x| < 1 / 8) : fB x = GEreal / 2 * fA x - Lser x := by
  have hA : Summable (fun n => aRe n * x ^ n) := by
    have h := summable_aRe_pow |x| (abs_nonneg x) hx
    refine Summable.of_norm (h.congr (fun n => ?_))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow]
  have hB : Summable (fun n => bRe n * x ^ n) := by
    have h := summable_bRe_pow |x| (abs_nonneg x) hx
    refine Summable.of_norm (h.congr (fun n => ?_))
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_pow]
  have hL : Summable (fun n => (GEreal / 2 * aRe n - bRe n) * x ^ n) :=
    (summable_linE_pow hx.le).of_abs
  have : Lser x = GEreal / 2 * fA x - fB x := by
    rw [Lser, fA, fB, ← tsum_mul_left]
    rw [← (hA.mul_left (GEreal / 2)).tsum_sub hB]
    exact tsum_congr (fun n => by ring)
  rw [this]; ring

/-! ### `F(w) → ∞` -/

lemma abin_ge (k : ℕ) : (1 : ℝ) / (4 * k + 1) ≤ abin k * (1 / 16) ^ k := by
  have h := sixteen_pow_le_centralBinom_sq k
  have hpos : (0 : ℝ) < 4 * k + 1 := by positivity
  have h16 : (0 : ℝ) < (16 : ℝ) ^ k := by positivity
  rw [div_le_iff₀ hpos]
  rw [abin, show ((1 : ℝ) / 16) ^ k = ((16 : ℝ) ^ k)⁻¹ by rw [div_pow]; simp]
  rw [inv_eq_one_div, mul_one_div, div_mul_eq_mul_div, le_div_iff₀ h16]
  linarith [h]

lemma tendsto_partial_abin :
    Tendsto (fun K => ∑ k ∈ range K, abin k * (1 / 16 : ℝ) ^ k) atTop atTop := by
  have hns : ¬ Summable (fun k : ℕ => (1 : ℝ) / (4 * k + 1)) := by
    intro hsum
    have h1 : Summable (fun k : ℕ => (1 : ℝ) / (4 * (k + 1))) := by
      refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_) hsum
      have : (0 : ℝ) < 4 * (k : ℝ) + 1 := by positivity
      rw [div_le_div_iff₀ (by positivity) this]
      linarith
    have h2 : Summable (fun k : ℕ => (1 : ℝ) / ((k : ℝ) + 1)) := by
      have := h1.mul_left 4
      refine this.congr (fun k => ?_)
      field_simp
    have h3 : Summable (fun k : ℕ => (1 : ℝ) / (k : ℝ)) := by
      rw [← summable_nat_add_iff 1]
      refine h2.congr (fun k => ?_)
      push_cast
      ring_nf
    exact Real.not_summable_one_div_natCast h3
  have hdiv : Tendsto (fun K => ∑ k ∈ range K, (1 : ℝ) / (4 * k + 1)) atTop atTop := by
    rw [← not_summable_iff_tendsto_nat_atTop_of_nonneg (fun k => by positivity)]
    exact hns
  refine tendsto_atTop_mono (fun K => ?_) hdiv
  exact Finset.sum_le_sum (fun k _ => abin_ge k)

lemma Fser_ge_partial {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 1 / 16) (K : ℕ) :
    ∑ k ∈ range K, abin k * w ^ k ≤ Fgen w := by
  have hsum : Summable (fun k => abin k * w ^ k) :=
    summable_abin_pow w (by rw [abs_of_nonneg hw0]; exact hw)
  exact hsum.sum_le_tsum _ (fun k _ => mul_nonneg (abin_pos k).le (pow_nonneg hw0 k))

lemma Fser_pos {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 1 / 16) : 0 < Fgen w := by
  have h := Fser_ge_partial hw0 hw 1
  have h0 : ∑ k ∈ range 1, abin k * w ^ k = 1 := by
    simp [abin, Nat.centralBinom]
  linarith [h0 ▸ h]

/-- `F(w) → ∞` as `w → 1/16⁻`. -/
theorem tendsto_Fser_atTop :
    Tendsto Fgen (𝓝[Ico (0 : ℝ) (1 / 16)] (1 / 16)) atTop := by
  rw [tendsto_atTop]
  intro M
  obtain ⟨K, hK⟩ := (tendsto_atTop.mp tendsto_partial_abin (M + 1)).exists
  have hcont : ContinuousAt (fun w : ℝ => ∑ k ∈ range K, abin k * w ^ k) (1 / 16) :=
    (continuous_finset_sum (range K)
      (fun k _ => continuous_const.mul (continuous_pow k))).continuousAt
  have hev : ∀ᶠ w in 𝓝[Ico (0 : ℝ) (1 / 16)] (1 / 16),
      M ≤ ∑ k ∈ range K, abin k * w ^ k := by
    have h1 : Tendsto (fun w : ℝ => ∑ k ∈ range K, abin k * w ^ k)
        (𝓝[Ico (0 : ℝ) (1 / 16)] (1 / 16)) (𝓝 (∑ k ∈ range K, abin k * (1 / 16 : ℝ) ^ k)) :=
      hcont.continuousWithinAt.tendsto
    have h2 : M < ∑ k ∈ range K, abin k * (1 / 16 : ℝ) ^ k := by linarith
    exact (h1.eventually (eventually_gt_nhds h2)).mono (fun w hw => hw.le)
  filter_upwards [hev, self_mem_nhdsWithin] with w hw hmem
  exact hw.trans (Fser_ge_partial hmem.1 hmem.2 K)

/-! ### `Γ(w)/F(w) → G/2` -/

/-- The error series `E(w) = ∑_k C(2k,k)^2 (G/2 - c_k) w^k`. -/
noncomputable def Eser (w : ℝ) : ℝ := ∑' k, (abin k * (catalanReal / 2 - cRe k)) * w ^ k

lemma summable_Eser {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 1 / 16) :
    Summable (fun k => (abin k * (catalanReal / 2 - cRe k)) * w ^ k) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (mul_nonneg (abin_pos k).le
      (by linarith [cRe_le k])) (pow_nonneg hw0 k)) (fun k => ?_)
    (summable_abin_pow w (by rw [abs_of_nonneg hw0]; exact hw) |>.mul_left (catalanReal / 2))
  have hkey : abin k * (catalanReal / 2 - cRe k) * w ^ k
      = catalanReal / 2 * (abin k * w ^ k) - abin k * cRe k * w ^ k := by ring
  have hnn : 0 ≤ abin k * cRe k * w ^ k :=
    mul_nonneg (mul_nonneg (abin_pos k).le (cRe_nonneg k)) (pow_nonneg hw0 k)
  linarith [hkey]

lemma Gser_eq {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 1 / 16) :
    Ggen w = catalanReal / 2 * Fgen w - Eser w := by
  have habs : |w| < 1 / 16 := by rwa [abs_of_nonneg hw0]
  have hF := summable_abin_pow w habs
  have hE := summable_Eser hw0 hw
  rw [Eser, Fgen, Ggen, ← tsum_mul_left, ← (hF.mul_left (catalanReal / 2)).tsum_sub hE]
  exact tsum_congr (fun k => by ring)

lemma Eser_nonneg {w : ℝ} (hw0 : 0 ≤ w) : 0 ≤ Eser w := by
  refine tsum_nonneg (fun k => ?_)
  have h1 : 0 ≤ catalanReal / 2 - cRe k := by linarith [cRe_le k]
  have := abin_pos k
  positivity

lemma Eser_le {w : ℝ} (hw0 : 0 ≤ w) (hw : w < 1 / 16) {K : ℕ} {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ k, K ≤ k → catalanReal / 2 - cRe k ≤ ε) :
    Eser w ≤ (∑ k ∈ range K, abin k * (catalanReal / 2) * (1 / 16 : ℝ) ^ k) + ε * Fgen w := by
  have habs : |w| < 1 / 16 := by rwa [abs_of_nonneg hw0]
  have hE := summable_Eser hw0 hw
  have hF := summable_abin_pow w habs
  rw [Eser, ← hE.sum_add_tsum_nat_add K]
  have hhead : ∑ k ∈ range K, (abin k * (catalanReal / 2 - cRe k)) * w ^ k
      ≤ ∑ k ∈ range K, abin k * (catalanReal / 2) * (1 / 16 : ℝ) ^ k := by
    refine Finset.sum_le_sum (fun k _ => ?_)
    have hb := abin_pos k
    have h1 : catalanReal / 2 - cRe k ≤ catalanReal / 2 := by linarith [cRe_nonneg k]
    have h2 : w ^ k ≤ (1 / 16 : ℝ) ^ k := pow_le_pow_left₀ hw0 hw.le k
    have h3 : (0 : ℝ) ≤ catalanReal / 2 - cRe k := by linarith [cRe_le k]
    have hnn : 0 ≤ abin k * cRe k * w ^ k :=
      mul_nonneg (mul_nonneg hb.le (cRe_nonneg k)) (pow_nonneg hw0 k)
    have hc0 : (0 : ℝ) ≤ catalanReal / 2 := le_trans (cRe_nonneg k) (cRe_le k)
    calc abin k * (catalanReal / 2 - cRe k) * w ^ k
        ≤ abin k * (catalanReal / 2) * w ^ k := by nlinarith
      _ ≤ abin k * (catalanReal / 2) * (1 / 16 : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
  have htail : ∑' k, (abin (k + K) * (catalanReal / 2 - cRe (k + K))) * w ^ (k + K)
      ≤ ε * Fgen w := by
    have hsum1 : Summable
        (fun k => (abin (k + K) * (catalanReal / 2 - cRe (k + K))) * w ^ (k + K)) :=
      (summable_nat_add_iff K).mpr hE
    have hsum2 : Summable (fun k => ε * (abin (k + K) * w ^ (k + K))) :=
      ((summable_nat_add_iff K).mpr hF).mul_left ε
    have hle : ∀ k, (abin (k + K) * (catalanReal / 2 - cRe (k + K))) * w ^ (k + K)
        ≤ ε * (abin (k + K) * w ^ (k + K)) := by
      intro k
      have hb := abin_pos (k + K)
      have h2 := hε (k + K) (Nat.le_add_left K k)
      have hw' : (0 : ℝ) ≤ w ^ (k + K) := pow_nonneg hw0 (k + K)
      calc (abin (k + K) * (catalanReal / 2 - cRe (k + K))) * w ^ (k + K)
          = (abin (k + K) * w ^ (k + K)) * (catalanReal / 2 - cRe (k + K)) := by ring
        _ ≤ (abin (k + K) * w ^ (k + K)) * ε :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hb.le hw')
        _ = ε * (abin (k + K) * w ^ (k + K)) := by ring
    refine (hsum1.tsum_le_tsum hle hsum2).trans ?_
    rw [tsum_mul_left]
    have : ∑' k, abin (k + K) * w ^ (k + K) ≤ Fgen w := by
      have hsplit := hF.sum_add_tsum_nat_add K
      have hhead0 : 0 ≤ ∑ k ∈ range K, abin k * w ^ k :=
        Finset.sum_nonneg (fun k _ => mul_nonneg (abin_pos k).le (pow_nonneg hw0 k))
      rw [Fgen, ← hsplit]
      linarith
    exact mul_le_mul_of_nonneg_left this hε0
  linarith

/-- `Γ(w)/F(w) → G/2` as `w → 1/16⁻`. -/
theorem tendsto_Gser_div_Fser :
    Tendsto (fun w => Ggen w / Fgen w) (𝓝[Ico (0 : ℝ) (1 / 16)] (1 / 16))
      (𝓝 (catalanReal / 2)) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  set ε := δ / 4 with hεdef
  have hε0 : 0 < ε := by positivity
  obtain ⟨K, hK⟩ : ∃ K, ∀ k, K ≤ k → catalanReal / 2 - cRe k ≤ ε := by
    have h := tendsto_cCoef
    rw [Metric.tendsto_atTop] at h
    obtain ⟨K, hK⟩ := h ε hε0
    exact ⟨K, fun k hk => by
      have := hK k hk
      rw [Real.dist_eq, abs_lt] at this
      have h2 : cRe k = ((cCoef k : ℚ) : ℝ) := rfl
      rw [h2]
      linarith [this.1]⟩
  set S := ∑ k ∈ range K, abin k * (catalanReal / 2) * (1 / 16 : ℝ) ^ k with hS
  have hSnn : 0 ≤ S := by
    refine Finset.sum_nonneg (fun k _ => ?_)
    have := abin_pos k
    have := cRe_nonneg k
    have := cRe_le k
    have hc : 0 ≤ catalanReal / 2 := le_trans (cRe_nonneg 0) (cRe_le 0)
    exact mul_nonneg (mul_nonneg (abin_pos k).le hc) (by positivity)
  have hbig : ∀ᶠ w in 𝓝[Ico (0 : ℝ) (1 / 16)] (1 / 16), S / ε < Fgen w :=
    tendsto_Fser_atTop.eventually_gt_atTop (S / ε)
  filter_upwards [hbig, self_mem_nhdsWithin] with w hw hmem
  obtain ⟨hw0, hw16⟩ := hmem
  have hFpos : 0 < Fgen w := Fser_pos hw0 hw16
  have hGe := Gser_eq hw0 hw16
  have hEnn := Eser_nonneg hw0
  have hEle := Eser_le hw0 hw16 hε0.le hK
  have hFne : Fgen w ≠ 0 := hFpos.ne'
  have hratio : Ggen w / Fgen w - catalanReal / 2 = -(Eser w / Fgen w) := by
    rw [hGe]
    field_simp
    ring
  rw [Real.dist_eq, hratio, abs_neg, abs_of_nonneg (div_nonneg hEnn hFpos.le)]
  have h1 : Eser w / Fgen w ≤ (S + ε * Fgen w) / Fgen w := by gcongr
  have hSlt : S < ε * Fgen w := by
    rw [div_lt_iff₀ hε0] at hw
    linarith [hw]
  have h2 : (S + ε * Fgen w) / Fgen w = S / Fgen w + ε := by field_simp
  have h3 : S / Fgen w < ε := by
    rw [div_lt_iff₀ hFpos]
    linarith [hSlt]
  have : Eser w / Fgen w < 2 * ε := by
    rw [h2] at h1
    linarith
  have hδε : 2 * ε < δ := by rw [hεdef]; linarith
  linarith

/-! ### The two limits of `f_B/f_A` -/

lemma tendsto_wsub :
    Tendsto (fun x : ℝ => x * (1 - 4 * x)) (𝓝[Ioo (0 : ℝ) (1 / 8)] (1 / 8))
      (𝓝[Ico (0 : ℝ) (1 / 16)] (1 / 16)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have hc : Continuous (fun x : ℝ => x * (1 - 4 * x)) :=
      continuous_id.mul (continuous_const.sub (continuous_const.mul continuous_id))
    have h := (hc.tendsto (1 / 8 : ℝ)).mono_left (nhdsWithin_le_nhds
      (s := Ioo (0 : ℝ) (1 / 8)) (a := (1 / 8 : ℝ)))
    have hval : (1 / 8 : ℝ) * (1 - 4 * (1 / 8)) = 1 / 16 := by norm_num
    rwa [hval] at h
  · filter_upwards [self_mem_nhdsWithin] with x hx
    obtain ⟨hx0, hx1⟩ := hx
    constructor
    · nlinarith
    · nlinarith [mul_pos (show (0:ℝ) < 1/8 - x by linarith) (show (0:ℝ) < 1/8 - x by linarith)]

theorem tendsto_fA_atTop :
    Tendsto fA (𝓝[Ioo (0 : ℝ) (1 / 8)] (1 / 8)) atTop := by
  have h := tendsto_Fser_atTop.comp tendsto_wsub
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ∈ Ioo (-(1 / 24) : ℝ) (1 / 8) := ⟨by linarith [hx.1], hx.2⟩
  exact (fA_eq_Fser hx').symm

theorem tendsto_ratio_catalan :
    Tendsto (fun x => fB x / fA x) (𝓝[Ioo (0 : ℝ) (1 / 8)] (1 / 8))
      (𝓝 (catalanReal / 2)) := by
  have h := tendsto_Gser_div_Fser.comp tendsto_wsub
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx' : x ∈ Ioo (-(1 / 24) : ℝ) (1 / 8) := ⟨by linarith [hx.1], hx.2⟩
  simp only [Function.comp]
  rw [← fA_eq_Fser hx', ← fB_eq_Gser hx']

theorem tendsto_ratio_GEreal :
    Tendsto (fun x => fB x / fA x) (𝓝[Ioo (0 : ℝ) (1 / 8)] (1 / 8)) (𝓝 (GEreal / 2)) := by
  have hL : Tendsto (fun x => Lser x / fA x) (𝓝[Ioo (0 : ℝ) (1 / 8)] (1 / 8)) (𝓝 0) := by
    have hcb : Tendsto (fun _ : ℝ => LserBound) (𝓝[Ioo (0 : ℝ) (1 / 8)] (1 / 8))
        (𝓝 LserBound) := tendsto_const_nhds
    refine squeeze_zero_norm' ?_ (hcb.div_atTop tendsto_fA_atTop)
    filter_upwards [self_mem_nhdsWithin] with x hx
    obtain ⟨hx0, hx1⟩ := hx
    have hxabs : |x| ≤ 1 / 8 := by rw [abs_of_pos hx0]; linarith
    have hFA : 0 < fA x := by
      have hx' : x ∈ Ioo (-(1 / 24) : ℝ) (1 / 8) := ⟨by linarith, hx1⟩
      rw [fA_eq_Fser hx']
      refine Fser_pos (by nlinarith) ?_
      nlinarith [mul_pos (show (0:ℝ) < 1/8 - x by linarith) (show (0:ℝ) < 1/8 - x by linarith)]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hFA]
    gcongr
    exact Lser_abs_le hxabs
  have hconst : Tendsto (fun _ : ℝ => GEreal / 2) (𝓝[Ioo (0 : ℝ) (1 / 8)] (1 / 8))
      (𝓝 (GEreal / 2)) := tendsto_const_nhds
  have := hconst.sub hL
  rw [sub_zero] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  obtain ⟨hx0, hx1⟩ := hx
  have hxabs : |x| < 1 / 8 := by rw [abs_of_pos hx0]; exact hx1
  have hFA : 0 < fA x := by
    have hx' : x ∈ Ioo (-(1 / 24) : ℝ) (1 / 8) := ⟨by linarith, hx1⟩
    rw [fA_eq_Fser hx']
    refine Fser_pos (by nlinarith) ?_
    nlinarith [mul_pos (show (0:ℝ) < 1/8 - x by linarith) (show (0:ℝ) < 1/8 - x by linarith)]
  rw [fB_eq_sub hxabs]
  field_simp

/-- **The analytic half of Imported Theorem E**: the limit of the modular row `2 B_n / A_n` is
Catalan's constant. -/
theorem GEreal_eq_catalanReal : GEreal = catalanReal := by
  have hne : (𝓝[Ioo (0 : ℝ) (1 / 8)] (1 / 8)).NeBot := by
    rw [← mem_closure_iff_nhdsWithin_neBot, closure_Ioo (by norm_num)]
    exact right_mem_Icc.mpr (by norm_num)
  have h := tendsto_nhds_unique tendsto_ratio_GEreal tendsto_ratio_catalan
  linarith [h]

end Catalan
