import Mathlib

/-!
# Normalized logarithmic rates

A small toolkit for statements of the shape `log |f n| = a n + o(n)`, which is how all the
archimedean estimates of the two notes are phrased.  We write `LogRate f a` for

`(1/n) log |f n| → a`.

The three basic operations are: the rate of a product is the sum of the rates
(`LogRate.mul`), a constant has rate `0` (`LogRate.const`), and passing to the arithmetic
subsequence `n ↦ k n` multiplies the rate by `k` (`LogRate.comp_mul`).
-/

namespace Catalan

open Filter Topology

/-- `LogRate f a` means `log |f n| = a n + o(n)`, i.e. `(1/n) log |f n| → a`. -/
def LogRate (f : ℕ → ℝ) (a : ℝ) : Prop :=
  Tendsto (fun n : ℕ => Real.log |f n| / n) atTop (𝓝 a)

namespace LogRate

lemma congr_eventuallyEq {f g : ℕ → ℝ} {a : ℝ} (hf : LogRate f a)
    (h : ∀ᶠ n in atTop, f n = g n) : LogRate g a := by
  refine Filter.Tendsto.congr' ?_ hf
  filter_upwards [h] with n hn
  rw [hn]

lemma of_eq {f g : ℕ → ℝ} {a : ℝ} (hf : LogRate f a) (h : ∀ n, f n = g n) : LogRate g a :=
  hf.congr_eventuallyEq (Eventually.of_forall h)

/-- A sequence with a nonzero rate is eventually nonzero. -/
lemma eventually_ne_zero {f : ℕ → ℝ} {a : ℝ} (ha : a ≠ 0) (hf : LogRate f a) :
    ∀ᶠ n in atTop, f n ≠ 0 := by
  have h := hf.eventually (eventually_ne_nhds ha)
  filter_upwards [h] with n hn
  intro hfn
  apply hn
  rw [hfn]
  simp

/-- The rate of a product is the sum of the rates. -/
lemma mul {f g : ℕ → ℝ} {a b : ℝ} (hf : LogRate f a) (hg : LogRate g b)
    (hf0 : ∀ᶠ n in atTop, f n ≠ 0) (hg0 : ∀ᶠ n in atTop, g n ≠ 0) :
    LogRate (fun n => f n * g n) (a + b) := by
  refine (hf.add hg).congr' ?_
  filter_upwards [hf0, hg0] with n h1 h2
  rw [abs_mul, Real.log_mul (abs_ne_zero.mpr h1) (abs_ne_zero.mpr h2), add_div]

/-- A nonzero constant sequence has rate `0`. -/
lemma const (c : ℝ) : LogRate (fun _ => c) 0 :=
  tendsto_const_div_atTop_nhds_zero_nat (Real.log |c|)

/-- Passing to the subsequence `n ↦ k n` multiplies the rate by `k`. -/
lemma comp_mul {f : ℕ → ℝ} {a : ℝ} (k : ℕ) (hk : 0 < k) (hf : LogRate f a) :
    LogRate (fun n => f (k * n)) (k * a) := by
  have hktop : Tendsto (fun n : ℕ => k * n) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n hk) tendsto_id
  have hcomp : Tendsto (fun n : ℕ => Real.log |f (k * n)| / ((k * n : ℕ) : ℝ)) atTop (𝓝 a) :=
    hf.comp hktop
  have hmul : Tendsto (fun n : ℕ => (k : ℝ) * (Real.log |f (k * n)| / ((k * n : ℕ) : ℝ)))
      atTop (𝓝 ((k : ℝ) * a)) := hcomp.const_mul (k : ℝ)
  refine hmul.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hkR : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  push_cast
  field_simp

/-- Passing to absolute values does not change the rate. -/
lemma of_abs {f : ℕ → ℝ} {a : ℝ} (h : LogRate (fun n => |f n|) a) : LogRate f a := by
  unfold LogRate at h ⊢
  simpa [abs_abs] using h

/-- Passing to absolute values does not change the rate. -/
lemma to_abs {f : ℕ → ℝ} {a : ℝ} (h : LogRate f a) : LogRate (fun n => |f n|) a := by
  unfold LogRate at h ⊢
  simpa [abs_abs] using h

/-- The rate of the reciprocal is the negative rate. -/
lemma inv {f : ℕ → ℝ} {a : ℝ} (h : LogRate f a) : LogRate (fun n => (f n)⁻¹) (-a) := by
  unfold LogRate at h ⊢
  have := h.neg
  refine this.congr (fun n => ?_)
  rw [abs_inv, Real.log_inv, neg_div]

/-- Shifting the index does not change the rate. -/
lemma shift {f : ℕ → ℝ} {a : ℝ} (h : LogRate f a) : LogRate (fun n => f (n + 1)) a := by
  unfold LogRate at h ⊢
  have h1 : Tendsto (fun n : ℕ => Real.log |f (n + 1)| / ((n : ℝ) + 1)) atTop (𝓝 a) := by
    have hcomp := h.comp (tendsto_add_atTop_nat 1)
    refine hcomp.congr (fun n => ?_)
    simp [Function.comp]
  have h2 : Tendsto (fun n : ℕ => ((n : ℝ) + 1) / (n : ℝ)) atTop (𝓝 1) := by
    have h3 : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
      tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at h3
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hn' : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  have h4 := h1.mul h2
  rw [mul_one] at h4
  refine h4.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hn1 : ((n : ℝ) + 1) ≠ 0 := by positivity
  field_simp

/-- Two sequences that agree up to bounded multiplicative constants have the same rate. -/
lemma of_ratio_bounded {f g : ℕ → ℝ} {a c₁ c₂ : ℝ} (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hg : LogRate g a) (hgne : ∀ᶠ n in atTop, g n ≠ 0)
    (hlb : ∀ᶠ n in atTop, c₁ * |g n| ≤ |f n|)
    (hub : ∀ᶠ n in atTop, |f n| ≤ c₂ * |g n|) : LogRate f a := by
  have hlo : Tendsto (fun n : ℕ => Real.log c₁ / n + Real.log |g n| / n) atTop (𝓝 a) := by
    have h1 : Tendsto (fun n : ℕ => Real.log c₁ / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have := h1.add hg
    simpa using this
  have hhi : Tendsto (fun n : ℕ => Real.log c₂ / n + Real.log |g n| / n) atTop (𝓝 a) := by
    have h1 : Tendsto (fun n : ℕ => Real.log c₂ / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat _
    have := h1.add hg
    simpa using this
  unfold LogRate
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi ?_ ?_
  · filter_upwards [hlb, hgne, eventually_gt_atTop 0] with n h1 h2 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hgpos : 0 < |g n| := abs_pos.mpr h2
    have hfpos : 0 < |f n| := lt_of_lt_of_le (by positivity) h1
    have := Real.log_le_log (by positivity) h1
    rw [Real.log_mul hc₁.ne' hgpos.ne'] at this
    rw [← add_div, div_le_div_iff_of_pos_right hn0]
    linarith
  · filter_upwards [hub, hgne, hlb, eventually_gt_atTop 0] with n h1 h2 h3 hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hgpos : 0 < |g n| := abs_pos.mpr h2
    have hfpos : 0 < |f n| := lt_of_lt_of_le (by positivity) h3
    have := Real.log_le_log hfpos h1
    rw [Real.log_mul hc₂.ne' hgpos.ne'] at this
    rw [← add_div, div_le_div_iff_of_pos_right hn0]
    linarith

/-- The upper half of a logarithmic rate: `|f n| ≤ e^{(a+ε)n}` eventually. -/
lemma upper {f : ℕ → ℝ} {a : ℝ} (h : LogRate f a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, |f n| ≤ Real.exp ((a + ε) * n) := by
  have h1 : ∀ᶠ n : ℕ in atTop, Real.log |f n| / n < a + ε :=
    h.eventually_lt_const (by linarith)
  filter_upwards [h1, Filter.eventually_gt_atTop 0] with n hn hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hlog : Real.log |f n| < (a + ε) * n := by rwa [div_lt_iff₀ hnR] at hn
  rcases eq_or_ne (f n) 0 with h0 | h0
  · rw [h0, abs_zero]; positivity
  · have hpos : 0 < |f n| := abs_pos.mpr h0
    calc |f n| = Real.exp (Real.log |f n|) := (Real.exp_log hpos).symm
      _ ≤ Real.exp ((a + ε) * n) := Real.exp_le_exp.mpr hlog.le

/-- The lower half of a logarithmic rate: `e^{(a-ε)n} ≤ |f n|` eventually, for an eventually
nonvanishing sequence. -/
lemma lower {f : ℕ → ℝ} {a : ℝ} (h : LogRate f a) (hf0 : ∀ᶠ n in atTop, f n ≠ 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Real.exp ((a - ε) * n) ≤ |f n| := by
  have h1 : ∀ᶠ n : ℕ in atTop, a - ε < Real.log |f n| / n :=
    h.eventually_const_lt (by linarith)
  filter_upwards [h1, hf0, Filter.eventually_gt_atTop 0] with n hn h0 hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hlog : (a - ε) * n < Real.log |f n| := by rwa [lt_div_iff₀ hnR] at hn
  have hpos : 0 < |f n| := abs_pos.mpr h0
  calc Real.exp ((a - ε) * n) ≤ Real.exp (Real.log |f n|) := Real.exp_le_exp.mpr hlog.le
    _ = |f n| := Real.exp_log hpos

end LogRate

/-- The one-sided version of `LogRate`: `|g n| ≤ e^{(b+ε)n}` eventually, for every `ε > 0`.
Unlike `LogRate` it is stable under products with no nonvanishing assumption. -/
def LogRateLE (g : ℕ → ℝ) (b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, |g n| ≤ Real.exp ((b + ε) * n)

lemma LogRate.toLE {g : ℕ → ℝ} {b : ℝ} (h : LogRate g b) : LogRateLE g b :=
  fun _ hε => h.upper hε

lemma LogRateLE.mul {f g : ℕ → ℝ} {a b : ℝ} (hf : LogRateLE f a) (hg : LogRateLE g b) :
    LogRateLE (fun n => f n * g n) (a + b) := by
  intro ε hε
  filter_upwards [hf (ε / 2) (by linarith), hg (ε / 2) (by linarith)] with n h1 h2
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  calc |f n * g n| = |f n| * |g n| := abs_mul _ _
    _ ≤ Real.exp ((a + ε / 2) * n) * Real.exp ((b + ε / 2) * n) := by
        have := abs_nonneg (f n)
        have := abs_nonneg (g n)
        have h3 := Real.exp_pos ((a + ε / 2) * n)
        nlinarith [h1, h2]
    _ = Real.exp ((a + b + ε) * n) := by rw [← Real.exp_add]; ring_nf

namespace LogRate

/-- **The dominant term determines the rate.**  If `f` has rate `a`, `g` has the strictly smaller
rate `b`, and `f` is eventually nonzero, then `f - g` is eventually nonzero and again has
rate `a`. -/
lemma sub_dominant {f g : ℕ → ℝ} {a b : ℝ} (hf : LogRate f a) (hg : LogRateLE g b)
    (hlt : b < a) (hf0 : ∀ᶠ n in atTop, f n ≠ 0) :
    LogRate (fun n => f n - g n) a ∧ ∀ᶠ n in atTop, f n - g n ≠ 0 := by
  set c : ℝ := (a - b) / 4 with hc
  have hcpos : 0 < c := by rw [hc]; linarith
  -- the ratio `g / f` tends to `0`
  have hratio : Tendsto (fun n : ℕ => g n / f n) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hsq : ∀ᶠ n : ℕ in atTop, ‖g n / f n‖ ≤ Real.exp ((b - a + 2 * c) * n) := by
      filter_upwards [hg c hcpos, hf.lower hf0 hcpos, hf0] with n h1 h2 h3
      have hfpos : 0 < |f n| := abs_pos.mpr h3
      rw [Real.norm_eq_abs, abs_div]
      rw [div_le_iff₀ hfpos]
      calc |g n| ≤ Real.exp ((b + c) * n) := h1
        _ = Real.exp ((b - a + 2 * c) * n) * Real.exp ((a - c) * n) := by
            rw [← Real.exp_add]; ring_nf
        _ ≤ Real.exp ((b - a + 2 * c) * n) * |f n| := by
            have := Real.exp_pos ((b - a + 2 * c) * n)
            nlinarith [h2]
    have hexp : Tendsto (fun n : ℕ => Real.exp ((b - a + 2 * c) * n)) atTop (𝓝 0) := by
      have hneg : b - a + 2 * c < 0 := by rw [hc]; linarith
      have : Tendsto (fun n : ℕ => (b - a + 2 * c) * n) atTop atBot :=
        Filter.Tendsto.const_mul_atTop_of_neg hneg tendsto_natCast_atTop_atTop
      exact Real.tendsto_exp_atBot.comp this
    refine squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _)) hsq hexp
  -- hence `1 - g/f` tends to `1`
  have hone : Tendsto (fun n : ℕ => 1 - g n / f n) atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub hratio
    simpa using this
  have hbound : ∀ᶠ n : ℕ in atTop, 1 / 2 ≤ |1 - g n / f n| ∧ |1 - g n / f n| ≤ 2 := by
    have h1 : ∀ᶠ n : ℕ in atTop, 1 / 2 < 1 - g n / f n := hone.eventually_const_lt (by norm_num)
    have h2 : ∀ᶠ n : ℕ in atTop, 1 - g n / f n < 2 := hone.eventually_lt_const (by norm_num)
    filter_upwards [h1, h2] with n ha hb
    constructor
    · rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  have hne : ∀ᶠ n : ℕ in atTop, f n - g n ≠ 0 := by
    filter_upwards [hbound, hf0] with n hb h0
    intro hz
    have hgf : 1 - g n / f n = 0 := by
      have hgn : g n = f n := by linarith [sub_eq_zero.mp hz]
      rw [hgn, div_self h0]; ring
    have h1 := hb.1
    rw [hgf, abs_zero] at h1
    linarith
  refine ⟨?_, hne⟩
  -- `log |f - g| = log |f| + log |1 - g/f|`, and the second term is `O(1)`
  have hsplit : ∀ᶠ n : ℕ in atTop,
      Real.log |f n - g n| / n = Real.log |f n| / n + Real.log |1 - g n / f n| / n := by
    filter_upwards [hbound, hf0] with n hb h0
    have hfac : f n - g n = f n * (1 - g n / f n) := by field_simp
    have hp1 : |f n| ≠ 0 := abs_ne_zero.mpr h0
    have hp2 : |1 - g n / f n| ≠ 0 := by
      intro h; rw [h] at hb; linarith [hb.1]
    rw [hfac, abs_mul, Real.log_mul hp1 hp2, add_div]
  have htail : Tendsto (fun n : ℕ => Real.log |1 - g n / f n| / n) atTop (𝓝 0) := by
    have hb : ∀ᶠ n : ℕ in atTop, |Real.log |1 - g n / f n| / n| ≤ Real.log 2 / n := by
      filter_upwards [hbound, Filter.eventually_gt_atTop 0] with n h hn0
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      have h1 : Real.log |1 - g n / f n| ≤ Real.log 2 :=
        Real.log_le_log (by linarith [h.1]) h.2
      have h2 : -Real.log 2 ≤ Real.log |1 - g n / f n| := by
        have := Real.log_le_log (by norm_num : (0:ℝ) < 1/2) h.1
        rw [show Real.log (1/2) = -Real.log 2 by
          rw [one_div, Real.log_inv]] at this
        exact this
      rw [abs_div, abs_of_pos hnR, div_le_div_iff_of_pos_right hnR]
      rw [abs_le]
      exact ⟨h2, h1⟩
    have hz : Tendsto (fun n : ℕ => Real.log 2 / n) atTop (𝓝 0) :=
      tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)
    refine squeeze_zero_norm' ?_ hz
    filter_upwards [hb] with n h
    rw [Real.norm_eq_abs]
    exact h
  have := hf.add htail
  rw [add_zero] at this
  exact this.congr' (hsplit.mono (fun n h => h.symm))

end LogRate

/-- An eventual statement survives restriction to the subsequence `n ↦ k n`. -/
lemma eventually_comp_mul {P : ℕ → Prop} (k : ℕ) (hk : 0 < k) (h : ∀ᶠ N in atTop, P N) :
    ∀ᶠ n in atTop, P (k * n) :=
  (tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_left n hk) tendsto_id).eventually h

lemma log_eight_eq : Real.log 8 = 3 * Real.log 2 := by
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
  push_cast
  ring

lemma log_four_eq : Real.log 4 = 2 * Real.log 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  push_cast
  ring

end Catalan
