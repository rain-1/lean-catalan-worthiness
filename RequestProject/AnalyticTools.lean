import Mathlib

/-!
# Tools for power series on the real line

Two general facts used in `EGenFun.lean`:

* `analyticOnNhd_tsum_pow`: a real power series whose coefficients are summable against every
  smaller radius defines an analytic function on the ball of that radius;
* `tsum_pow_comp_quadratic`: the substitution `x ↦ x(1-4x)` may be performed term by term inside
  a power series, *provided* the resulting double family is absolutely summable (which happens
  for `|x|` small).  Together with the identity theorem this gives the substitution identity on
  the whole interval of convergence.
-/

namespace Catalan

open FormalMultilinearSeries ENNReal Finset

/-- A real power series is analytic on the open ball of any radius `r` for which the
coefficients are absolutely summable against `ρ ^ n` for all `ρ < r`. -/
theorem analyticOnNhd_tsum_pow (c : ℕ → ℝ) (r : ℝ) (hr : 0 < r)
    (hsum : ∀ ρ : ℝ, 0 ≤ ρ → ρ < r → Summable (fun n => ‖c n‖ * ρ ^ n)) :
    AnalyticOnNhd ℝ (fun x : ℝ => ∑' n, c n * x ^ n) (Metric.ball 0 r) := by
  set p := FormalMultilinearSeries.ofScalars ℝ c with hp
  have hrad : ENNReal.ofReal r ≤ p.radius := by
    refine le_of_forall_nnreal_lt (fun ρ hρ => ?_)
    have hρr : (ρ : ℝ) < r := by
      exact_mod_cast (ENNReal.lt_ofReal_iff_toReal_lt (by simp)).mp hρ
    refine FormalMultilinearSeries.le_radius_of_summable_norm p ?_
    simpa [hp, ofScalars_norm] using hsum ρ ρ.coe_nonneg hρr
  have hpos : 0 < p.radius := lt_of_lt_of_le (by simpa using ENNReal.ofReal_pos.mpr hr) hrad
  have hball := p.hasFPowerSeriesOnBall hpos
  have hAn : AnalyticOnNhd ℝ p.sum (Metric.eball (0 : ℝ) p.radius) := hball.analyticOnNhd
  intro x hx
  have hxb : x ∈ Metric.eball (0 : ℝ) p.radius := by
    rw [Metric.mem_eball, edist_dist]
    refine lt_of_lt_of_le ?_ hrad
    rw [Metric.mem_ball] at hx
    exact ENNReal.ofReal_lt_ofReal_iff_of_nonneg dist_nonneg |>.mpr hx
  refine (hAn x hxb).congr ?_
  filter_upwards with y
  simp [hp, FormalMultilinearSeries.sum, mul_comm]

/-- The coefficient sequence obtained from `c` by the substitution `x ↦ x (1 - 4x)`. -/
noncomputable def subCoef (c : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ range (n + 1), c k * ((-4 : ℝ) ^ (n - k) * (k.choose (n - k) : ℝ))

/-- Term-by-term substitution `x ↦ x(1-4x)`, valid where the double family is absolutely
summable. -/
theorem tsum_pow_comp_quadratic (c : ℕ → ℝ) (x : ℝ)
    (hs : Summable (fun k => |c k| * (|x| * (1 + 4 * |x|)) ^ k)) :
    ∑' k, c k * (x * (1 - 4 * x)) ^ k = ∑' n, subCoef c n * x ^ n := by
  set u : ℕ × ℕ → ℝ := fun p => c p.1 * (p.1.choose p.2 : ℝ) * (-4 : ℝ) ^ p.2 * x ^ (p.1 + p.2)
    with hu
  have hrow : ∀ k : ℕ, HasSum (fun m => u (k, m)) (c k * (x * (1 - 4 * x)) ^ k) := by
    intro k
    have hfin : ∀ m ∉ range (k + 1), u (k, m) = 0 := by
      intro m hm
      simp only [mem_range, not_lt] at hm
      have : k.choose m = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [hu, this]
    have hval : ∑ m ∈ range (k + 1), u (k, m) = c k * (x * (1 - 4 * x)) ^ k := by
      have h1 : ∑ m ∈ range (k + 1), u (k, m)
          = c k * x ^ k * ∑ m ∈ range (k + 1), (-4 * x) ^ m * 1 ^ (k - m) * (k.choose m : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m hm => ?_)
        have hxp : x ^ (k + m) = x ^ k * x ^ m := pow_add x k m
        simp only [hu, hxp, mul_pow, one_pow, mul_one]
        ring
      rw [h1, ← add_pow, show (-4 * x + 1 : ℝ) = 1 - 4 * x by ring, mul_pow]
      ring
    exact hval ▸ hasSum_sum_of_ne_finset_zero hfin
  have hrowabs : ∀ k : ℕ, HasSum (fun m => |u (k, m)|) (|c k| * (|x| * (1 + 4 * |x|)) ^ k) := by
    intro k
    have hfin : ∀ m ∉ range (k + 1), |u (k, m)| = 0 := by
      intro m hm
      simp only [mem_range, not_lt] at hm
      have : k.choose m = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [hu, this]
    have hval : ∑ m ∈ range (k + 1), |u (k, m)| = |c k| * (|x| * (1 + 4 * |x|)) ^ k := by
      have h1 : ∑ m ∈ range (k + 1), |u (k, m)|
          = |c k| * |x| ^ k
            * ∑ m ∈ range (k + 1), (4 * |x|) ^ m * 1 ^ (k - m) * (k.choose m : ℝ) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m hm => ?_)
        have hxp : x ^ (k + m) = x ^ k * x ^ m := pow_add x k m
        simp only [hu, hxp, abs_mul, abs_pow, mul_pow]
        rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ (k.choose m : ℝ)),
          show |(-4 : ℝ)| = 4 by norm_num]
        ring
      rw [h1, ← add_pow, show (4 * |x| + 1 : ℝ) = 1 + 4 * |x| by ring, mul_pow]
      ring
    exact hval ▸ hasSum_sum_of_ne_finset_zero hfin
  have habs : Summable (fun p : ℕ × ℕ => |u p|) := by
    rw [summable_prod_of_nonneg (fun p => abs_nonneg _)]
    exact ⟨fun k => (hrowabs k).summable, hs.congr (fun k => ((hrowabs k).tsum_eq).symm)⟩
  have hsum : Summable u := habs.of_abs
  have hL : ∑' p : ℕ × ℕ, u p = ∑' k, c k * (x * (1 - 4 * x)) ^ k := by
    rw [hsum.tsum_prod' (fun k => (hrow k).summable)]
    exact tsum_congr (fun k => (hrow k).tsum_eq)
  have hR : ∑' p : ℕ × ℕ, u p = ∑' n, subCoef c n * x ^ n := by
    have he := (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).tsum_eq u
    rw [← he]
    have hsig : Summable (fun s : Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n =>
        u (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd s)) :=
      (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd (A := ℕ)).summable_iff.mpr hsum
    rw [hsig.tsum_sigma]
    refine tsum_congr (fun n => ?_)
    rw [tsum_fintype]
    have hstep : ∀ b : (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)),
        u (Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd
          (⟨n, b⟩ : Σ n : ℕ, Finset.HasAntidiagonal.antidiagonal n))
          = u (b : ℕ × ℕ) := by
      intro b; simp [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd]
    rw [Finset.sum_congr rfl (fun b _ => hstep b)]
    rw [Finset.sum_coe_sort (Finset.HasAntidiagonal.antidiagonal n) (fun kl => u kl)]
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    rw [subCoef, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    simp only [mem_range] at hk
    have hkn : k + (n - k) = n := by omega
    simp only [hu, hkn]
    ring
  rw [← hL, hR]

/-- Polynomial times geometric is summable. -/
lemma summable_succ_pow_mul_geometric (d : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) :
    Summable (fun n : ℕ => ((n : ℝ) + 1) ^ d * r ^ n) := by
  rcases eq_or_lt_of_le hr0 with h0 | h0
  · refine summable_of_ne_finset_zero (s := {0}) (fun n hn => ?_)
    simp only [Finset.mem_singleton] at hn
    rw [← h0, zero_pow hn, mul_zero]
  · have h := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) d
      (r := r) (by rwa [Real.norm_eq_abs, abs_of_nonneg hr0])
    have h2 := (summable_nat_add_iff 1).mpr h
    have h3 := h2.mul_left r⁻¹
    refine h3.congr (fun n => ?_)
    push_cast
    field_simp
    ring

open Set Filter Topology in
/-- **The Legendre substitution identity.**  If `A n` is the `n`-th coefficient obtained from a
sequence `c` bounded by `16 ^ k` by the substitution `x ↦ x(1-4x)`, and the power series of `A`
converges on `(-1/8, 1/8)`, then the substitution identity holds on all of `(-1/24, 1/8)` — not
only near `0`, where it is the elementary rearrangement `tsum_pow_comp_quadratic`.  The passage
from a neighbourhood of `0` to the whole interval is the identity theorem for real analytic
functions. -/
theorem subst_identity (c : ℕ → ℝ) (A : ℕ → ℝ) (hA : ∀ n, A n = subCoef c n)
    (M : ℝ) (hc : ∀ k, |c k| ≤ M * 16 ^ k)
    (hAsum : ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 / 8 → Summable (fun n => ‖A n‖ * ρ ^ n))
    {x : ℝ} (hx : x ∈ Ioo (-(1 / 24) : ℝ) (1 / 8)) :
    ∑' n, A n * x ^ n = ∑' k, c k * (x * (1 - 4 * x)) ^ k := by
  have hcsum : ∀ ρ : ℝ, 0 ≤ ρ → ρ < 1 / 16 → Summable (fun k => ‖c k‖ * ρ ^ k) := by
    intro ρ hρ0 hρ
    refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
      ((summable_geometric_of_lt_one (by positivity)
        (show 16 * ρ < 1 by linarith)).mul_left M)
    calc ‖c k‖ * ρ ^ k ≤ (M * 16 ^ k) * ρ ^ k := by
          rw [Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right (hc k) (by positivity)
      _ = M * (16 * ρ) ^ k := by rw [mul_pow]; ring
  have hf : AnalyticOnNhd ℝ (fun x : ℝ => ∑' n, A n * x ^ n) (Metric.ball 0 (1 / 8)) :=
    analyticOnNhd_tsum_pow A (1 / 8) (by norm_num) hAsum
  have hg : AnalyticOnNhd ℝ (fun w : ℝ => ∑' k, c k * w ^ k) (Metric.ball 0 (1 / 16)) :=
    analyticOnNhd_tsum_pow c (1 / 16) (by norm_num) hcsum
  have hmap : ∀ y ∈ Ioo (-(1 / 24) : ℝ) (1 / 8),
      y * (1 - 4 * y) ∈ Metric.ball (0 : ℝ) (1 / 16) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor
    · nlinarith [mul_pos (show (0:ℝ) < y + 1/24 by linarith) (show (0:ℝ) < 1/8 - y by linarith)]
    · nlinarith [mul_pos (show (0:ℝ) < 1/8 - y by linarith) (show (0:ℝ) < 1/8 - y by linarith)]
  have hsub : Ioo (-(1 / 24) : ℝ) (1 / 8) ⊆ Metric.ball (0 : ℝ) (1 / 8) := by
    intro y hy
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]
    exact ⟨by linarith [hy.1], hy.2⟩
  have hh : AnalyticOnNhd ℝ (fun y : ℝ => ∑' k, c k * (y * (1 - 4 * y)) ^ k)
      (Ioo (-(1 / 24) : ℝ) (1 / 8)) := by
    intro y hy
    have hpoly : AnalyticAt ℝ (fun y : ℝ => y * (1 - 4 * y)) y :=
      analyticAt_id.mul (analyticAt_const.sub (analyticAt_const.mul analyticAt_id))
    have := AnalyticAt.comp (g := fun w : ℝ => ∑' k, c k * w ^ k)
      (f := fun y : ℝ => y * (1 - 4 * y)) (hg _ (hmap y hy)) hpoly
    change AnalyticAt ℝ
      ((fun w : ℝ => ∑' k, c k * w ^ k) ∘ fun y : ℝ => y * (1 - 4 * y)) y
    exact this
  have heq : (fun x : ℝ => ∑' n, A n * x ^ n)
      =ᶠ[𝓝 (0 : ℝ)] (fun y : ℝ => ∑' k, c k * (y * (1 - 4 * y)) ^ k) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (show (0:ℝ) < 1/32 by norm_num)] with y hy
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at hy
    have hyy : |y| * (1 + 4 * |y|) < 1 / 16 := by
      have h1 : (0:ℝ) ≤ |y| := abs_nonneg y
      nlinarith
    have hs : Summable (fun k => |c k| * (|y| * (1 + 4 * |y|)) ^ k) := by
      have := hcsum (|y| * (1 + 4 * |y|)) (by positivity) hyy
      exact this.congr (fun k => by rw [Real.norm_eq_abs])
    rw [tsum_pow_comp_quadratic c y hs]
    exact tsum_congr (fun n => by rw [hA n])
  exact ((hf.mono hsub).eqOn_of_preconnected_of_eventuallyEq hh isPreconnected_Ioo
    (show (0:ℝ) ∈ Ioo (-(1/24) : ℝ) (1/8) by constructor <;> norm_num) heq) hx

end Catalan
