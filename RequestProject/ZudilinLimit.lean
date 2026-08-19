import RequestProject.LinearForms
import RequestProject.RivoalP
import RequestProject.PadeEstimate

/-!
# The Zudilin row converges to Catalan's constant

Rivoal's identity (4.9), proved in `RivoalP.lean`, says

`P_m / Q_m = σ_m + (-1)^m p_m(x_m) / (8 Q_m)`,

where `σ_m = ∑_{k<m} (-1)^k/(2k+1)²` are the partial sums of Catalan's series.  Here we show
that the correction term is `O(1/m²)`, so that the real limit `G_Z` of the Zudilin row is
Catalan's constant

`G = ∑_{k} (-1)^k/(2k+1)²`.

The size estimate is elementary.  At a point with `y = x² - x ≥ 0` Beukers' denominators
`q_n(x)` are `≥ 1` and increasing (`bq_one_le`, `bq_mono`), and the Casoratian
`p_{n+1}q_n - p_n q_{n+1} = 1/(n+1)²` telescopes to

`p_n(x)/q_n(x) = ∑_{r<n} 1/((r+1)² q_r(x) q_{r+1}(x)) ≤ 2/(1+y)`  (`bp_le`).

At the moving point `x_m = 1/2 - m` one has `1 + y = m² + 3/4`, so `|p_m(x_m)| ≤ 2Q_m/(m²+3/4)`.
-/

namespace Catalan

open Finset Filter Topology

/-! ### Positivity and monotonicity of `q_n(x)` for `y = x² - x ≥ 0` -/

/-- For `y = x² - x ≥ 0`, Beukers' denominators are `≥ 1` and increasing. -/
lemma bq_one_le_and_mono (x : ℚ) (hy : 0 ≤ x ^ 2 - x) (n : ℕ) :
    1 ≤ bq x n ∧ bq x n ≤ bq x (n + 1) := by
  induction n with
  | zero =>
      refine ⟨by simp, ?_⟩
      rw [bq_zero, bq_one]
      linarith
  | succ k ih =>
      obtain ⟨hk1, hkm⟩ := ih
      have hk1' : (1 : ℚ) ≤ bq x (k + 1) := le_trans hk1 hkm
      refine ⟨hk1', ?_⟩
      have hrec := bq_rec x k
      simp only [bL, bC, bR] at hrec
      have hL : (0 : ℚ) < ((k : ℚ) + 1 + 1) ^ 2 := by positivity
      have hkey : (((k : ℚ) + 1 + 1) ^ 2) * bq x (k + 2)
          ≥ (((k : ℚ) + 1 + 1) ^ 2) * bq x (k + 1) := by
        have hstep : (2 * ((k : ℚ) + 1) * (((k : ℚ) + 1) + 1) + 1 - x + x ^ 2) * bq x (k + 1)
            + (-(((k : ℚ) + 1) ^ 2)) * bq x k
            ≥ (((k : ℚ) + 1 + 1) ^ 2) * bq x (k + 1) := by
          have h1 : (((k : ℚ) + 1) ^ 2) * bq x k ≤ (((k : ℚ) + 1) ^ 2) * bq x (k + 1) := by
            have : (0 : ℚ) ≤ ((k : ℚ) + 1) ^ 2 := by positivity
            nlinarith [hkm]
          nlinarith [hy, hk1']
        push_cast at hrec ⊢
        linarith [hrec, hstep]
      exact le_of_mul_le_mul_left (by linarith [hkey]) hL

lemma bq_one_le (x : ℚ) (hy : 0 ≤ x ^ 2 - x) (n : ℕ) : 1 ≤ bq x n :=
  (bq_one_le_and_mono x hy n).1

lemma bq_pos (x : ℚ) (hy : 0 ≤ x ^ 2 - x) (n : ℕ) : 0 < bq x n :=
  lt_of_lt_of_le zero_lt_one (bq_one_le x hy n)

lemma bq_mono (x : ℚ) (hy : 0 ≤ x ^ 2 - x) : Monotone (bq x) := by
  refine monotone_nat_of_le_succ (fun n => ?_)
  exact (bq_one_le_and_mono x hy n).2

/-! ### The telescoping formula for `p_n/q_n` -/

/-- The Casoratian telescopes: `p_n/q_n = ∑_{r<n} 1/((r+1)² q_r q_{r+1})`. -/
lemma bp_div_bq_eq_sum (x : ℚ) (hy : 0 ≤ x ^ 2 - x) (n : ℕ) :
    bp x n / bq x n = ∑ r ∈ range n, 1 / (((r : ℚ) + 1) ^ 2 * bq x r * bq x (r + 1)) := by
  induction n with
  | zero => simp
  | succ k ih =>
      have h0 := (bq_pos x hy k).ne'
      have h1 := (bq_pos x hy (k + 1)).ne'
      have hk : (((k : ℚ) + 1) ^ 2) ≠ 0 := by positivity
      have hcas' : (bp x (k + 1) * bq x k - bp x k * bq x (k + 1)) * ((k : ℚ) + 1) ^ 2 = 1 := by
        rw [bp_bq_casoratian x k]
        field_simp
      rw [Finset.sum_range_succ, ← ih,
        div_add_div _ _ h0 (by positivity), div_eq_div_iff h1 (by positivity)]
      linear_combination (bq x k * bq x (k + 1)) * hcas'

/-- The telescoping sum is bounded by `2/(1+y)`. -/
lemma bp_div_bq_le (x : ℚ) (hy : 0 ≤ x ^ 2 - x) (n : ℕ) :
    bp x n / bq x n ≤ 2 / (1 + (x ^ 2 - x)) := by
  have hy1 : (0 : ℚ) < 1 + (x ^ 2 - x) := by linarith
  have hne : (1 + (x ^ 2 - x)) ≠ 0 := hy1.ne'
  have hq1 : bq x 1 = 1 + (x ^ 2 - x) := by rw [bq_one]; ring
  have hterm : ∀ r ∈ range n, 1 / (((r : ℚ) + 1) ^ 2 * bq x r * bq x (r + 1))
      ≤ (1 / (1 + (x ^ 2 - x))) * (1 / ((r : ℚ) + 1) ^ 2) := by
    intro r _
    have hqr : (1 : ℚ) ≤ bq x r := bq_one_le x hy r
    have hqr1 : (1 + (x ^ 2 - x)) ≤ bq x (r + 1) := by
      rw [← hq1]
      exact bq_mono x hy (by omega)
    have hrne : (((r : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    have hpos : (0 : ℚ) < ((r : ℚ) + 1) ^ 2 := by positivity
    have hmul : (1 + (x ^ 2 - x)) * 1 ≤ bq x (r + 1) * bq x r :=
      mul_le_mul hqr1 hqr zero_le_one (by linarith)
    have hle : ((r : ℚ) + 1) ^ 2 * (1 + (x ^ 2 - x))
        ≤ ((r : ℚ) + 1) ^ 2 * bq x r * bq x (r + 1) := by
      nlinarith [hmul, hpos]
    have h2 : 1 / (((r : ℚ) + 1) ^ 2 * bq x r * bq x (r + 1))
        ≤ 1 / (((r : ℚ) + 1) ^ 2 * (1 + (x ^ 2 - x))) :=
      one_div_le_one_div_of_le (by positivity) hle
    have h3 : 1 / (((r : ℚ) + 1) ^ 2 * (1 + (x ^ 2 - x)))
        = (1 / (1 + (x ^ 2 - x))) * (1 / ((r : ℚ) + 1) ^ 2) := by
      field_simp
    linarith [h2, h3.le, h3.ge]
  have hsum : ∑ r ∈ range n, 1 / (((r : ℚ) + 1) ^ 2 * bq x r * bq x (r + 1))
      ≤ ∑ r ∈ range n, (1 / (1 + (x ^ 2 - x))) * (1 / ((r : ℚ) + 1) ^ 2) :=
    Finset.sum_le_sum hterm
  have hbasel : ∀ N : ℕ, ∑ r ∈ range (N + 1), (1 : ℚ) / ((r : ℚ) + 1) ^ 2
      ≤ 2 - 1 / ((N : ℚ) + 1) := by
    intro N
    induction N with
    | zero => norm_num
    | succ K ihK =>
        rw [Finset.sum_range_succ]
        have hstep : (1 : ℚ) / (((K : ℚ) + 1) + 1) ^ 2
            ≤ 1 / ((K : ℚ) + 1) - 1 / ((K : ℚ) + 1 + 1) := by
          rw [div_sub_div _ _ (by positivity) (by positivity),
            div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [sq_nonneg ((K : ℚ) + 1)]
        push_cast at ihK ⊢
        linarith
  have hb : ∑ r ∈ range n, (1 / (1 + (x ^ 2 - x))) * (1 / ((r : ℚ) + 1) ^ 2)
      ≤ 2 / (1 + (x ^ 2 - x)) := by
    rw [← Finset.mul_sum]
    have hle : ∑ r ∈ range n, (1 : ℚ) / ((r : ℚ) + 1) ^ 2 ≤ 2 := by
      match n with
      | 0 => norm_num
      | (N + 1) =>
          have h := hbasel N
          have hpos : (0 : ℚ) < 1 / ((N : ℚ) + 1) := by positivity
          linarith
    have hinv : (0 : ℚ) < 1 / (1 + (x ^ 2 - x)) := by positivity
    calc (1 / (1 + (x ^ 2 - x))) * ∑ r ∈ range n, (1 : ℚ) / ((r : ℚ) + 1) ^ 2
        ≤ (1 / (1 + (x ^ 2 - x))) * 2 := by nlinarith
      _ = 2 / (1 + (x ^ 2 - x)) := by ring
  rw [bp_div_bq_eq_sum x hy n]
  linarith [hsum, hb]

/-- The numerator is nonnegative at a point with `y = x² - x ≥ 0`. -/
lemma bp_nonneg (x : ℚ) (hy : 0 ≤ x ^ 2 - x) (n : ℕ) : 0 ≤ bp x n := by
  have hq := bq_pos x hy n
  have h := bp_div_bq_eq_sum x hy n
  have hs : 0 ≤ ∑ r ∈ range n, 1 / (((r : ℚ) + 1) ^ 2 * bq x r * bq x (r + 1)) := by
    refine Finset.sum_nonneg (fun r _ => ?_)
    have h1 := bq_pos x hy r
    have h2 := bq_pos x hy (r + 1)
    positivity
  have hdiv : 0 ≤ bp x n / bq x n := by rw [h]; exact hs
  have heq : bp x n = (bp x n / bq x n) * bq x n := by field_simp
  rw [heq]
  exact mul_nonneg hdiv hq.le

/-- The key size estimate: `|p_n(x)| ≤ 2 q_n(x)/(1+y)` whenever `y = x² - x ≥ 0`. -/
lemma abs_bp_le (x : ℚ) (hy : 0 ≤ x ^ 2 - x) (n : ℕ) :
    |bp x n| ≤ 2 * bq x n / (1 + (x ^ 2 - x)) := by
  have hq := bq_pos x hy n
  have hy1 : (0 : ℚ) < 1 + (x ^ 2 - x) := by linarith
  have hnn := bp_nonneg x hy n
  rw [abs_of_nonneg hnn]
  have h := bp_div_bq_le x hy n
  rw [div_le_div_iff₀ hq hy1] at h
  rw [le_div_iff₀ hy1]
  linarith


/-! ### The Zudilin row converges to Catalan's constant -/

/-- The diagonal estimate: `|p_m(x_m)| ≤ 2 Q_m/(m² + 3/4)` for `m ≥ 1`. -/
lemma abs_bp_xpt_le (m : ℕ) (hm : 1 ≤ m) :
    |bp (xpt m) m| ≤ 2 * Qz m / ((m : ℚ) ^ 2 + 3 / 4) := by
  have hy : (xpt m) ^ 2 - xpt m = (m : ℚ) ^ 2 - 1 / 4 := by
    unfold xpt
    ring
  have hm1 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have hynn : 0 ≤ (xpt m) ^ 2 - xpt m := by
    rw [hy]
    nlinarith
  have h := abs_bp_le (xpt m) hynn m
  rw [hy, bq_xpt_eq_Qz m] at h
  calc |bp (xpt m) m| ≤ 2 * Qz m / (1 + ((m : ℚ) ^ 2 - 1 / 4)) := h
    _ = 2 * Qz m / ((m : ℚ) ^ 2 + 3 / 4) := by ring_nf

/-- Catalan's constant `G = ∑_k (-1)^k/(2k+1)²`. -/
noncomputable def catalanReal : ℝ := ∑' k : ℕ, (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1) ^ 2

lemma summable_catalan_series :
    Summable (fun k : ℕ => (-1 : ℝ) ^ k / (2 * (k : ℝ) + 1) ^ 2) := by
  have hbase : Summable (fun k : ℕ => 1 / ((k : ℝ) + 1) ^ 2) := by
    simpa using (summable_nat_add_iff (f := fun k : ℕ => 1 / ((k : ℝ)) ^ 2) 1).2
      (Real.summable_one_div_nat_pow.mpr one_lt_two)
  refine hbase.of_norm_bounded (fun k => ?_)
  have h1 : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
  have h2 : ((k : ℝ) + 1) ^ 2 ≤ (2 * (k : ℝ) + 1) ^ 2 := by
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith
  rw [Real.norm_eq_abs, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_pos (show (0 : ℝ) < (2 * (k : ℝ) + 1) ^ 2 by positivity)]
  exact one_div_le_one_div_of_le h1 h2

lemma tendsto_sigmaCat :
    Tendsto (fun m : ℕ => ((sigmaCat m : ℚ) : ℝ)) atTop (𝓝 catalanReal) := by
  have h := summable_catalan_series.hasSum.tendsto_sum_nat
  refine h.congr (fun m => ?_)
  rw [sigmaCat]
  push_cast
  rfl

/-- The Zudilin row differs from the partial sums of Catalan's series by `O(1/m)`. -/
lemma abs_ratZ_sub_sigmaCat (m : ℕ) (hm : 1 ≤ m) :
    |pR m / qR m - ((sigmaCat m : ℚ) : ℝ)| ≤ 1 / ((m : ℝ) + 1) := by
  have hQ : Qz m ≠ 0 := Qz_ne_zero m
  have hm1 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  have hQpos : (0 : ℚ) < Qz m := by
    have h := bq_pos (xpt m) (by
      have : (xpt m) ^ 2 - xpt m = (m : ℚ) ^ 2 - 1 / 4 := by unfold xpt; ring
      rw [this]; nlinarith) m
    rwa [bq_xpt_eq_Qz m] at h
  have hriv := rivoal_numerator m
  have hdiff : Pz m / Qz m - sigmaCat m = (-1 : ℚ) ^ m / 8 * bp (xpt m) m / Qz m := by
    rw [hriv]
    field_simp
    ring
  have habs : |Pz m / Qz m - sigmaCat m| ≤ 1 / ((m : ℚ) + 1) := by
    rw [hdiff, abs_div, abs_of_pos hQpos, abs_mul, abs_div, abs_pow, abs_neg, abs_one, one_pow]
    have hb := abs_bp_xpt_le m hm
    have hpos : (0 : ℚ) < (m : ℚ) ^ 2 + 3 / 4 := by positivity
    rw [div_le_div_iff₀ hQpos (by positivity)]
    have hstep : (1 / |(8 : ℚ)| * |bp (xpt m) m|) * ((m : ℚ) + 1)
        ≤ (2 * Qz m / ((m : ℚ) ^ 2 + 3 / 4)) / 8 * ((m : ℚ) + 1) := by
      have h8 : |(8 : ℚ)| = 8 := by norm_num
      rw [h8]
      have : (0 : ℚ) < (m : ℚ) + 1 := by positivity
      nlinarith [hb]
    have hfin : (2 * Qz m / ((m : ℚ) ^ 2 + 3 / 4)) / 8 * ((m : ℚ) + 1) ≤ 1 * Qz m := by
      rw [div_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hQpos.le
        (show (0 : ℚ) ≤ 8 * (m : ℚ) ^ 2 + 6 - 2 * ((m : ℚ) + 1) by nlinarith)]
    linarith [hstep, hfin]
  have hcast : pR m / qR m - ((sigmaCat m : ℚ) : ℝ) = ((Pz m / Qz m - sigmaCat m : ℚ) : ℝ) := by
    unfold pR qR
    push_cast
    ring
  rw [hcast, ← Rat.cast_abs]
  have h1 : ((1 / ((m : ℚ) + 1) : ℚ) : ℝ) = 1 / ((m : ℝ) + 1) := by push_cast; ring
  rw [← h1]
  exact_mod_cast habs

/-- **The real limit of the Zudilin row is Catalan's constant.**  This is the analytic half of
Imported Theorem Z; with `RivoalP.lean` it is now proved rather than assumed. -/
theorem GZreal_eq_catalanReal : GZreal = catalanReal := by
  have hzero : Tendsto (fun m : ℕ => pR m / qR m - ((sigmaCat m : ℚ) : ℝ)) atTop (𝓝 0) := by
    rw [tendsto_zero_iff_abs_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall (fun m => abs_nonneg _))
      (Filter.eventually_atTop.2 ⟨1, fun m hm => abs_ratZ_sub_sigmaCat m hm⟩) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hsig : Tendsto (fun m : ℕ => ((sigmaCat m : ℚ) : ℝ)) atTop (𝓝 (GZreal - 0)) := by
    have := tendsto_ratZ.sub hzero
    refine this.congr (fun m => ?_)
    ring
  rw [sub_zero] at hsig
  exact tendsto_nhds_unique hsig tendsto_sigmaCat

end Catalan
