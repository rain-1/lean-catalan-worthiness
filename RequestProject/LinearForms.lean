import RequestProject.ERate
import RequestProject.ZRatio

/-!
# The two rows converge, and the rates of their linear forms

Both rows of the note are Padé-type rows: their Wronskians are known exactly, so the
increments of the approximations `2B_n/A_n` and `P_m/Q_m` are known exactly as well.
Together with the growth rates of the denominators (`Catalan.rate_Ae`, `Catalan.rate_Qz`)
this gives, with no imported input:

* the two rows converge, to `Catalan.GEreal` and `Catalan.GZreal` respectively;
* `GEreal ≥ 1/2`, in particular the limit of the modular row is nonzero;
* the archimedean rates of the two linear forms, equations (9.3) and Imported Theorem Z:
  `(1/n) log |α A_n/2 - B_n| → log 4`  (`Catalan.rate_linE`) and
  `(1/m) log |Q_m α - P_m| → -5 log φ` (`Catalan.rate_linZ`).

The two limits are the ones the note calls `G`; that they are equal (both equal Catalan's
constant) is the one remaining archimedean input.
-/

namespace Catalan

open Filter Topology Finset

/-! ### Summability of polynomial multiples of a geometric series -/

lemma summable_poly_geom : Summable (fun k : ℕ => ((k : ℝ) + 1) ^ 4 * (1 / 2 : ℝ) ^ k) := by
  have h : Summable (fun k : ℕ => ((k : ℝ)) ^ 4 * (1 / 2 : ℝ) ^ k) :=
    summable_pow_mul_geometric_of_norm_lt_one 4 (by rw [norm_div]; norm_num)
  have h2 : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ)) ^ 4 * (1 / 2 : ℝ) ^ (k + 1)) :=
    (summable_nat_add_iff 1).mpr h
  have h3 := h2.mul_left 2
  refine h3.congr (fun k => ?_)
  push_cast
  ring

/-- `K = ∑_k (k+1)^4 2^{-k}`, the constant of the tail estimate for the modular row. -/
noncomputable def geomPoly4 : ℝ := ∑' k : ℕ, ((k : ℝ) + 1) ^ 4 * (1 / 2 : ℝ) ^ k

lemma geomPoly4_pos : 0 < geomPoly4 := by
  have hterm : ∀ k : ℕ, (0 : ℝ) ≤ ((k : ℝ) + 1) ^ 4 * (1 / 2 : ℝ) ^ k := by
    intro k; positivity
  have h0 : ((0 : ℝ) + 1) ^ 4 * (1 / 2 : ℝ) ^ 0 ≤ geomPoly4 := by
    have := summable_poly_geom.le_tsum 0 (fun i _ => hterm i)
    simpa [geomPoly4] using this
  norm_num at h0
  linarith [h0]

/-! ### The modular `E` row -/

/-- `A_n` as a real number. -/
noncomputable def aRe (n : ℕ) : ℝ := ((Ae n : ℚ) : ℝ)

/-- `B_n` as a real number. -/
noncomputable def bRe (n : ℕ) : ℝ := ((Be n : ℚ) : ℝ)

lemma aRe_pos (n : ℕ) : 0 < aRe n := by
  have h : Ae n = (eSum n : ℚ) := Ae_eq_eSum n
  have h2 : 0 < eSum n := eSum_pos n
  have : (0 : ℝ) < (eSum n : ℝ) := by exact_mod_cast h2
  simpa [aRe, h] using this

lemma aRe_ub (n : ℕ) : aRe n ≤ ((n : ℝ) + 1) * 8 ^ n := by
  have h : Ae n = (eSum n : ℚ) := Ae_eq_eSum n
  have h2 : (eSum n : ℝ) ≤ ((n : ℝ) + 1) * 8 ^ n := by
    have := eSum_le n
    have : ((eSum n : ℕ) : ℝ) ≤ (((n + 1) * 8 ^ n : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this
    linarith
  simpa [aRe, h] using h2

lemma aRe_lb (n : ℕ) : (8 : ℝ) ^ n / (16 * ((n : ℝ) + 1) ^ 3) ≤ aRe n := by
  have h : Ae n = (eSum n : ℚ) := Ae_eq_eSum n
  have h2 : ((8 : ℕ) ^ n : ℝ) ≤ ((16 * (n + 1) ^ 3 * eSum n : ℕ) : ℝ) := by
    exact_mod_cast eight_pow_le_eSum n
  push_cast at h2
  have hpos : (0 : ℝ) < 16 * ((n : ℝ) + 1) ^ 3 := by positivity
  rw [div_le_iff₀ hpos]
  have : ((eSum n : ℕ) : ℝ) = aRe n := by simp [aRe, h]
  rw [← this]
  linarith

/-- The increment of `2B_n/A_n`, an exact consequence of the Wronskian identity. -/
noncomputable def tE (n : ℕ) : ℝ :=
  2 * 32 ^ n / (((n : ℝ) + 1) ^ 2 * aRe n * aRe (n + 1))

lemma tE_pos (n : ℕ) : 0 < tE n := by
  have h1 := aRe_pos n
  have h2 := aRe_pos (n + 1)
  unfold tE
  positivity

lemma ratE_diff (n : ℕ) : 2 * bRe (n + 1) / aRe (n + 1) - 2 * bRe n / aRe n = tE n := by
  have hW : ((n : ℝ) + 1) ^ 2 * (aRe (n + 1) * bRe n - aRe n * bRe (n + 1)) = -(32 : ℝ) ^ n := by
    have h := WE_closed_form_mul n
    have h2 := congrArg (fun z : ℚ => (z : ℝ)) h
    simpa [WE, aRe, bRe] using h2
  have h1 := (aRe_pos n).ne'
  have h2 := (aRe_pos (n + 1)).ne'
  have h3 : ((n : ℝ) + 1) ^ 2 ≠ 0 := by positivity
  unfold tE
  field_simp
  nlinarith [hW]

lemma tE_le (n : ℕ) : tE n ≤ 64 * ((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 3 * (1 / 2 : ℝ) ^ n := by
  have hA := aRe_lb n
  have hA1 : (8 : ℝ) ^ (n + 1) / (16 * ((n : ℝ) + 2) ^ 3) ≤ aRe (n + 1) := by
    have := aRe_lb (n + 1)
    have hcast : (((n + 1 : ℕ) : ℝ) + 1) = ((n : ℝ) + 2) := by push_cast; ring
    rw [hcast] at this
    exact this
  have hApos := aRe_pos n
  have hA1pos := aRe_pos (n + 1)
  have hprod : (8 : ℝ) ^ n * 8 ^ (n + 1) / (16 * ((n : ℝ) + 1) ^ 3 * (16 * ((n : ℝ) + 2) ^ 3))
      ≤ aRe n * aRe (n + 1) := by
    have h1 : (0 : ℝ) < 16 * ((n : ℝ) + 1) ^ 3 := by positivity
    have h2 : (0 : ℝ) < 16 * ((n : ℝ) + 2) ^ 3 := by positivity
    have e1 : (8 : ℝ) ^ n / (16 * ((n : ℝ) + 1) ^ 3) * ((8 : ℝ) ^ (n + 1) / (16 * ((n : ℝ) + 2) ^ 3))
        = (8 : ℝ) ^ n * 8 ^ (n + 1) / (16 * ((n : ℝ) + 1) ^ 3 * (16 * ((n : ℝ) + 2) ^ 3)) := by
      field_simp
    rw [← e1]
    exact mul_le_mul hA hA1 (by positivity) hApos.le
  have hden : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 * aRe n * aRe (n + 1) := by positivity
  rw [tE, div_le_iff₀ hden]
  have hpow : (8 : ℝ) ^ n * 8 ^ (n + 1) = 8 * 64 ^ n := by
    rw [pow_succ]
    rw [show (64 : ℝ) = 8 * 8 by norm_num, mul_pow]
    ring
  have hkey : 2 * (32 : ℝ) ^ n ≤ 64 * ((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 3 * (1 / 2 : ℝ) ^ n
      * (((n : ℝ) + 1) ^ 2 * ((8 : ℝ) ^ n * 8 ^ (n + 1)
        / (16 * ((n : ℝ) + 1) ^ 3 * (16 * ((n : ℝ) + 2) ^ 3)))) := by
    rw [hpow]
    have h32 : (32 : ℝ) ^ n = (1 / 2 : ℝ) ^ n * 64 ^ n := by
      rw [← mul_pow]; norm_num
    rw [h32]
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((n : ℝ) + 2) ≠ 0 := by positivity
    apply le_of_eq
    field_simp
    ring
  refine le_trans hkey ?_
  have hc : (0 : ℝ) ≤ 64 * ((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 3 * (1 / 2 : ℝ) ^ n := by positivity
  have hsq : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by positivity
  have hfin := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod hsq) hc
  exact le_trans hfin (le_of_eq (by ring))

lemma summable_tE : Summable tE := by
  refine Summable.of_nonneg_of_le (fun n => (tE_pos n).le) (fun n => tE_le n) ?_
  have hmaj : ∀ n : ℕ, 64 * ((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 3 * (1 / 2 : ℝ) ^ n
      ≤ 1024 * (((n : ℝ) + 1) ^ 4 * (1 / 2 : ℝ) ^ n) := by
    intro n
    have h1 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have h2 : ((n : ℝ) + 2) ^ 3 ≤ (2 * ((n : ℝ) + 1)) ^ 3 := by
      apply pow_le_pow_left₀ (by positivity)
      linarith
    have hp : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
    have h3 : 64 * ((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 3 ≤ 1024 * ((n : ℝ) + 1) ^ 4 := by
      nlinarith [pow_pos (show (0:ℝ) < (n : ℝ) + 1 by positivity) 3]
    exact le_trans (mul_le_mul_of_nonneg_right h3 hp) (le_of_eq (by ring))
  refine Summable.of_nonneg_of_le (fun n => by positivity) hmaj ?_
  exact summable_poly_geom.mul_left 1024

/-- The limit of the modular row `2 B_n / A_n`. -/
noncomputable def GEreal : ℝ := ∑' n, tE n

lemma ratE_eq_sum (n : ℕ) : 2 * bRe n / aRe n = ∑ k ∈ range n, tE k := by
  induction n with
  | zero => simp [bRe, aRe]
  | succ k ih =>
      rw [Finset.sum_range_succ, ← ih, ← ratE_diff k]
      ring

lemma tendsto_ratE : Tendsto (fun n => 2 * bRe n / aRe n) atTop (𝓝 GEreal) := by
  have h := summable_tE.hasSum.tendsto_sum_nat
  refine h.congr (fun n => ?_)
  rw [ratE_eq_sum n]

/-- The tail of the modular row. -/
lemma ratE_tail (n : ℕ) : GEreal - 2 * bRe n / aRe n = ∑' k, tE (n + k) := by
  have h := summable_tE.sum_add_tsum_nat_add n
  have hc : ∑' i : ℕ, tE (i + n) = ∑' k : ℕ, tE (n + k) :=
    tsum_congr (fun i => by rw [Nat.add_comm])
  rw [hc] at h
  rw [ratE_eq_sum n, GEreal, ← h]
  ring

lemma summable_tE_shift (n : ℕ) : Summable (fun k => tE (n + k)) :=
  ((summable_nat_add_iff n).mpr summable_tE).congr (fun k => by rw [Nat.add_comm])

lemma tail_tE_lb (n : ℕ) : tE n ≤ ∑' k, tE (n + k) := by
  have hsum : Summable (fun k => tE (n + k)) := summable_tE_shift n
  have := hsum.le_tsum 0 (fun i _ => (tE_pos (n + i)).le)
  simpa using this

lemma tail_tE_ub (n : ℕ) :
    ∑' k, tE (n + k) ≤ 64 * geomPoly4 * ((n : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ n := by
  have hsum : Summable (fun k => tE (n + k)) := summable_tE_shift n
  have hmaj : ∀ k : ℕ, tE (n + k)
      ≤ 64 * ((n : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ n * (((k : ℝ) + 1) ^ 4 * (1 / 2 : ℝ) ^ k) := by
    intro k
    refine le_trans (tE_le (n + k)) ?_
    have hcast1 : (((n + k : ℕ) : ℝ) + 1) = (n : ℝ) + (k : ℝ) + 1 := by push_cast; ring
    have hcast2 : (((n + k : ℕ) : ℝ) + 2) = (n : ℝ) + (k : ℝ) + 2 := by push_cast; ring
    rw [hcast1, hcast2]
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hp1 : (n : ℝ) + (k : ℝ) + 1 ≤ ((n : ℝ) + 2) * ((k : ℝ) + 1) := by nlinarith
    have hp2 : (n : ℝ) + (k : ℝ) + 2 ≤ ((n : ℝ) + 2) * ((k : ℝ) + 1) := by nlinarith
    have hp3 : ((n : ℝ) + (k : ℝ) + 2) ^ 3 ≤ (((n : ℝ) + 2) * ((k : ℝ) + 1)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) hp2 3
    have hpow : (1 / 2 : ℝ) ^ (n + k) = (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ k := pow_add _ _ _
    rw [hpow]
    have hbig : ((n : ℝ) + (k : ℝ) + 1) * ((n : ℝ) + (k : ℝ) + 2) ^ 3
        ≤ (((n : ℝ) + 2) * ((k : ℝ) + 1)) ^ 4 := by
      have h := mul_le_mul hp1 hp3 (by positivity) (by positivity)
      calc ((n : ℝ) + (k : ℝ) + 1) * ((n : ℝ) + (k : ℝ) + 2) ^ 3
          ≤ (((n : ℝ) + 2) * ((k : ℝ) + 1)) * ((((n : ℝ) + 2) * ((k : ℝ) + 1)) ^ 3) := h
        _ = (((n : ℝ) + 2) * ((k : ℝ) + 1)) ^ 4 := by ring
    have hq : (0 : ℝ) ≤ 64 * ((1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ k) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hbig hq
    calc 64 * ((n : ℝ) + (k : ℝ) + 1) * ((n : ℝ) + (k : ℝ) + 2) ^ 3
            * ((1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ k)
        = 64 * ((1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ k)
            * (((n : ℝ) + (k : ℝ) + 1) * ((n : ℝ) + (k : ℝ) + 2) ^ 3) := by ring
      _ ≤ 64 * ((1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ k)
            * ((((n : ℝ) + 2) * ((k : ℝ) + 1)) ^ 4) := hmul
      _ = 64 * ((n : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ n
            * (((k : ℝ) + 1) ^ 4 * (1 / 2 : ℝ) ^ k) := by ring
  have hsum2 : Summable (fun k : ℕ => 64 * ((n : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ n
      * (((k : ℝ) + 1) ^ 4 * (1 / 2 : ℝ) ^ k)) := summable_poly_geom.mul_left _
  have := hsum.tsum_mono hsum2 hmaj
  rw [tsum_mul_left] at this
  calc ∑' k, tE (n + k) ≤ 64 * ((n : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ n * geomPoly4 := this
    _ = 64 * geomPoly4 * ((n : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ n := by ring

/-- The limit of the modular row is at least `1/2`; in particular it is nonzero. -/
theorem GEreal_ge_half : (1 : ℝ) / 2 ≤ GEreal := by
  have h := tail_tE_lb 0
  have h0 : tE 0 = 1 / 2 := by
    have h1 : aRe 0 = 1 := by simp [aRe]
    have h2 : aRe 1 = 4 := by simp [aRe]
    rw [tE, h1, h2]
    norm_num
  rw [h0] at h
  simpa [GEreal] using h

theorem GEreal_pos : 0 < GEreal := lt_of_lt_of_le (by norm_num) GEreal_ge_half

/-! ### The rate of the modular linear form -/

private lemma exp_log_four_mul (n : ℕ) : Real.exp (Real.log 4 * n) = (4 : ℝ) ^ n := by
  rw [mul_comm, Real.exp_nat_mul, Real.exp_log]
  norm_num

lemma linE_eq (n : ℕ) : GEreal / 2 * aRe n - bRe n = aRe n / 2 * (∑' k, tE (n + k)) := by
  rw [← ratE_tail n]
  have h := (aRe_pos n).ne'
  field_simp

/-- Equation (9.3), now proved: `(1/n) log |G A_n/2 - B_n| → log 4`. -/
theorem rate_linE : LogRate (fun n => GEreal / 2 * aRe n - bRe n) (Real.log 4) := by
  refine logRate_of_sandwich (f := fun n => GEreal / 2 * aRe n - bRe n) (a := Real.log 4)
    (C := max 16 (8 * (64 * geomPoly4))) 5 (by positivity) ?_ ?_ ?_
  · filter_upwards with n
    rw [linE_eq n]
    have h1 := aRe_pos n
    have h2 := lt_of_lt_of_le (tE_pos n) (tail_tE_lb n)
    exact mul_pos (by positivity) h2
  · filter_upwards with n
    rw [linE_eq n, exp_log_four_mul]
    -- `4^n ≤ 16 (n+1)^3 · (A_n/2) S_n`
    have hlow : (4 : ℝ) ^ n / (8 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2))
        ≤ aRe n / 2 * (∑' k, tE (n + k)) := by
      have hstep : aRe n / 2 * tE n ≤ aRe n / 2 * (∑' k, tE (n + k)) :=
        mul_le_mul_of_nonneg_left (tail_tE_lb n) (by linarith [aRe_pos n])
      refine le_trans ?_ hstep
      have hA : aRe n / 2 * tE n = 32 ^ n / (((n : ℝ) + 1) ^ 2 * aRe (n + 1)) := by
        rw [tE]
        have h := (aRe_pos n).ne'
        field_simp
      rw [hA]
      have hA1 : aRe (n + 1) ≤ ((n : ℝ) + 2) * 8 ^ (n + 1) := by
        have := aRe_ub (n + 1)
        have hcast : (((n + 1 : ℕ) : ℝ) + 1) = ((n : ℝ) + 2) := by push_cast; ring
        rw [hcast] at this
        exact this
      have hden1 : (0 : ℝ) < ((n : ℝ) + 1) ^ 2 * aRe (n + 1) := by
        have := aRe_pos (n + 1); positivity
      have hden2 : (0 : ℝ) < 8 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) := by positivity
      rw [div_le_div_iff₀ hden2 hden1]
      have h8 : (8 : ℝ) ^ (n + 1) = 8 * 8 ^ n := by rw [pow_succ]; ring
      have h32 : (32 : ℝ) ^ n = 4 ^ n * 8 ^ n := by rw [← mul_pow]; norm_num
      have hstep2 : (4 : ℝ) ^ n * (((n : ℝ) + 1) ^ 2 * aRe (n + 1))
          ≤ 4 ^ n * (((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 2) * (8 * 8 ^ n))) := by
        have hc : (0 : ℝ) ≤ 4 ^ n * ((n : ℝ) + 1) ^ 2 := by positivity
        rw [h8] at hA1
        nlinarith [hA1, hc]
      calc (4 : ℝ) ^ n * (((n : ℝ) + 1) ^ 2 * aRe (n + 1))
          ≤ 4 ^ n * (((n : ℝ) + 1) ^ 2 * (((n : ℝ) + 2) * (8 * 8 ^ n))) := hstep2
        _ = 32 ^ n * (8 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2)) := by rw [h32]; ring
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hlow (by positivity))
    have hpos : (0 : ℝ) < 8 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) := by positivity
    rw [mul_div_assoc']
    rw [le_div_iff₀ hpos]
    have h4 : (0 : ℝ) < 4 ^ n := by positivity
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hmax : (16 : ℝ) ≤ max 16 (8 * (64 * geomPoly4)) := le_max_left _ _
    have hpoly : 8 * ((n : ℝ) + 1) ^ 2 * ((n : ℝ) + 2) ≤ 16 * ((n : ℝ) + 1) ^ 5 := by
      have h1 : ((n : ℝ) + 1) ^ 3 ≤ ((n : ℝ) + 1) ^ 5 :=
        pow_le_pow_right₀ (by linarith) (by norm_num)
      nlinarith [mul_nonneg (sq_nonneg ((n : ℝ) + 1)) hn, h1]
    have hstep := mul_le_mul_of_nonneg_left hpoly h4.le
    have hd : 0 ≤ (max 16 (8 * (64 * geomPoly4)) - 16) * (((n : ℝ) + 1) ^ 5 * 4 ^ n) :=
      mul_nonneg (by linarith) (by positivity)
    nlinarith [hstep, hd]
  · filter_upwards with n
    rw [linE_eq n, exp_log_four_mul]
    have hub := tail_tE_ub n
    have hAub := aRe_ub n
    have hApos := aRe_pos n
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hstep : aRe n / 2 * (∑' k, tE (n + k))
        ≤ (((n : ℝ) + 1) * 8 ^ n) / 2 * (64 * geomPoly4 * ((n : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ n) := by
      have h1 : (0 : ℝ) ≤ ∑' k, tE (n + k) := le_trans (tE_pos n).le (tail_tE_lb n)
      have h2 : (0 : ℝ) < 64 * geomPoly4 * ((n : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ n := by
        have := geomPoly4_pos; positivity
      have h3 : aRe n / 2 ≤ ((n : ℝ) + 1) * 8 ^ n / 2 := by linarith
      exact mul_le_mul h3 hub h1 (by positivity)
    refine le_trans hstep ?_
    have h8 : (8 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 4 ^ n := by
      rw [← mul_pow]; norm_num
    have hcalc : (((n : ℝ) + 1) * 8 ^ n) / 2 * (64 * geomPoly4 * ((n : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ n)
        = (32 * geomPoly4) * (((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 4) * (8 ^ n * (1 / 2 : ℝ) ^ n) := by
      ring
    rw [hcalc, h8]
    have hmax : 8 * (64 * geomPoly4) ≤ max 16 (8 * (64 * geomPoly4)) := le_max_right _ _
    have hpoly : ((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 4 ≤ 16 * ((n : ℝ) + 1) ^ 5 := by
      have h2 : ((n : ℝ) + 2) ^ 4 ≤ (2 * ((n : ℝ) + 1)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) (by linarith) 4
      have h3 := mul_le_mul_of_nonneg_left h2 (show (0 : ℝ) ≤ (n : ℝ) + 1 by linarith)
      calc ((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 4
          ≤ ((n : ℝ) + 1) * (2 * ((n : ℝ) + 1)) ^ 4 := h3
        _ = 16 * ((n : ℝ) + 1) ^ 5 := by ring
    have hg := geomPoly4_pos
    have h4pos : (0 : ℝ) < 4 ^ n := by positivity
    have hstep1 : 32 * geomPoly4 * (((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 4) * 4 ^ n
        ≤ 32 * geomPoly4 * (16 * ((n : ℝ) + 1) ^ 5) * 4 ^ n := by
      have hc : (0 : ℝ) ≤ 32 * geomPoly4 := by positivity
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly hc) h4pos.le
    have hd : 0 ≤ (max 16 (8 * (64 * geomPoly4)) - 8 * (64 * geomPoly4))
        * (((n : ℝ) + 1) ^ 5 * 4 ^ n) := mul_nonneg (by linarith) (by positivity)
    nlinarith [hstep1, hd]

/-! ### The Zudilin row -/

/-- `P_m` as a real number. -/
noncomputable def pR (m : ℕ) : ℝ := ((Pz m : ℚ) : ℝ)

/-- The increment of `P_m/Q_m`. -/
noncomputable def tZr (k : ℕ) : ℝ := ((WZ k : ℚ) : ℝ) / (qR k * qR (k + 1))

lemma ratZ_diff (k : ℕ) : pR (k + 1) / qR (k + 1) - pR k / qR k = tZr k := by
  have h1 := (qR_pos k).ne'
  have h2 := (qR_pos (k + 1)).ne'
  have hW : ((WZ k : ℚ) : ℝ) = pR (k + 1) * qR k - qR (k + 1) * pR k := by
    unfold WZ pR qR
    push_cast
    ring
  rw [tZr, hW]
  field_simp

/-- The closed form of `|W_k|`. -/
noncomputable def absW (k : ℕ) : ℝ :=
  (20 * ((k : ℝ) + 1) ^ 2 - 8 * ((k : ℝ) + 1) + 1) / (8 * ((k : ℝ) + 1) ^ 2 * (2 * (k : ℝ) + 1) ^ 2)

lemma absW_num_pos (k : ℕ) : (13 : ℝ) ≤ 20 * ((k : ℝ) + 1) ^ 2 - 8 * ((k : ℝ) + 1) + 1 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  nlinarith

lemma absW_pos (k : ℕ) : 0 < absW k := by
  have h := absW_num_pos k
  unfold absW
  have hden : (0 : ℝ) < 8 * ((k : ℝ) + 1) ^ 2 * (2 * (k : ℝ) + 1) ^ 2 := by positivity
  apply div_pos (by linarith) hden

lemma abs_WZ_eq (k : ℕ) : |((WZ k : ℚ) : ℝ)| = absW k := by
  have h := congrArg (fun z : ℚ => (z : ℝ)) (WZ_closed_form k)
  have hval : ((WZ k : ℚ) : ℝ)
      = (-1 : ℝ) ^ k * ((20 * ((k : ℝ) + 1) ^ 2 - 8 * ((k : ℝ) + 1) + 1)
        / (8 * ((k : ℝ) + 1) ^ 2 * (2 * (k : ℝ) + 1) ^ 2)) := by
    rw [h]; push_cast; ring
  rw [hval, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact abs_of_pos (absW_pos k)

lemma absW_lb (k : ℕ) : (13 : ℝ) / (32 * ((k : ℝ) + 1) ^ 4) ≤ absW k := by
  have hnum := absW_num_pos k
  have hden : (0 : ℝ) < 8 * ((k : ℝ) + 1) ^ 2 * (2 * (k : ℝ) + 1) ^ 2 := by positivity
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  rw [absW, div_le_div_iff₀ (by positivity) hden]
  have hd : 8 * ((k : ℝ) + 1) ^ 2 * (2 * (k : ℝ) + 1) ^ 2 ≤ 32 * ((k : ℝ) + 1) ^ 4 := by
    have h1 : (2 * (k : ℝ) + 1) ^ 2 ≤ (2 * ((k : ℝ) + 1)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 2
    nlinarith [pow_pos (show (0:ℝ) < (k : ℝ) + 1 by positivity) 2]
  nlinarith [pow_pos (show (0:ℝ) < (k : ℝ) + 1 by positivity) 4]

lemma absW_ub (k : ℕ) : absW k ≤ 3 := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hden : (0 : ℝ) < 8 * ((k : ℝ) + 1) ^ 2 * (2 * (k : ℝ) + 1) ^ 2 := by positivity
  rw [absW, div_le_iff₀ hden]
  nlinarith [sq_nonneg ((k : ℝ) + 1), sq_nonneg (2 * (k : ℝ) + 1)]

/-- Consecutive Wronskians are comparable. -/
lemma absW_ratio (k : ℕ) : absW (k + 1) ≤ 6 * absW k := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hden0 : (0 : ℝ) < 8 * ((k : ℝ) + 1) ^ 2 * (2 * (k : ℝ) + 1) ^ 2 := by positivity
  have hden1 : (0 : ℝ) < 8 * ((k : ℝ) + 2) ^ 2 * (2 * (k : ℝ) + 3) ^ 2 := by positivity
  have hval : absW (k + 1)
      = (20 * ((k : ℝ) + 2) ^ 2 - 8 * ((k : ℝ) + 2) + 1)
        / (8 * ((k : ℝ) + 2) ^ 2 * (2 * (k : ℝ) + 3) ^ 2) := by
    unfold absW
    push_cast
    ring_nf
  have hval0 : absW k = (20 * ((k : ℝ) + 1) ^ 2 - 8 * ((k : ℝ) + 1) + 1)
      / (8 * ((k : ℝ) + 1) ^ 2 * (2 * (k : ℝ) + 1) ^ 2) := rfl
  have hnum : 20 * ((k : ℝ) + 2) ^ 2 - 8 * ((k : ℝ) + 2) + 1
      ≤ 6 * (20 * ((k : ℝ) + 1) ^ 2 - 8 * ((k : ℝ) + 1) + 1) := by nlinarith
  have hdenle : 8 * ((k : ℝ) + 1) ^ 2 * (2 * (k : ℝ) + 1) ^ 2
      ≤ 8 * ((k : ℝ) + 2) ^ 2 * (2 * (k : ℝ) + 3) ^ 2 := by nlinarith
  have hnum1 : (0 : ℝ) ≤ 20 * ((k : ℝ) + 2) ^ 2 - 8 * ((k : ℝ) + 2) + 1 := by nlinarith
  rw [hval, hval0, mul_div_assoc', div_le_div_iff₀ hden1 hden0]
  nlinarith [mul_le_mul_of_nonneg_left hdenle hnum1,
    mul_le_mul_of_nonneg_right hnum hden1.le]

lemma tZr_ne_zero (k : ℕ) : tZr k ≠ 0 := by
  have h1 := (qR_pos k).ne'
  have h2 := (qR_pos (k + 1)).ne'
  have hW : ((WZ k : ℚ) : ℝ) ≠ 0 := Rat.cast_ne_zero.mpr (WZ_ne_zero k)
  exact div_ne_zero hW (by positivity)

lemma abs_tZr (k : ℕ) : |tZr k| = absW k / (qR k * qR (k + 1)) := by
  have h : (0 : ℝ) < qR k * qR (k + 1) := by
    have := qR_pos k; have := qR_pos (k + 1); positivity
  rw [tZr, abs_div, abs_of_pos h, abs_WZ_eq]

lemma qR_succ_succ_ge (k : ℕ) (hk : 35 ≤ k) : 100 * qR k ≤ qR (k + 2) := by
  have hq0 := qR_pos k
  have hq1 := qR_pos (k + 1)
  have hrho1 : 10 ≤ rhoZ k := rhoZ_ge_ten k (by omega)
  have hrho2 : 10 ≤ rhoZ (k + 1) := rhoZ_ge_ten (k + 1) (by omega)
  have e1 : qR (k + 1) = rhoZ k * qR k := by
    unfold rhoZ; rw [div_mul_cancel₀ _ hq0.ne']
  have e2 : qR (k + 2) = rhoZ (k + 1) * qR (k + 1) := by
    have h : qR (k + 1 + 1) = rhoZ (k + 1) * qR (k + 1) := by
      unfold rhoZ; rw [div_mul_cancel₀ _ hq1.ne']
    simpa using h
  rw [e2, e1]
  nlinarith

/-- Consecutive increments of the Zudilin row decay by a factor at least four. -/
lemma tZr_ratio (k : ℕ) (hk : 35 ≤ k) : |tZr (k + 1)| ≤ 1 / 4 * |tZr k| := by
  have hq0 := qR_pos k
  have hq1 := qR_pos (k + 1)
  have hq2 := qR_pos (k + 2)
  have hQ2 := qR_succ_succ_ge k hk
  have hW := absW_ratio k
  have hWpos := absW_pos k
  have hcast : qR (k + 1 + 1) = qR (k + 2) := by norm_num
  rw [abs_tZr, abs_tZr, hcast, div_le_iff₀ (by positivity : (0 : ℝ) < qR (k + 1) * qR (k + 2))]
  have key : 1 / 4 * (absW k / (qR k * qR (k + 1))) * (qR (k + 1) * qR (k + 2))
      = absW k * qR (k + 2) / (4 * qR k) := by
    field_simp
  rw [key, le_div_iff₀ (by positivity : (0 : ℝ) < 4 * qR k)]
  nlinarith [mul_le_mul_of_nonneg_left hQ2 hWpos.le,
    mul_le_mul_of_nonneg_right hW (by positivity : (0 : ℝ) ≤ 4 * qR k),
    mul_nonneg hWpos.le hq0.le]

lemma summable_tZr : Summable tZr := by
  refine summable_of_ratio_norm_eventually_le (r := 1 / 4) (by norm_num) ?_
  filter_upwards [eventually_ge_atTop 35] with k hk
  simpa [Real.norm_eq_abs] using tZr_ratio k hk

lemma tZr_decay (n : ℕ) (hn : 35 ≤ n) : ∀ j : ℕ, |tZr (n + j)| ≤ (1 / 4 : ℝ) ^ j * |tZr n| := by
  intro j
  induction j with
  | zero => simp
  | succ i ih =>
      have h := tZr_ratio (n + i) (by omega)
      have hstep : |tZr (n + (i + 1))| ≤ 1 / 4 * |tZr (n + i)| := by
        have e : n + (i + 1) = (n + i) + 1 := by omega
        rw [e]; exact h
      calc |tZr (n + (i + 1))| ≤ 1 / 4 * |tZr (n + i)| := hstep
        _ ≤ 1 / 4 * ((1 / 4 : ℝ) ^ i * |tZr n|) := by
            exact mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1 / 4 : ℝ) ^ (i + 1) * |tZr n| := by ring

lemma summable_tZr_shift (n : ℕ) : Summable (fun k => tZr (n + k)) :=
  ((summable_nat_add_iff n).mpr summable_tZr).congr (fun k => by rw [Nat.add_comm])

set_option maxHeartbeats 1000000 in
lemma tZr_tail_bounds (n : ℕ) (hn : 35 ≤ n) :
    2 / 3 * |tZr n| ≤ |∑' k, tZr (n + k)| ∧ |∑' k, tZr (n + k)| ≤ 4 / 3 * |tZr n| := by
  have hsum : Summable (fun k => tZr (n + k)) := summable_tZr_shift n
  have hsum1 : Summable (fun k => tZr (n + 1 + k)) := summable_tZr_shift (n + 1)
  have hsplit : ∑' k, tZr (n + k) = tZr n + ∑' k, tZr (n + 1 + k) := by
    have h2 : ∑' b : ℕ, tZr (n + (b + 1)) = ∑' k : ℕ, tZr (n + 1 + k) :=
      tsum_congr (fun k => by congr 1; omega)
    calc ∑' k, tZr (n + k) = tZr (n + 0) + ∑' b : ℕ, tZr (n + (b + 1)) :=
          hsum.tsum_eq_zero_add
      _ = tZr n + ∑' k, tZr (n + 1 + k) := by rw [h2, Nat.add_zero]
  have htail : |∑' k, tZr (n + 1 + k)| ≤ 1 / 3 * |tZr n| := by
    have hgeom : Summable (fun k : ℕ => (1 / 4 : ℝ) ^ (k + 1) * |tZr n|) := by
      have := (summable_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 4)
        (by norm_num : (1 / 4 : ℝ) < 1))
      have h2 := (this.mul_left (1 / 4 : ℝ)).mul_right |tZr n|
      refine h2.congr (fun k => ?_)
      rw [pow_succ]
      ring
    have hmaj : ∀ k : ℕ, |tZr (n + 1 + k)| ≤ (1 / 4 : ℝ) ^ (k + 1) * |tZr n| := by
      intro k
      have h := tZr_decay n hn (k + 1)
      have e : n + (k + 1) = n + 1 + k := by omega
      rw [e] at h
      exact h
    have hnorm : Summable (fun k => ‖tZr (n + 1 + k)‖) := by
      simpa [Real.norm_eq_abs] using hsum1.abs
    have habs := norm_tsum_le_tsum_norm hnorm
    simp only [Real.norm_eq_abs] at habs
    calc |∑' k, tZr (n + 1 + k)| ≤ ∑' k, |tZr (n + 1 + k)| := habs
      _ ≤ ∑' k : ℕ, (1 / 4 : ℝ) ^ (k + 1) * |tZr n| :=
          hsum1.abs.tsum_mono hgeom hmaj
      _ = 1 / 3 * |tZr n| := by
          rw [tsum_mul_right]
          have hg : ∑' k : ℕ, (1 / 4 : ℝ) ^ (k + 1) = 1 / 3 := by
            have h := tsum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1 / 4)
              (by norm_num : (1 / 4 : ℝ) < 1)
            have h2 : ∑' k : ℕ, (1 / 4 : ℝ) ^ (k + 1) = (1 / 4 : ℝ) * ∑' k : ℕ, (1 / 4 : ℝ) ^ k := by
              rw [← tsum_mul_left]
              refine tsum_congr (fun k => ?_)
              rw [pow_succ]
              ring
            rw [h2, h]
            norm_num
          rw [hg]
  constructor
  · rw [hsplit]
    calc 2 / 3 * |tZr n| = |tZr n| - 1 / 3 * |tZr n| := by ring
      _ ≤ |tZr n| - |∑' k, tZr (n + 1 + k)| := by linarith
      _ ≤ |tZr n + ∑' k, tZr (n + 1 + k)| := by
          have h := abs_sub_abs_le_abs_sub (tZr n) (-(∑' k, tZr (n + 1 + k)))
          rw [abs_neg, sub_neg_eq_add] at h
          linarith
  · rw [hsplit]
    calc |tZr n + ∑' k, tZr (n + 1 + k)| ≤ |tZr n| + |∑' k, tZr (n + 1 + k)| := abs_add_le _ _
      _ ≤ |tZr n| + 1 / 3 * |tZr n| := by linarith
      _ = 4 / 3 * |tZr n| := by ring

/-- The limit of the Zudilin row `P_m / Q_m`. -/
noncomputable def GZreal : ℝ := ∑' k, tZr k

lemma ratZ_eq_sum (m : ℕ) : pR m / qR m = ∑ k ∈ range m, tZr k := by
  induction m with
  | zero => simp [pR, qR]
  | succ k ih =>
      rw [Finset.sum_range_succ, ← ih, ← ratZ_diff k]
      ring

lemma tendsto_ratZ : Tendsto (fun m => pR m / qR m) atTop (𝓝 GZreal) := by
  have h := summable_tZr.hasSum.tendsto_sum_nat
  refine h.congr (fun n => ?_)
  rw [ratZ_eq_sum n]

lemma ratZ_tail (n : ℕ) : GZreal - pR n / qR n = ∑' k, tZr (n + k) := by
  have h := summable_tZr.sum_add_tsum_nat_add n
  have hc : ∑' i : ℕ, tZr (i + n) = ∑' k : ℕ, tZr (n + k) :=
    tsum_congr (fun i => by rw [Nat.add_comm])
  rw [hc] at h
  rw [ratZ_eq_sum n, GZreal, ← h]
  ring

lemma linZ_eq (m : ℕ) : qR m * GZreal - pR m = qR m * (∑' k, tZr (m + k)) := by
  rw [← ratZ_tail m]
  have h := (qR_pos m).ne'
  field_simp

/-- The rate of the Wronskian quotient `|W_m| / Q_{m+1}`. -/
lemma rate_absW_div : LogRate (fun m => absW m / qR (m + 1))
    (-(5 * Real.log Real.goldenRatio)) := by
  have h1 : LogRate absW 0 := by
    refine logRate_of_sandwich (f := absW) (a := 0) (C := 32) 4 (by norm_num)
      (Eventually.of_forall (fun m => absW_pos m)) ?_ ?_
    · filter_upwards with m
      have h := absW_lb m
      have hp : (0 : ℝ) < 32 * ((m : ℝ) + 1) ^ 4 := by positivity
      rw [zero_mul, Real.exp_zero]
      rw [div_le_iff₀ hp] at h
      linarith
    · filter_upwards with m
      have h := absW_ub m
      have hm : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 4 := by
        have : (1 : ℝ) ≤ (m : ℝ) + 1 := by
          have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
          linarith
        exact one_le_pow₀ this
      rw [zero_mul, Real.exp_zero, mul_one]
      nlinarith
  have h2 : LogRate (fun m => (qR (m + 1))⁻¹) (-(5 * Real.log Real.goldenRatio)) :=
    (rate_Qz.shift).inv
  have h3 := h1.mul h2 (Eventually.of_forall (fun m => (absW_pos m).ne'))
    (Eventually.of_forall (fun m => inv_ne_zero (qR_pos (m + 1)).ne'))
  rw [zero_add] at h3
  refine h3.of_eq (fun m => ?_)
  rw [div_eq_mul_inv]

/-- Imported Theorem Z, second half, now proved: `(1/m) log |Q_m G - P_m| → -5 log φ`. -/
theorem rate_linZ :
    LogRate (fun m => qR m * GZreal - pR m) (-(5 * Real.log Real.goldenRatio)) := by
  have hgne : ∀ᶠ m in atTop, absW m / qR (m + 1) ≠ 0 := by
    filter_upwards with m
    exact div_ne_zero (absW_pos m).ne' (qR_pos (m + 1)).ne'
  have hkey : ∀ m : ℕ, 35 ≤ m →
      2 / 3 * |absW m / qR (m + 1)| ≤ |qR m * GZreal - pR m| ∧
      |qR m * GZreal - pR m| ≤ 4 / 3 * |absW m / qR (m + 1)| := by
    intro m hm
    obtain ⟨hlo, hhi⟩ := tZr_tail_bounds m hm
    have hq := qR_pos m
    have hq1 := qR_pos (m + 1)
    have habs : |qR m * (∑' k, tZr (m + k))| = qR m * |∑' k, tZr (m + k)| := by
      rw [abs_mul, abs_of_pos hq]
    have hrel : qR m * |tZr m| = |absW m / qR (m + 1)| := by
      rw [abs_tZr m, abs_of_pos (div_pos (absW_pos m) hq1)]
      field_simp
    rw [linZ_eq m, habs]
    constructor
    · rw [← hrel]
      have := mul_le_mul_of_nonneg_left hlo hq.le
      calc 2 / 3 * (qR m * |tZr m|) = qR m * (2 / 3 * |tZr m|) := by ring
        _ ≤ qR m * |∑' k, tZr (m + k)| := this
    · rw [← hrel]
      have := mul_le_mul_of_nonneg_left hhi hq.le
      calc qR m * |∑' k, tZr (m + k)| ≤ qR m * (4 / 3 * |tZr m|) := this
        _ = 4 / 3 * (qR m * |tZr m|) := by ring
  refine LogRate.of_ratio_bounded (c₁ := 2 / 3) (c₂ := 4 / 3) (by norm_num) (by norm_num)
    rate_absW_div hgne ?_ ?_
  · filter_upwards [eventually_ge_atTop 35] with m hm
    exact (hkey m hm).1
  · filter_upwards [eventually_ge_atTop 35] with m hm
    exact (hkey m hm).2

end Catalan
