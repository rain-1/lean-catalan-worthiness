import Mathlib

/-!
# A small `2`-adic limit toolkit

We record the facts about `ℚ_[2]` that are needed to turn the exact increment valuations
proved for the two Catalan rows into `2`-adic limits together with *exact* tail valuations.

The main statement is `padic2_limit_of_strictMono_val`: if the increments of a rational
sequence have valuations `w n` with `w` strictly increasing, then the sequence converges in
`ℚ_[2]` and the tail `L - r n` has valuation exactly `w n`.
-/

namespace Catalan

open Filter Topology

/-- Norm of a rational number viewed in `ℚ_[2]`. -/
lemma norm_ratCast_padic2 {q : ℚ} (hq : q ≠ 0) :
    ‖((q : ℚ_[2]))‖ = (2 : ℝ) ^ (-(padicValRat 2 q)) := by
  have hq2 : ((q : ℚ_[2])) ≠ 0 := by
    simpa using (Rat.cast_injective (α := ℚ_[2])).ne_iff.mpr hq
  rw [Padic.norm_eq_zpow_neg_valuation hq2, Padic.valuation_ratCast]
  norm_num

lemma padic2_valuation_eq_of_norm {x : ℚ_[2]} {k : ℤ} (hx : x ≠ 0)
    (h : ‖x‖ = (2 : ℝ) ^ (-k)) : Padic.valuation x = k := by
  rw [Padic.norm_eq_zpow_neg_valuation hx] at h
  have h2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [h2] at h
  have := zpow_right_injective₀ (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1) h
  omega

lemma padic2_ne_zero_of_norm_pos {x : ℚ_[2]} (h : ‖x‖ ≠ 0) : x ≠ 0 := by
  intro hx; apply h; simp [hx]

lemma padic2_valuation_neg {x : ℚ_[2]} (hx : x ≠ 0) :
    Padic.valuation (-x) = Padic.valuation x := by
  have h1 : ‖(-x)‖ = ‖x‖ := norm_neg x
  rw [Padic.norm_eq_zpow_neg_valuation hx,
    Padic.norm_eq_zpow_neg_valuation (neg_ne_zero.mpr hx)] at h1
  have := zpow_right_injective₀ (by norm_num : (0:ℝ) < ((2:ℕ):ℝ))
    (by norm_num : ((2:ℕ):ℝ) ≠ 1) h1
  omega

/-- Ultrametric equality rule: a sum of two nonzero `2`-adic numbers of distinct valuations has
the smaller valuation. -/
lemma padic2_valuation_add_of_lt {x y : ℚ_[2]} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : Padic.valuation x < Padic.valuation y) :
    x + y ≠ 0 ∧ Padic.valuation (x + y) = Padic.valuation x := by
  have hnx : ‖x‖ = (2 : ℝ) ^ (-(Padic.valuation x)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hx]; norm_num
  have hny : ‖y‖ = (2 : ℝ) ^ (-(Padic.valuation y)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hy]; norm_num
  have hlt : ‖y‖ < ‖x‖ := by
    rw [hnx, hny]
    exact zpow_lt_zpow_right₀ (by norm_num) (by omega)
  have hsum : ‖x + y‖ = ‖x‖ :=
    (IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt hlt)).trans
      (max_eq_left (le_of_lt hlt))
  have hne : x + y ≠ 0 := by
    apply padic2_ne_zero_of_norm_pos
    rw [hsum, hnx]
    positivity
  exact ⟨hne, padic2_valuation_eq_of_norm hne (by rw [hsum, hnx])⟩

/-- The main convergence and exact-tail statement. -/
theorem padic2_limit_of_strictMono_val {r : ℕ → ℚ} {w : ℕ → ℤ}
    (hne : ∀ n, r (n + 1) - r n ≠ 0)
    (hval : ∀ n, padicValRat 2 (r (n + 1) - r n) = w n)
    (hmono : StrictMono w) :
    ∃ L : ℚ_[2], Tendsto (fun n => ((r n : ℚ) : ℚ_[2])) atTop (𝓝 L) ∧
      ∀ n, L - ((r n : ℚ) : ℚ_[2]) ≠ 0 ∧ Padic.valuation (L - ((r n : ℚ) : ℚ_[2])) = w n := by
  set f : ℕ → ℚ_[2] := fun n => ((r n : ℚ) : ℚ_[2]) with hf
  -- exact norms of the increments
  have hstep : ∀ n, ‖f (n + 1) - f n‖ = (2 : ℝ) ^ (-(w n)) := by
    intro n
    have hrw : f (n + 1) - f n = ((r (n + 1) - r n : ℚ) : ℚ_[2]) := by
      simp [hf]
    rw [hrw, norm_ratCast_padic2 (hne n), hval n]
  -- geometric decay
  have hwge : ∀ n : ℕ, w 0 + (n : ℤ) ≤ w n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih =>
        have hk : w k < w (k + 1) := hmono (by omega)
        push_cast
        omega
  have hgeo : ∀ n : ℕ, dist (f n) (f (n + 1)) ≤ ((2 : ℝ) ^ (-(w 0))) * (1 / 2 : ℝ) ^ n := by
    intro n
    have h1 : dist (f n) (f (n + 1)) = ‖f (n + 1) - f n‖ := by
      rw [dist_eq_norm, ← norm_neg]
      congr 1
      ring
    rw [h1, hstep n]
    have h2 : ((2 : ℝ) ^ (-(w n))) ≤ (2 : ℝ) ^ (-(w 0 + (n : ℤ))) :=
      zpow_le_zpow_right₀ (by norm_num) (by have := hwge n; omega)
    calc (2 : ℝ) ^ (-(w n)) ≤ (2 : ℝ) ^ (-(w 0 + (n : ℤ))) := h2
      _ = ((2 : ℝ) ^ (-(w 0))) * (1 / 2 : ℝ) ^ n := by
          rw [neg_add, zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
          congr 1
          rw [zpow_neg, zpow_natCast]
          simp
  have hcau : CauchySeq f := cauchySeq_of_le_geometric (1/2 : ℝ) _ (by norm_num) hgeo
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨L, hL, ?_⟩
  -- tail bound
  have htail : ∀ n : ℕ, ‖L - f n‖ ≤ (2 : ℝ) ^ (-(w n)) := by
    intro n
    have hbd : ∀ m : ℕ, ‖f (m + n) - f n‖ ≤ (2 : ℝ) ^ (-(w n)) := by
      intro m
      induction m with
      | zero => simp; positivity
      | succ k ih =>
          have hsplit : f (k + 1 + n) - f n = (f (k + n + 1) - f (k + n)) + (f (k + n) - f n) := by
            have he : k + 1 + n = k + n + 1 := by omega
            rw [he]; ring
          have h1 : ‖f (k + n + 1) - f (k + n)‖ ≤ (2 : ℝ) ^ (-(w n)) := by
            rw [hstep]
            have hle : w n ≤ w (k + n) := hmono.monotone (by omega)
            exact zpow_le_zpow_right₀ (by norm_num) (by omega)
          rw [hsplit]
          exact le_trans (IsUltrametricDist.norm_add_le_max _ _) (max_le h1 ih)
    have hlim : Tendsto (fun m => ‖f (m + n) - f n‖) atTop (𝓝 ‖L - f n‖) :=
      ((hL.comp (tendsto_add_atTop_nat n)).sub_const (f n)).norm
    exact le_of_tendsto hlim (Eventually.of_forall hbd)
  intro n
  have hlt : ‖L - f (n + 1)‖ < ‖f (n + 1) - f n‖ := by
    rw [hstep n]
    refine lt_of_le_of_lt (htail (n + 1)) ?_
    have hs : w n < w (n + 1) := hmono (by omega)
    exact zpow_lt_zpow_right₀ (by norm_num) (by omega)
  have hsum : L - f n = (L - f (n + 1)) + (f (n + 1) - f n) := by ring
  have hnorm : ‖L - f n‖ = (2 : ℝ) ^ (-(w n)) := by
    rw [hsum, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_lt hlt), hstep n]
    exact max_eq_right (le_of_lt (by rw [hstep n] at hlt; exact hlt))
  have hne0 : L - f n ≠ 0 := by
    apply padic2_ne_zero_of_norm_pos
    rw [hnorm]
    positivity
  exact ⟨hne0, padic2_valuation_eq_of_norm hne0 hnorm⟩

end Catalan
