import RequestProject.CrossIdentity

/-!
# The off-diagonal `2`-adic cross bound

The diagonal cross theorem `v₂(P_m A_{2m} - 2 B_{2m} Q_m) = 4m - 1` of `Plucker.lean` compares
the Zudilin row at index `m` with the modular row at index `2m`.  For the improved worthiness
bound the two rows are sampled at the *off-diagonal* indices `5n` and `8n`, and what is needed is
the lower bound

`v₂(P_i A_k - 2 B_k Q_i) ≥ min(8i - 1 - 4 s₂(i), 5k - 1 - 4 s₂(k)) - 4i + 2 s₂(i) + 2 s₂(k)`,

which follows from the same two exact tail valuations (`val_GZ2_sub`, `val_GE2_sub`) and the
cross-realization identity `𝒢_{Z,2} = 𝒢_{E,2}`, now used through the ultrametric *inequality*
instead of the equality case.  Specialized to `i = 5n`, `k = 8n` this gives

`v₂(P_{5n} A_{8n} - 2 B_{8n} Q_{5n}) ≥ 20n - 3 - 2⌊log₂(5n)⌋`  (`val_Delta58_ge`).
-/

namespace Catalan

open Filter

/-- Ultrametric inequality in valuation form: the valuation of a sum is at least the minimum of
the two valuations. -/
lemma padic2_valuation_add_ge {x y : ℚ_[2]} (hx : x ≠ 0) (hy : y ≠ 0) (hxy : x + y ≠ 0) :
    min (Padic.valuation x) (Padic.valuation y) ≤ Padic.valuation (x + y) := by
  have hnx : ‖x‖ = (2 : ℝ) ^ (-(Padic.valuation x)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hx]; norm_num
  have hny : ‖y‖ = (2 : ℝ) ^ (-(Padic.valuation y)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hy]; norm_num
  have hns : ‖x + y‖ = (2 : ℝ) ^ (-(Padic.valuation (x + y))) := by
    rw [Padic.norm_eq_zpow_neg_valuation hxy]; norm_num
  have hmax : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := IsUltrametricDist.norm_add_le_max x y
  have hbound : (2 : ℝ) ^ (-(Padic.valuation (x + y)))
      ≤ (2 : ℝ) ^ (-(min (Padic.valuation x) (Padic.valuation y))) := by
    rw [← hns]
    refine hmax.trans ?_
    rcases le_total (Padic.valuation x) (Padic.valuation y) with h | h
    · rw [min_eq_left h, ← hnx]
      refine max_le le_rfl ?_
      rw [hnx, hny]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
    · rw [min_eq_right h, ← hny]
      refine max_le ?_ le_rfl
      rw [hnx, hny]
      exact zpow_le_zpow_right₀ (by norm_num) (by omega)
  by_contra hcon
  push_neg at hcon
  have : (2 : ℝ) ^ (-(min (Padic.valuation x) (Padic.valuation y)))
      < (2 : ℝ) ^ (-(Padic.valuation (x + y))) :=
    zpow_lt_zpow_right₀ (by norm_num) (by omega)
  linarith

/-- The generalized Plücker factorization, at arbitrary pairs of indices. -/
lemma plucker_factor_offdiag (i k : ℕ) :
    Pz i * Ae k - 2 * Be k * Qz i = Qz i * Ae k * (RatZ i - RatE k) := by
  unfold RatZ RatE
  have hQ : Qz i ≠ 0 := Qz_ne_zero i
  have hA : Ae k ≠ 0 := Ae_ne_zero k
  field_simp

/-- The off-diagonal analogue of `val_ratio_cross`: the difference of the two rational rows has
valuation at least the minimum of the two exact tail valuations. -/
theorem val_ratio_offdiag (i k : ℕ) (h : RatZ i - RatE k ≠ 0) :
    min (8 * (i : ℤ) - 1 - 4 * (s2 i : ℤ)) (5 * (k : ℤ) - 1 - 4 * (s2 k : ℤ))
      ≤ padicValRat 2 (RatZ i - RatE k) := by
  set x : ℚ_[2] := -(GZ2 - ((RatZ i : ℚ) : ℚ_[2])) with hx
  set y : ℚ_[2] := GE2 - ((RatE k : ℚ) : ℚ_[2]) with hy
  have hxne : x ≠ 0 := neg_ne_zero.mpr (GZ2_sub_ne_zero i)
  have hyne : y ≠ 0 := GE2_sub_ne_zero k
  have hvx : Padic.valuation x = 8 * (i : ℤ) - 1 - 4 * (s2 i : ℤ) := by
    rw [hx, padic2_valuation_neg (GZ2_sub_ne_zero i), val_GZ2_sub i]
  have hvy : Padic.valuation y = 5 * (k : ℤ) - 1 - 4 * (s2 k : ℤ) := val_GE2_sub k
  have hsum : x + y = ((RatZ i - RatE k : ℚ) : ℚ_[2]) := by
    rw [hx, hy, cross_identity]
    push_cast
    ring
  have hsne : x + y ≠ 0 := by
    rw [hsum]
    exact_mod_cast (Rat.cast_injective (α := ℚ_[2])).ne_iff.mpr h
  have hge := padic2_valuation_add_ge hxne hyne hsne
  rw [hvx, hvy, hsum, Padic.valuation_ratCast] at hge
  exact hge

/-! ### Digit bounds -/

/-- The binary digit sum is at most the number of binary digits. -/
lemma s2_le_log_succ (m : ℕ) (hm : 1 ≤ m) : s2 m ≤ Nat.log 2 m + 1 := by
  have hlen : (Nat.digits 2 m).length = Nat.log 2 m + 1 :=
    Nat.digits_len 2 m (by norm_num) (by omega)
  have hsum : (Nat.digits 2 m).sum ≤ (Nat.digits 2 m).length * 1 := by
    refine (List.sum_le_card_nsmul _ 1 ?_).trans_eq (by simp)
    intro d hd
    have := Nat.digits_lt_base (by norm_num : 1 < 2) hd
    omega
  simpa [s2, hlen] using hsum

/-! ### The `5 : 8` off-diagonal bound -/

/-- The off-diagonal cross combination `Δ_n = P_{5n} A_{8n} - 2 B_{8n} Q_{5n}`. -/
noncomputable def Delta58 (n : ℕ) : ℚ := Pz (5 * n) * Ae (8 * n) - 2 * Be (8 * n) * Qz (5 * n)

lemma s2_eight_mul (n : ℕ) : s2 (8 * n) = s2 n := by
  have h1 : 8 * n = 2 * (2 * (2 * n)) := by ring
  rw [h1, s2_two_mul, s2_two_mul, s2_two_mul]

/-- **The off-diagonal `5 : 8` cross bound.** -/
theorem val_Delta58_ge (n : ℕ) (hn : 1 ≤ n) (h : Delta58 n ≠ 0) :
    20 * (n : ℤ) - 3 - 2 * (Nat.log 2 (5 * n) : ℤ) ≤ padicValRat 2 (Delta58 n) := by
  have hQ : Qz (5 * n) ≠ 0 := Qz_ne_zero (5 * n)
  have hA : Ae (8 * n) ≠ 0 := Ae_ne_zero (8 * n)
  have hfac : Delta58 n = Qz (5 * n) * Ae (8 * n) * (RatZ (5 * n) - RatE (8 * n)) :=
    plucker_factor_offdiag (5 * n) (8 * n)
  have hdiff : RatZ (5 * n) - RatE (8 * n) ≠ 0 := by
    intro hz
    apply h
    rw [hfac, hz, mul_zero]
  have hval := val_ratio_offdiag (5 * n) (8 * n) hdiff
  have hvalD : padicValRat 2 (Delta58 n)
      = (-4 * (5 * n : ℤ) + 2 * (s2 (5 * n) : ℤ)) + 2 * (s2 (8 * n) : ℤ)
        + padicValRat 2 (RatZ (5 * n) - RatE (8 * n)) := by
    rw [hfac, padicValRat.mul (mul_ne_zero hQ hA) hdiff, padicValRat.mul hQ hA,
      val_Qz (5 * n), val_Ae (8 * n)]
    push_cast
    ring
  have h8 : (s2 (8 * n) : ℤ) = (s2 n : ℤ) := by rw [s2_eight_mul]
  have hb1 : s2 (5 * n) ≤ Nat.log 2 (5 * n) + 1 := s2_le_log_succ (5 * n) (by omega)
  have hb2 : s2 n ≤ Nat.log 2 (5 * n) + 1 := by
    refine le_trans (s2_le_log_succ n hn) ?_
    have : Nat.log 2 n ≤ Nat.log 2 (5 * n) := Nat.log_mono_right (by omega)
    omega
  have hb1' : (s2 (5 * n) : ℤ) ≤ (Nat.log 2 (5 * n) : ℤ) + 1 := by exact_mod_cast hb1
  have hb2' : (s2 n : ℤ) ≤ (Nat.log 2 (5 * n) : ℤ) + 1 := by exact_mod_cast hb2
  have hnn1 : (0 : ℤ) ≤ (s2 (5 * n) : ℤ) := Int.natCast_nonneg _
  have hnn2 : (0 : ℤ) ≤ (s2 n : ℤ) := Int.natCast_nonneg _
  rw [hvalD, h8]
  have hmin := hval
  rw [h8] at hmin
  push_cast at hmin ⊢
  rcases le_total (8 * (5 * (n : ℤ)) - 1 - 4 * (s2 (5 * n) : ℤ))
      (5 * (8 * (n : ℤ)) - 1 - 4 * (s2 n : ℤ)) with hc | hc
  · rw [min_eq_left hc] at hmin
    omega
  · rw [min_eq_right hc] at hmin
    omega

end Catalan
