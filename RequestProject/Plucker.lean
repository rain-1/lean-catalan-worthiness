import RequestProject.Limits

/-!
# The exact cross-determinant (Plücker) valuation

Section 13 of the base note / Section 8 of the unconditional note.

Given the cross-realization identity `𝒢_{Z,2} = 𝒢_{E,2}` (proved unconditionally in
`CrossIdentity.lean`) we deduce

* `val_ratio_cross` : `v₂(P_m/Q_m - 2B_{2m}/A_{2m}) = 8m - 1 - 4 s₂(m)`  (`m ≥ 1`),
* `val_plucker`     : `v₂(P_m A_{2m} - 2 B_{2m} Q_m) = 4m - 1`            (`m ≥ 1`).
-/

namespace Catalan

open Filter Topology

/-- Proposition 13.1, in the form of an equality of `2`-adic valuations of a rational number. -/
theorem val_ratio_cross (hGap : GZ2 = GE2) (m : ℕ) (hm : 1 ≤ m) :
    padicValRat 2 (RatZ m - RatE (2 * m)) = 8 * (m : ℤ) - 1 - 4 * (s2 m : ℤ) := by
  set x : ℚ_[2] := -(GZ2 - ((RatZ m : ℚ) : ℚ_[2])) with hx
  set y : ℚ_[2] := GE2 - ((RatE (2 * m) : ℚ) : ℚ_[2]) with hy
  have hxne : x ≠ 0 := neg_ne_zero.mpr (GZ2_sub_ne_zero m)
  have hyne : y ≠ 0 := GE2_sub_ne_zero (2 * m)
  have hvx : Padic.valuation x = 8 * (m : ℤ) - 1 - 4 * (s2 m : ℤ) := by
    rw [hx, padic2_valuation_neg (GZ2_sub_ne_zero m), val_GZ2_sub m]
  have hvy : Padic.valuation y = 10 * (m : ℤ) - 1 - 4 * (s2 m : ℤ) := val_GE2_sub_two_mul m
  have hlt : Padic.valuation x < Padic.valuation y := by
    rw [hvx, hvy]
    have : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
    omega
  obtain ⟨hne, hval⟩ := padic2_valuation_add_of_lt hxne hyne hlt
  have hsum : x + y = ((RatZ m - RatE (2 * m) : ℚ) : ℚ_[2]) := by
    rw [hx, hy, hGap]
    push_cast
    ring
  rw [hsum] at hval
  rw [Padic.valuation_ratCast] at hval
  rw [hval, hvx]

/-- The factorisation `P_m A_{2m} - 2 B_{2m} Q_m = Q_m A_{2m} (P_m/Q_m - 2B_{2m}/A_{2m})`. -/
lemma plucker_factor (m : ℕ) :
    Pz m * Ae (2 * m) - 2 * Be (2 * m) * Qz m
      = Qz m * Ae (2 * m) * (RatZ m - RatE (2 * m)) := by
  unfold RatZ RatE
  have hQ : Qz m ≠ 0 := Qz_ne_zero m
  have hA : Ae (2 * m) ≠ 0 := Ae_ne_zero (2 * m)
  field_simp

/-- Theorem 13.2 / Theorem 8.1: the exact Plücker valuation
`v₂(P_m A_{2m} - 2 B_{2m} Q_m) = 4m - 1` for `m ≥ 1`. -/
theorem val_plucker (hGap : GZ2 = GE2) (m : ℕ) (hm : 1 ≤ m) :
    padicValRat 2 (Pz m * Ae (2 * m) - 2 * Be (2 * m) * Qz m) = 4 * (m : ℤ) - 1 := by
  have hQ : Qz m ≠ 0 := Qz_ne_zero m
  have hA : Ae (2 * m) ≠ 0 := Ae_ne_zero (2 * m)
  have hdiff : RatZ m - RatE (2 * m) ≠ 0 := by
    intro h
    have := val_ratio_cross hGap m hm
    rw [h] at this
    simp only [padicValRat.zero] at this
    have h1 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
    have h2 : (s2 m : ℤ) ≤ (m : ℤ) := by exact_mod_cast s2_le m
    omega
  rw [plucker_factor m, padicValRat.mul (mul_ne_zero hQ hA) hdiff,
    padicValRat.mul hQ hA, val_Qz m, val_Ae (2 * m), val_ratio_cross hGap m hm, s2_two_mul m]
  ring

end Catalan
