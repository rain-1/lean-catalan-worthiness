import RequestProject.Padic2
import RequestProject.Zudilin
import RequestProject.EFamily

/-!
# The two `2`-adic Catalan limits and their exact tails

Sections 8.2 and 11.2 of the base note.  Using the exact valuations of the increments
(`val_ratio_diff` and `val_E_ratio_diff`) together with the toolkit of `Padic2.lean`, both
rational rows converge in `ℚ_[2]` and the tails are computed exactly:

* `val_GZ2_sub` : `v₂(𝒢_{Z,2} - P_m/Q_m) = 8m - 1 - 4 s₂(m)`,
* `val_GE2_sub` : `v₂(𝒢_{E,2} - 2B_n/A_n) = 5n - 1 - 4 s₂(n)`,
* `val_GE2_sub_two_mul` : `v₂(𝒢_{E,2} - 2B_{2m}/A_{2m}) = 10m - 1 - 4 s₂(m)`.
-/

namespace Catalan

open Filter Topology

/-! ### The Zudilin row -/

/-- `R^Z_m = P_m / Q_m`. -/
noncomputable def RatZ (m : ℕ) : ℚ := Pz m / Qz m

/-- `w^Z_m = 8m - 1 - 4 s₂(m)`, the valuation of the tail after index `m`. -/
def wZfun (m : ℕ) : ℤ := 8 * (m : ℤ) - 1 - 4 * (s2 m : ℤ)

lemma RatZ_diff_eq (k : ℕ) : RatZ (k + 1) - RatZ k = WZ k / (Qz (k + 1) * Qz k) := by
  unfold RatZ WZ
  have hQ1 : Qz (k + 1) ≠ 0 := Qz_ne_zero (k + 1)
  have hQ0 : Qz k ≠ 0 := Qz_ne_zero k
  field_simp

lemma RatZ_diff_ne_zero (k : ℕ) : RatZ (k + 1) - RatZ k ≠ 0 := by
  rw [RatZ_diff_eq]
  exact div_ne_zero (WZ_ne_zero k) (mul_ne_zero (Qz_ne_zero (k + 1)) (Qz_ne_zero k))

lemma val_RatZ_diff (k : ℕ) : padicValRat 2 (RatZ (k + 1) - RatZ k) = wZfun k := by
  have h := val_ratio_diff k
  have hs : (s2 (k + 1) : ℤ) = (s2 k : ℤ) + 1 - (padicValNat 2 (k + 1) : ℤ) := s2_succ k
  unfold RatZ wZfun
  rw [h]
  omega

lemma wZfun_strictMono : StrictMono wZfun := by
  refine strictMono_nat_of_lt_succ ?_
  intro k
  have hs : (s2 (k + 1) : ℤ) = (s2 k : ℤ) + 1 - (padicValNat 2 (k + 1) : ℤ) := s2_succ k
  have hv : (0 : ℤ) ≤ (padicValNat 2 (k + 1) : ℤ) := Int.natCast_nonneg _
  unfold wZfun
  push_cast
  omega

lemma exists_GZ2 :
    ∃ L : ℚ_[2], Tendsto (fun m => ((RatZ m : ℚ) : ℚ_[2])) atTop (𝓝 L) ∧
      ∀ m, L - ((RatZ m : ℚ) : ℚ_[2]) ≠ 0 ∧
        Padic.valuation (L - ((RatZ m : ℚ) : ℚ_[2])) = wZfun m :=
  padic2_limit_of_strictMono_val RatZ_diff_ne_zero val_RatZ_diff wZfun_strictMono

/-- The `2`-adic limit `𝒢_{Z,2}` of the Zudilin row. -/
noncomputable def GZ2 : ℚ_[2] := exists_GZ2.choose

theorem tendsto_GZ2 : Tendsto (fun m => ((RatZ m : ℚ) : ℚ_[2])) atTop (𝓝 GZ2) :=
  exists_GZ2.choose_spec.1

theorem GZ2_sub_ne_zero (m : ℕ) : GZ2 - ((RatZ m : ℚ) : ℚ_[2]) ≠ 0 :=
  (exists_GZ2.choose_spec.2 m).1

/-- Equation (8.2): `v₂(𝒢_{Z,2} - P_m/Q_m) = 8m - 1 - 4 s₂(m)`. -/
theorem val_GZ2_sub (m : ℕ) :
    Padic.valuation (GZ2 - ((RatZ m : ℚ) : ℚ_[2])) = 8 * (m : ℤ) - 1 - 4 * (s2 m : ℤ) :=
  (exists_GZ2.choose_spec.2 m).2

/-! ### The modular `E` row -/

/-- `R^E_n = 2 B_n / A_n`. -/
noncomputable def RatE (n : ℕ) : ℚ := 2 * Be n / Ae n

/-- `w^E_n = 5n - 1 - 4 s₂(n)`, the valuation of the tail after index `n`. -/
def wEfun (n : ℕ) : ℤ := 5 * (n : ℤ) - 1 - 4 * (s2 n : ℤ)

lemma RatE_diff_eq (n : ℕ) : RatE (n + 1) - RatE n = (-2 * WE n) / (Ae (n + 1) * Ae n) := by
  unfold RatE WE
  have hA1 : Ae (n + 1) ≠ 0 := Ae_ne_zero (n + 1)
  have hA0 : Ae n ≠ 0 := Ae_ne_zero n
  field_simp
  ring

lemma RatE_diff_ne_zero (n : ℕ) : RatE (n + 1) - RatE n ≠ 0 := by
  rw [RatE_diff_eq]
  exact div_ne_zero (mul_ne_zero (by norm_num) (WE_ne_zero n))
    (mul_ne_zero (Ae_ne_zero (n + 1)) (Ae_ne_zero n))

lemma val_RatE_diff (n : ℕ) : padicValRat 2 (RatE (n + 1) - RatE n) = wEfun n := by
  have h := val_E_ratio_diff n
  have hs : (s2 (n + 1) : ℤ) = (s2 n : ℤ) + 1 - (padicValNat 2 (n + 1) : ℤ) := s2_succ n
  unfold RatE wEfun
  rw [h]
  omega

lemma wEfun_strictMono : StrictMono wEfun := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  have hs : (s2 (n + 1) : ℤ) = (s2 n : ℤ) + 1 - (padicValNat 2 (n + 1) : ℤ) := s2_succ n
  have hv : (0 : ℤ) ≤ (padicValNat 2 (n + 1) : ℤ) := Int.natCast_nonneg _
  unfold wEfun
  push_cast
  omega

lemma exists_GE2 :
    ∃ L : ℚ_[2], Tendsto (fun n => ((RatE n : ℚ) : ℚ_[2])) atTop (𝓝 L) ∧
      ∀ n, L - ((RatE n : ℚ) : ℚ_[2]) ≠ 0 ∧
        Padic.valuation (L - ((RatE n : ℚ) : ℚ_[2])) = wEfun n :=
  padic2_limit_of_strictMono_val RatE_diff_ne_zero val_RatE_diff wEfun_strictMono

/-- The `2`-adic limit `𝒢_{E,2}` of the modular `E` row. -/
noncomputable def GE2 : ℚ_[2] := exists_GE2.choose

theorem tendsto_GE2 : Tendsto (fun n => ((RatE n : ℚ) : ℚ_[2])) atTop (𝓝 GE2) :=
  exists_GE2.choose_spec.1

theorem GE2_sub_ne_zero (n : ℕ) : GE2 - ((RatE n : ℚ) : ℚ_[2]) ≠ 0 :=
  (exists_GE2.choose_spec.2 n).1

/-- Equation (11.2): `v₂(𝒢_{E,2} - 2B_n/A_n) = 5n - 1 - 4 s₂(n)`. -/
theorem val_GE2_sub (n : ℕ) :
    Padic.valuation (GE2 - ((RatE n : ℚ) : ℚ_[2])) = 5 * (n : ℤ) - 1 - 4 * (s2 n : ℤ) :=
  (exists_GE2.choose_spec.2 n).2

/-- Equation (11.3): `v₂(𝒢_{E,2} - 2B_{2m}/A_{2m}) = 10m - 1 - 4 s₂(m)`. -/
theorem val_GE2_sub_two_mul (m : ℕ) :
    Padic.valuation (GE2 - ((RatE (2 * m) : ℚ) : ℚ_[2])) = 10 * (m : ℤ) - 1 - 4 * (s2 m : ℤ) := by
  rw [val_GE2_sub (2 * m), s2_two_mul m]
  push_cast
  ring

end Catalan
