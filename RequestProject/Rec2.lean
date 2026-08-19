import Mathlib

/-!
# Generic second order recurrences and a small `2`-adic valuation API

`rec2 L C R z₀ z₁` is the solution of

`L m * z (m+1) = C m * z m + R m * z (m-1)`   (`m ≥ 1`)

with prescribed initial values `z 0 = z₀`, `z 1 = z₁`.

We also collect a handful of lemmas about `padicValRat 2` that are used repeatedly.
-/

namespace Catalan

/-- Solution of the two-term recurrence `L m * z (m+1) = C m * z m + R m * z (m-1)`
(`m ≥ 1`) with initial data `z 0 = z₀`, `z 1 = z₁`. -/
def rec2 (L C R : ℕ → ℚ) (z0 z1 : ℚ) : ℕ → ℚ
  | 0 => z0
  | 1 => z1
  | (m + 2) => (C (m + 1) * rec2 L C R z0 z1 (m + 1) + R (m + 1) * rec2 L C R z0 z1 m) / L (m + 1)

@[simp] lemma rec2_zero (L C R : ℕ → ℚ) (z0 z1 : ℚ) : rec2 L C R z0 z1 0 = z0 := rfl

@[simp] lemma rec2_one (L C R : ℕ → ℚ) (z0 z1 : ℚ) : rec2 L C R z0 z1 1 = z1 := rfl

lemma rec2_add_two (L C R : ℕ → ℚ) (z0 z1 : ℚ) (m : ℕ) :
    rec2 L C R z0 z1 (m + 2) =
      (C (m + 1) * rec2 L C R z0 z1 (m + 1) + R (m + 1) * rec2 L C R z0 z1 m) / L (m + 1) := rfl

/-- The defining recurrence, in cleared-denominator form. -/
lemma rec2_rec (L C R : ℕ → ℚ) (z0 z1 : ℚ) (m : ℕ) (hL : L (m + 1) ≠ 0) :
    L (m + 1) * rec2 L C R z0 z1 (m + 2) =
      C (m + 1) * rec2 L C R z0 z1 (m + 1) + R (m + 1) * rec2 L C R z0 z1 m := by
  rw [rec2_add_two, mul_div_cancel₀ _ hL]

/-- A sequence satisfying the same recurrence and the same initial data as `rec2` is `rec2`. -/
lemma rec2_unique (L C R : ℕ → ℚ) (z0 z1 : ℚ) (u : ℕ → ℚ) (h0 : u 0 = z0) (h1 : u 1 = z1)
    (hL : ∀ m, L (m + 1) ≠ 0)
    (hrec : ∀ m, L (m + 1) * u (m + 2) = C (m + 1) * u (m + 1) + R (m + 1) * u m) :
    ∀ n, u n = rec2 L C R z0 z1 n := by
  have key : ∀ n, u n = rec2 L C R z0 z1 n ∧ u (n + 1) = rec2 L C R z0 z1 (n + 1) := by
    intro n
    induction n with
    | zero => exact ⟨by simpa using h0, by simpa using h1⟩
    | succ k ih =>
        refine ⟨ih.2, ?_⟩
        have h := hrec k
        rw [ih.1, ih.2] at h
        have h' := rec2_rec L C R z0 z1 k (hL k)
        exact mul_left_cancel₀ (hL k) (by rw [h, h'])
  exact fun n => (key n).1

/-! ### `2`-adic valuation helpers -/

lemma padicValRat_two_natCast (n : ℕ) :
    padicValRat 2 (n : ℚ) = (padicValNat 2 n : ℤ) := by
  have h : ((n : ℤ) : ℚ) = (n : ℚ) := by push_cast; ring
  rw [← h, padicValRat.of_int]
  simp [padicValInt]

lemma padicValRat_two_of_odd_int {k : ℤ} (hk : Odd k) : padicValRat 2 (k : ℚ) = 0 := by
  have hv : padicValInt 2 k = 0 := by
    unfold padicValInt
    refine padicValNat.eq_zero_of_not_dvd ?_
    have : k.natAbs % 2 = 1 := Nat.odd_iff.mp (Int.natAbs_odd.mpr hk)
    omega
  rw [padicValRat.of_int, hv]
  simp

lemma padicValRat_two_two_pow (k : ℕ) : padicValRat 2 ((2 : ℚ) ^ k) = k := by
  rw [padicValRat.pow]
  have h2 : ((2 : ℕ) : ℚ) = (2 : ℚ) := by norm_num
  rw [← h2, padicValRat_two_natCast]
  simp

/-- Generic induction step for the exact `2`-adic valuation of a solution of a two-term
recurrence: if the middle term has strictly smaller valuation than the trailing term, there is
no cancellation and the valuation of the new term is forced. -/
lemma padicValRat_two_rec_step {L C R x y w : ℚ}
    (hrec : L * w = C * y + R * x)
    (hL : L ≠ 0) (hC : C ≠ 0) (hR : R ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0)
    (hlt : padicValRat 2 C + padicValRat 2 y < padicValRat 2 R + padicValRat 2 x) :
    w ≠ 0 ∧ padicValRat 2 w = padicValRat 2 C + padicValRat 2 y - padicValRat 2 L := by
  have ha : C * y ≠ 0 := mul_ne_zero hC hy
  have hb : R * x ≠ 0 := mul_ne_zero hR hx
  have hva : padicValRat 2 (C * y) = padicValRat 2 C + padicValRat 2 y := padicValRat.mul hC hy
  have hvb : padicValRat 2 (R * x) = padicValRat 2 R + padicValRat 2 x := padicValRat.mul hR hx
  have hvlt : padicValRat 2 (C * y) < padicValRat 2 (R * x) := by rw [hva, hvb]; exact hlt
  have hsum : C * y + R * x ≠ 0 := by
    intro h
    have : R * x = -(C * y) := by linarith [h]
    rw [this, padicValRat.neg] at hvlt
    exact lt_irrefl _ hvlt
  have hvsum : padicValRat 2 (C * y + R * x) = padicValRat 2 (C * y) :=
    padicValRat.add_eq_of_lt hsum ha hb hvlt
  have hw : w = (C * y + R * x) / L := by
    field_simp at hrec ⊢
    linarith [hrec]
  refine ⟨?_, ?_⟩
  · rw [hw]
    exact div_ne_zero hsum hL
  · rw [hw, padicValRat.div hsum hL, hvsum, hva]

end Catalan
