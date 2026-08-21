import Mathlib

/-!
# Binary digit identities (Section 3 of the source note)

`s₂ n` is the sum of the binary digits of `n`.  We prove the two identities

* `s₂ (m - 1) = s₂ m - 1 + v₂ m`   (for `m ≥ 1`),
* `s₂ (m + 1) = s₂ m + 1 - v₂ (m+1)`,

stated over `ℤ` to avoid truncated subtraction, together with `s₂ (2 m) = s₂ m`.
-/

namespace Catalan

open Nat

/-- Sum of the binary digits of `n`. -/
def s2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

@[simp] lemma s2_zero : s2 0 = 0 := rfl

@[simp] lemma s2_one : s2 1 = 1 := rfl

lemma s2_le (n : ℕ) : s2 n ≤ n := Nat.digit_sum_le 2 n

/-- Legendre's formula in base two: `v₂ (n !) = n - s₂ n`. -/
lemma padicValNat_two_factorial (n : ℕ) : padicValNat 2 (n !) = n - s2 n := by
  have := sub_one_mul_padicValNat_factorial (p := 2) n
  simpa [s2] using this

/-- Equation (3.2): `s₂ (m+1) = s₂ m + 1 - v₂ (m+1)`. -/
lemma s2_succ (m : ℕ) :
    (s2 (m + 1) : ℤ) = (s2 m : ℤ) + 1 - (padicValNat 2 (m + 1) : ℤ) := by
  have hfac : ((m + 1)! ) = (m + 1) * (m !) := Nat.factorial_succ m
  have hmul : padicValNat 2 ((m + 1)!) = padicValNat 2 (m + 1) + padicValNat 2 (m !) := by
    rw [hfac]
    exact padicValNat.mul (by omega) (Nat.factorial_ne_zero m)
  have h1 : padicValNat 2 ((m + 1)!) = (m + 1) - s2 (m + 1) := padicValNat_two_factorial _
  have h2 : padicValNat 2 (m !) = m - s2 m := padicValNat_two_factorial _
  have hle1 : s2 (m + 1) ≤ m + 1 := s2_le _
  have hle2 : s2 m ≤ m := s2_le _
  have hv : padicValNat 2 (m + 1) ≤ m + 1 := by
    have : (m + 1) - s2 (m + 1) ≤ m + 1 := by omega
    omega
  omega

/-- Equation (3.1): `s₂ (m-1) = s₂ m - 1 + v₂ m` for `m ≥ 1`. -/
lemma s2_pred (m : ℕ) (hm : 1 ≤ m) :
    (s2 (m - 1) : ℤ) = (s2 m : ℤ) - 1 + (padicValNat 2 m : ℤ) := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have := s2_succ k
  simp only [Nat.add_sub_cancel]
  omega

/-- Binary digit sum is invariant under doubling. -/
lemma s2_two_mul (m : ℕ) : s2 (2 * m) = s2 m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have hpos : 0 < 2 * m := by omega
    have : Nat.digits 2 (2 * m) = (2 * m) % 2 :: Nat.digits 2 ((2 * m) / 2) :=
      Nat.digits_def' (by norm_num) hpos
    simp [s2, this, Nat.mul_div_cancel_left m (by norm_num : 0 < 2),
      Nat.mul_mod_right]

/-- Appending a binary `1` increases the digit sum by one. -/
lemma s2_two_mul_add_one (m : ℕ) : s2 (2 * m + 1) = s2 m + 1 := by
  have hpos : 0 < 2 * m + 1 := by omega
  have hdigits : Nat.digits 2 (2 * m + 1) =
      (2 * m + 1) % 2 :: Nat.digits 2 ((2 * m + 1) / 2) :=
    Nat.digits_def' (by norm_num) hpos
  unfold s2
  rw [hdigits, show (2 * m + 1) / 2 = m by omega]
  norm_num
  omega

/-- Binary digit sums are subadditive.  The proof compares the `2`-adic
valuation of `(a+b)!` with those of `a!`, `b!`, and the binomial coefficient. -/
lemma s2_add_le (a b : ℕ) : s2 (a + b) ≤ s2 a + s2 b := by
  have hfac := Nat.add_choose_mul_factorial_mul_factorial a b
  have hchoose : (a + b).choose b ≠ 0 := Nat.choose_ne_zero (Nat.le_add_left b a)
  have hval : padicValNat 2 (Nat.factorial (a + b)) =
      padicValNat 2 ((a + b).choose b) + padicValNat 2 (Nat.factorial a) +
        padicValNat 2 (Nat.factorial b) := by
    rw [← hfac, padicValNat.mul (mul_ne_zero hchoose (Nat.factorial_ne_zero a))
      (Nat.factorial_ne_zero b), padicValNat.mul hchoose (Nat.factorial_ne_zero a)]
  rw [padicValNat_two_factorial, padicValNat_two_factorial,
    padicValNat_two_factorial] at hval
  have ha := s2_le a
  have hb := s2_le b
  have hab := s2_le (a + b)
  omega

end Catalan
