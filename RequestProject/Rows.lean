import RequestProject.CrossIdentity
import RequestProject.LcmRow

/-!
# The two integer rows and the unconditional `2^{24n}` Plücker divisor

Sections 15 and 18 of the base note, i.e. Section 9 of the unconditional note.

With `S n = D(6n)²` the common integral factor and `e` the `2`-adic clearing exponents of the
Zudilin row, the two rows are

* modular `E`-row  : `X₁ n = S n · A_{6n}`, `Y₁ n = 2 S n · B_{6n}`;
* Zudilin row      : `X₂ n = 2^{e_{3n}} S n · Q_{3n}`, `Y₂ n = 2^{e_{3n}} S n · P_{3n}`,

and their cross determinant is

`h n = X₁ n · Y₂ n - X₂ n · Y₁ n = 2^{e_{3n}} (S n)² (P_{3n} A_{6n} - 2 B_{6n} Q_{3n})`,

equation (9.1).  Combining the exact Plücker valuation `v₂(P_m A_{2m} - 2B_{2m}Q_m) = 4m - 1`
(Theorem 8.1, proved unconditionally in `CrossIdentity.lean`) with the clearing bound
`e_{3n} ≥ 12n + 1` quoted from the base note gives `v₂(h n) ≥ 24 n`, equation (9.4).
-/

namespace Catalan

/-- The modular `E`-row denominator `X₁ n = S n · A_{6n}`. -/
noncomputable def X1row (n : ℕ) : ℚ := (Sfac n : ℚ) * Ae (6 * n)

/-- The modular `E`-row numerator `Y₁ n = 2 S n · B_{6n}`. -/
noncomputable def Y1row (n : ℕ) : ℚ := 2 * (Sfac n : ℚ) * Be (6 * n)

/-- The Zudilin-row denominator `X₂ n = 2^{e_{3n}} S n · Q_{3n}`. -/
noncomputable def X2row (e : ℕ → ℕ) (n : ℕ) : ℚ :=
  2 ^ (e (3 * n)) * (Sfac n : ℚ) * Qz (3 * n)

/-- The Zudilin-row numerator `Y₂ n = 2^{e_{3n}} S n · P_{3n}`. -/
noncomputable def Y2row (e : ℕ → ℕ) (n : ℕ) : ℚ :=
  2 ^ (e (3 * n)) * (Sfac n : ℚ) * Pz (3 * n)

/-- The cross determinant `h n = X₁ n Y₂ n - X₂ n Y₁ n` of the two rows, equation (9.1). -/
noncomputable def hRow (e : ℕ → ℕ) (n : ℕ) : ℚ := X1row n * Y2row e n - X2row e n * Y1row n

/-- The reduced cross determinant `h n / S n = a₁ Y₂ - a₂ Y₁`, where `aᵢ = Xᵢ / S` are the
first coordinates divided by the common factor `S n`.  This is the quantity `h` of Lemma 20.1
of the base note. -/
noncomputable def hRed (e : ℕ → ℕ) (n : ℕ) : ℚ :=
  Ae (6 * n) * Y2row e n - (2 ^ (e (3 * n)) * Qz (3 * n)) * Y1row n

lemma Dlcm_pos (N : ℕ) : 0 < Dlcm N :=
  Nat.pos_of_ne_zero (by simp [Dlcm, Finset.lcm_eq_zero_iff])

lemma Sfac_pos (n : ℕ) : 0 < Sfac n := by
  have := Dlcm_pos (6 * n)
  unfold Sfac
  positivity

/-- Equation (9.1): the cross determinant factors through the Plücker combination. -/
lemma hRow_eq (e : ℕ → ℕ) (n : ℕ) :
    hRow e n = 2 ^ (e (3 * n)) * (Sfac n : ℚ) ^ 2 *
      (Pz (3 * n) * Ae (2 * (3 * n)) - 2 * Be (2 * (3 * n)) * Qz (3 * n)) := by
  unfold hRow X1row Y1row X2row Y2row
  rw [show 2 * (3 * n) = 6 * n by ring]
  ring

/-- The reduced cross determinant factors in the same way, with one factor `S n` less. -/
lemma hRed_eq (e : ℕ → ℕ) (n : ℕ) :
    hRed e n = 2 ^ (e (3 * n)) * (Sfac n : ℚ) *
      (Pz (3 * n) * Ae (2 * (3 * n)) - 2 * Be (2 * (3 * n)) * Qz (3 * n)) := by
  unfold hRed Y1row Y2row
  rw [show 2 * (3 * n) = 6 * n by ring]
  ring

lemma hRow_eq_Sfac_mul_hRed (e : ℕ → ℕ) (n : ℕ) : hRow e n = (Sfac n : ℚ) * hRed e n := by
  rw [hRow_eq, hRed_eq]; ring



lemma plucker_ne_zero (n : ℕ) (hn : 1 ≤ n) :
    Pz (3 * n) * Ae (2 * (3 * n)) - 2 * Be (2 * (3 * n)) * Qz (3 * n) ≠ 0 := by
  have hm : 1 ≤ 3 * n := by omega
  have hplu := val_plucker_uncond (3 * n) hm
  intro hz
  rw [hz, padicValRat.zero] at hplu
  have : (1 : ℤ) ≤ (3 * n : ℕ) := by exact_mod_cast hm
  omega

lemma padicValRat_Sfac_nonneg (n : ℕ) : 0 ≤ padicValRat 2 ((Sfac n : ℚ)) := by
  rw [show ((Sfac n : ℚ)) = ((Sfac n : ℤ) : ℚ) by push_cast; ring, padicValRat.of_int]
  positivity

lemma padicValRat_two_pow (k : ℕ) : padicValRat 2 ((2 : ℚ) ^ k) = (k : ℤ) := by
  have hself : padicValRat 2 (2 : ℚ) = 1 := by
    simpa using padicValRat.self (p := 2) (by norm_num)
  rw [padicValRat.pow, hself, mul_one]

/-- Equations (9.3)–(9.4) for the reduced determinant: with the base-note clearing bound
`e_{3n} ≥ 12n + 1` one has `v₂(h n / S n) ≥ 24 n`. -/
theorem val_hRed_ge (e : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n) (he : 12 * n + 1 ≤ e (3 * n)) :
    24 * (n : ℤ) ≤ padicValRat 2 (hRed e n) := by
  have hm : 1 ≤ 3 * n := by omega
  have hplu := val_plucker_uncond (3 * n) hm
  have hpne := plucker_ne_zero n hn
  have hS : ((Sfac n : ℚ)) ≠ 0 := by
    have := Sfac_pos n
    positivity
  have h2 : ((2 : ℚ) ^ (e (3 * n))) ≠ 0 := by positivity
  have hvalS := padicValRat_Sfac_nonneg n
  rw [hRed_eq, padicValRat.mul (by positivity) hpne,
    padicValRat.mul h2 hS, padicValRat_two_pow, hplu]
  have hnn : (12 : ℤ) * n + 1 ≤ (e (3 * n) : ℤ) := by exact_mod_cast he
  push_cast
  omega

/-- Equation (9.4): the cross determinant of the two rows satisfies `v₂(h n) ≥ 24 n`. -/
theorem val_hRow_ge (e : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n) (he : 12 * n + 1 ≤ e (3 * n)) :
    24 * (n : ℤ) ≤ padicValRat 2 (hRow e n) := by
  have hS : ((Sfac n : ℚ)) ≠ 0 := by
    have := Sfac_pos n
    positivity
  have hred : hRed e n ≠ 0 := by
    rw [hRed_eq]
    exact mul_ne_zero (by positivity) (plucker_ne_zero n hn)
  rw [hRow_eq_Sfac_mul_hRed, padicValRat.mul hS hred]
  have := padicValRat_Sfac_nonneg n
  have := val_hRed_ge e n hn he
  omega

/-- Equation (18.5): `T_n = 2^{24n}` divides the reduced cross determinant, as an integer
divisibility once the row entries are known to be integers. -/
theorem two_pow_dvd_hRed (e : ℕ → ℕ) (n : ℕ) (hn : 1 ≤ n) (he : 12 * n + 1 ≤ e (3 * n))
    (z : ℤ) (hz : (z : ℚ) = hRed e n) : (2 : ℤ) ^ (24 * n) ∣ z := by
  have hval := val_hRed_ge e n hn he
  rw [← hz, padicValRat.of_int] at hval
  have : 24 * n ≤ padicValInt 2 z := by exact_mod_cast hval
  exact (padicValInt_dvd_iff (p := 2) (24 * n) z).mpr (Or.inr this)


end Catalan
