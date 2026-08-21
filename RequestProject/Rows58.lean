import RequestProject.Plucker58
import RequestProject.EIntegrality
import RequestProject.EIntegralityB
import RequestProject.ZIntegrality
import RequestProject.Y2Integrality

/-!
# The `5 : 8` integer rows and their dyadic cross divisor

The improved construction samples the Zudilin row at index `5n` and the modular `E`-row at index
`8n`, over the common lcm square `S_n = D_{10n}²`:

* modular row : `X₁ n = S_n A_{8n}`, `Y₁ n = 2 S_n B_{8n}`;
* Zudilin row : `X₂ n = 2^{e_{5n}} S_n Q_{5n}`, `Y₂ n = 2^{e_{5n}} S_n P_{5n}`.

All four entries are integers (`EIntegrality.lean`, `EIntegralityB.lean`, `ZIntegrality.lean`
and the general clearing statement of `Y2Integrality.lean`), and the reduced cross determinant

`a₁ Y₂ - a₂ Y₁ = 2^{e_{5n}} S_n (P_{5n} A_{8n} - 2 B_{8n} Q_{5n})`

is divisible by `T_n = 2^{40n - 3 - 2⌊log₂(5n)⌋}`, by the off-diagonal cross bound
`val_Delta58_ge` of `Plucker58.lean` together with `e_{5n} ≥ 20n`.
-/

namespace Catalan

/-! ### The clearing exponent at index `5n` -/

/-- `e_{5n} ≥ 4·(5n)`, which is what the denominator row needs. -/
lemma eZud_five_mul_lb (n : ℕ) : 4 * (5 * n) ≤ eZud (5 * n) := by
  have h := Nat.zero_le (Nat.log 2 (2 * (5 * n) - 1))
  simp only [eZud, le_min_iff]
  omega

/-- `e_{5n} ≥ 4·(5n) + 3` for `n ≥ 1`, which is what the numerator row needs. -/
lemma eZud_five_mul_ge (n : ℕ) (hn : 1 ≤ n) : 4 * (5 * n) + 3 ≤ eZud (5 * n) := by
  have h := Nat.zero_le (Nat.log 2 (2 * (5 * n) - 1))
  simp only [eZud, le_min_iff]
  omega

/-! ### The rows -/

/-- The common lcm square `S_n = D_{10n}²` of the `5 : 8` construction. -/
def Sfac58 (n : ℕ) : ℕ := (Dlcm (10 * n)) ^ 2

lemma Sfac58_pos (n : ℕ) : 0 < Sfac58 n := by
  have := Dlcm_pos (10 * n)
  unfold Sfac58
  positivity

/-- The dyadic divisor exponent `40n - 3 - 2⌊log₂(5n)⌋`. -/
def Texp58 (n : ℕ) : ℕ := 40 * n - 3 - 2 * Nat.log 2 (5 * n)

lemma Texp58_le (n : ℕ) (hn : 1 ≤ n) :
    (Texp58 n : ℤ) = 40 * (n : ℤ) - 3 - 2 * (Nat.log 2 (5 * n) : ℤ) := by
  have h : Nat.log 2 (5 * n) ≤ 5 * n := Nat.log_le_self 2 (5 * n)
  have : 3 + 2 * Nat.log 2 (5 * n) ≤ 40 * n := by omega
  unfold Texp58
  omega

/-- The modular denominator row `a₁ n = A_{8n}`. -/
def a1row58 (n : ℕ) : ℤ := AeInt (8 * n)

@[simp] lemma a1row58_cast (n : ℕ) : ((a1row58 n : ℤ) : ℚ) = Ae (8 * n) := AeInt_cast (8 * n)

/-- The Zudilin denominator row `a₂ n = 2^{e_{5n}} Q_{5n}`. -/
noncomputable def a2row58 (n : ℕ) : ℤ :=
  Classical.choose (two_pow_mul_Qz_isInt (5 * n) (eZud (5 * n)) (eZud_five_mul_lb n))

lemma a2row58_cast (n : ℕ) : ((a2row58 n : ℤ) : ℚ) = 2 ^ (eZud (5 * n)) * Qz (5 * n) :=
  Classical.choose_spec (two_pow_mul_Qz_isInt (5 * n) (eZud (5 * n)) (eZud_five_mul_lb n))

/-- `D_M² B_N` is an integer as soon as `N ≤ M`. -/
lemma Dlcm_sq_mul_Be_isInt' (N M : ℕ) (h : N ≤ M) :
    ∃ z : ℤ, (z : ℚ) = (Dlcm M : ℚ) ^ 2 * Be N := by
  obtain ⟨z, hz⟩ := Dlcm_sq_mul_Be_isInt N
  obtain ⟨t, ht⟩ := Dlcm_dvd_Dlcm h
  refine ⟨(t : ℤ) ^ 2 * z, ?_⟩
  have hD : (Dlcm M : ℚ) = (Dlcm N : ℚ) * (t : ℚ) := by
    exact_mod_cast congrArg (fun s : ℕ => (s : ℚ)) ht
  push_cast
  rw [hz, hD]
  ring

lemma Y1row58_isInt (n : ℕ) :
    ∃ z : ℤ, (z : ℚ) = 2 * ((Sfac58 n : ℕ) : ℚ) * Be (8 * n) := by
  obtain ⟨z, hz⟩ := Dlcm_sq_mul_Be_isInt' (8 * n) (10 * n) (by omega)
  refine ⟨2 * z, ?_⟩
  have hS : ((Sfac58 n : ℕ) : ℚ) = (Dlcm (10 * n) : ℚ) ^ 2 := by
    unfold Sfac58
    push_cast
    ring
  rw [hS]
  push_cast
  linarith [hz]

lemma Y2row58_isInt (n : ℕ) :
    ∃ z : ℤ, (z : ℚ) = 2 ^ (eZud (5 * n)) * ((Sfac58 n : ℕ) : ℚ) * Pz (5 * n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, ?_⟩
    have hP : Pz 0 = 0 := by simp
    simp [hP]
  · obtain ⟨z, hz⟩ := two_pow_mul_Dlcm_sq_mul_Pz_isInt (5 * n) (eZud (5 * n)) (10 * n)
      (eZud_five_mul_ge n hn) (by omega) (by omega)
    refine ⟨z, ?_⟩
    rw [hz, Sfac58]
    push_cast
    ring

/-- The modular numerator row `Y₁ n = 2 S_n B_{8n}`. -/
noncomputable def y1row58 (n : ℕ) : ℤ := Classical.choose (Y1row58_isInt n)

lemma y1row58_cast (n : ℕ) :
    ((y1row58 n : ℤ) : ℚ) = 2 * ((Sfac58 n : ℕ) : ℚ) * Be (8 * n) :=
  Classical.choose_spec (Y1row58_isInt n)

/-- The Zudilin numerator row `Y₂ n = 2^{e_{5n}} S_n P_{5n}`. -/
noncomputable def y2row58 (n : ℕ) : ℤ := Classical.choose (Y2row58_isInt n)

lemma y2row58_cast (n : ℕ) :
    ((y2row58 n : ℤ) : ℚ) = 2 ^ (eZud (5 * n)) * ((Sfac58 n : ℕ) : ℚ) * Pz (5 * n) :=
  Classical.choose_spec (Y2row58_isInt n)

/-! ### The dyadic divisor of the reduced cross determinant -/

lemma hRed58_cast (n : ℕ) :
    ((a1row58 n * y2row58 n - a2row58 n * y1row58 n : ℤ) : ℚ)
      = 2 ^ (eZud (5 * n)) * ((Sfac58 n : ℕ) : ℚ) * Delta58 n := by
  push_cast [a1row58_cast n, a2row58_cast n, y1row58_cast n, y2row58_cast n]
  rw [Delta58]
  ring

lemma padicValRat_Sfac58_nonneg (n : ℕ) : 0 ≤ padicValRat 2 ((Sfac58 n : ℕ) : ℚ) := by
  rw [show (((Sfac58 n : ℕ) : ℚ)) = ((Sfac58 n : ℤ) : ℚ) by push_cast; ring, padicValRat.of_int]
  positivity

/-- **The dyadic divisor of the `5 : 8` cross determinant**: `2^{40n-3-2⌊log₂(5n)⌋}` divides
`a₁ Y₂ - a₂ Y₁`. -/
theorem dvd_reduced_cross58 (n : ℕ) :
    (2 : ℤ) ^ (Texp58 n) ∣ a1row58 n * y2row58 n - a2row58 n * y1row58 n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Texp58]
  set z : ℤ := a1row58 n * y2row58 n - a2row58 n * y1row58 n with hzdef
  by_cases hD : Delta58 n = 0
  · have : (z : ℚ) = 0 := by rw [hzdef, hRed58_cast n, hD, mul_zero]
    have hz0 : z = 0 := by exact_mod_cast this
    simp [hz0]
  · have hS : ((Sfac58 n : ℕ) : ℚ) ≠ 0 := by
      have := Sfac58_pos n
      positivity
    have hval : (Texp58 n : ℤ) ≤ padicValRat 2 ((z : ℚ)) := by
      rw [hzdef, hRed58_cast n, padicValRat.mul (by positivity) hD,
        padicValRat.mul (by positivity : ((2 : ℚ) ^ (eZud (5 * n))) ≠ 0) hS,
        padicValRat_two_pow]
      have h1 := val_Delta58_ge n hn hD
      have h2 := padicValRat_Sfac58_nonneg n
      have h3 : (4 : ℤ) * (5 * n) ≤ (eZud (5 * n) : ℤ) := by
        exact_mod_cast eZud_five_mul_lb n
      have h4 := Texp58_le n hn
      push_cast at h3 ⊢
      omega
    rw [padicValRat.of_int] at hval
    have hle : Texp58 n ≤ padicValInt 2 z := by exact_mod_cast hval
    exact (padicValInt_dvd_iff (p := 2) (Texp58 n) z).mpr (Or.inr hle)

end Catalan
