import RequestProject.Assembly
import RequestProject.Plucker58

/-!
# The Nesterenko × Zudilin cross determinant

Sections 17–20 of the near-critical dossier, proved here rather than imported.

The imported Nesterenko `2`-adic material is collected in `NesterenkoPadicInputs`:

* the two rational rows `B_n`, `C_n` of the Nesterenko `(4,7)` realization, together with
  their integer normalizations `a_n = 4^{7n+1} B_n` and `Y_n = 4^{7n} D_{6n}² C_n`;
* the exact valuation `v₂(4 B_n) = 3 + s₂(n) + s₂(3n) - 14n`  (Section 14);
* the slope-`28` tail theorem `v₂(𝒢₂ - C_n/(4B_n)) = 28n - 1 - 2 s₂(n) - 2 s₂(3n)`
  (Section 15), where `𝒢₂` is the `2`-adic Catalan period `GZ2` of the project.

Everything after that is proved:

* `val_ratio_cross_N` (17.1): the two `2`-adic errors have different valuations, so by the
  ultrametric equality `v₂(C_n/(4B_n) - P_{3n}/Q_{3n}) = 24n - 1 - 4 s₂(3n)`;
* `val_DeltaN` (18.1): `v₂(4 B_n P_{3n} - C_n Q_{3n}) = -2n + 2 + s₂(n) - s₂(3n)`;
* `dvd_reduced_cross_N` (20.3): `2^{24n}` divides the reduced cross determinant
  `a₁ Y₂ - a₂ Y₁` of the Zudilin and Nesterenko rows.

The last step uses the exact clearing exponent `e_{3n} ≥ 12n + 3 + ⌊log₂ 3n⌋` together with the
binary-digit bound `s₂(m) ≤ ⌊log₂ m⌋ + 1`.
-/

namespace Catalan

open Filter Topology

/-! ### The imported `2`-adic Nesterenko package -/

/-- The imported `2`-adic data of the Nesterenko `(4,7)` realization. -/
structure NesterenkoPadicInputs where
  /-- The Nesterenko denominator sequence `B_n`. -/
  BN : ℕ → ℚ
  /-- The Nesterenko numerator sequence `C_n`. -/
  CN : ℕ → ℚ
  /-- The integer normalization `a_n = 4^{7n+1} B_n` of the denominator row. -/
  aN : ℕ → ℤ
  /-- The integer normalization `Y_n = 4^{7n} D_{6n}² C_n` of the numerator row. -/
  yN : ℕ → ℤ
  BN_ne_zero : ∀ n, 1 ≤ n → BN n ≠ 0
  aN_eq : ∀ n, ((aN n : ℤ) : ℚ) = 4 ^ (7 * n + 1) * BN n
  yN_eq : ∀ n, ((yN n : ℤ) : ℚ) = 4 ^ (7 * n) * (Sfac n : ℚ) * CN n
  /-- Section 14: `v₂(4 B_n) = 3 + s₂(n) + s₂(3n) - 14n`. -/
  val_four_BN : ∀ n, 1 ≤ n →
    padicValRat 2 (4 * BN n) = 3 + (s2 n : ℤ) + (s2 (3 * n) : ℤ) - 14 * (n : ℤ)
  /-- The Nesterenko row converges `2`-adically to the Catalan period `𝒢₂`. -/
  tail_ne_zero : ∀ n, 1 ≤ n → GZ2 - ((CN n / (4 * BN n) : ℚ) : ℚ_[2]) ≠ 0
  /-- Section 15, the slope-`28` theorem:
  `v₂(𝒢₂ - C_n/(4B_n)) = 28n - 1 - 2 s₂(n) - 2 s₂(3n)`. -/
  val_tail : ∀ n, 1 ≤ n →
    Padic.valuation (GZ2 - ((CN n / (4 * BN n) : ℚ) : ℚ_[2]))
      = 28 * (n : ℤ) - 1 - 2 * (s2 n : ℤ) - 2 * (s2 (3 * n) : ℤ)

namespace NesterenkoPadicInputs

variable (N : NesterenkoPadicInputs)

/-- The Nesterenko rational approximation `R^N_n = C_n/(4B_n)`. -/
noncomputable def RatN (n : ℕ) : ℚ := N.CN n / (4 * N.BN n)

/-! ### Section 17: the exact cross-ratio valuation -/

/-- Equation (17.1): the Nesterenko and Zudilin `2`-adic errors have different valuations, so
their difference has the smaller of the two valuations. -/
theorem val_ratio_cross_N (n : ℕ) (hn : 1 ≤ n) :
    padicValRat 2 (N.RatN n - RatZ (3 * n)) = 24 * (n : ℤ) - 1 - 4 * (s2 (3 * n) : ℤ) := by
  set x : ℚ_[2] := GZ2 - ((RatZ (3 * n) : ℚ) : ℚ_[2]) with hx
  set y : ℚ_[2] := -(GZ2 - ((N.RatN n : ℚ) : ℚ_[2])) with hy
  have hxne : x ≠ 0 := GZ2_sub_ne_zero (3 * n)
  have hyne : y ≠ 0 := neg_ne_zero.mpr (N.tail_ne_zero n hn)
  have hvx : Padic.valuation x = 24 * (n : ℤ) - 1 - 4 * (s2 (3 * n) : ℤ) := by
    rw [hx, val_GZ2_sub (3 * n)]
    push_cast
    ring
  have hvy : Padic.valuation y
      = 28 * (n : ℤ) - 1 - 2 * (s2 n : ℤ) - 2 * (s2 (3 * n) : ℤ) := by
    rw [hy]
    simp only [RatN]
    rw [padic2_valuation_neg (N.tail_ne_zero n hn)]
    exact N.val_tail n hn
  have hlt : Padic.valuation x < Padic.valuation y := by
    rw [hvx, hvy]
    have h1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    have h2 : (s2 n : ℤ) ≤ (n : ℤ) := by exact_mod_cast s2_le n
    have h3 : (0 : ℤ) ≤ (s2 (3 * n) : ℤ) := by positivity
    omega
  obtain ⟨hne, hval⟩ := padic2_valuation_add_of_lt hxne hyne hlt
  have hsum : x + y = ((N.RatN n - RatZ (3 * n) : ℚ) : ℚ_[2]) := by
    rw [hx, hy]
    push_cast
    ring
  rw [hsum, Padic.valuation_ratCast] at hval
  rw [hval, hvx]

/-- The Nesterenko and Zudilin approximations are distinct. -/
lemma ratio_cross_N_ne_zero (n : ℕ) (hn : 1 ≤ n) : N.RatN n - RatZ (3 * n) ≠ 0 := by
  intro h
  have hv := N.val_ratio_cross_N n hn
  rw [h, padicValRat.zero] at hv
  have h1 : (1 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
  have h2 : (s2 (3 * n) : ℤ) ≤ (3 * n : ℤ) := by
    have := s2_le (3 * n)
    exact_mod_cast this
  omega

/-! ### Section 18: the raw cross determinant -/

/-- The raw cross determinant `Δ_n = 4 B_n P_{3n} - C_n Q_{3n}`. -/
noncomputable def DeltaN (n : ℕ) : ℚ := 4 * N.BN n * Pz (3 * n) - N.CN n * Qz (3 * n)

lemma DeltaN_factor (n : ℕ) (hn : 1 ≤ n) :
    N.DeltaN n = -((4 * N.BN n) * Qz (3 * n) * (N.RatN n - RatZ (3 * n))) := by
  have hB : N.BN n ≠ 0 := N.BN_ne_zero n hn
  have hQ : Qz (3 * n) ≠ 0 := Qz_ne_zero (3 * n)
  unfold DeltaN RatN RatZ
  field_simp
  ring

/-- Equation (18.1): `v₂(4 B_n P_{3n} - C_n Q_{3n}) = -2n + 2 + s₂(n) - s₂(3n)`. -/
theorem val_DeltaN (n : ℕ) (hn : 1 ≤ n) :
    padicValRat 2 (N.DeltaN n) = -2 * (n : ℤ) + 2 + (s2 n : ℤ) - (s2 (3 * n) : ℤ) := by
  have hB : N.BN n ≠ 0 := N.BN_ne_zero n hn
  have h4B : (4 : ℚ) * N.BN n ≠ 0 := by
    simpa using mul_ne_zero (by norm_num : (4:ℚ) ≠ 0) hB
  have hQ : Qz (3 * n) ≠ 0 := Qz_ne_zero (3 * n)
  have hd : N.RatN n - RatZ (3 * n) ≠ 0 := N.ratio_cross_N_ne_zero n hn
  rw [N.DeltaN_factor n hn, padicValRat.neg,
    padicValRat.mul (mul_ne_zero h4B hQ) hd, padicValRat.mul h4B hQ,
    N.val_four_BN n hn, val_Qz (3 * n), N.val_ratio_cross_N n hn]
  push_cast
  ring

lemma DeltaN_ne_zero (n : ℕ) (hn : 1 ≤ n) : N.DeltaN n ≠ 0 := by
  have hB : N.BN n ≠ 0 := N.BN_ne_zero n hn
  have h4B : (4 : ℚ) * N.BN n ≠ 0 := by
    simpa using mul_ne_zero (by norm_num : (4:ℚ) ≠ 0) hB
  have hQ : Qz (3 * n) ≠ 0 := Qz_ne_zero (3 * n)
  have hd : N.RatN n - RatZ (3 * n) ≠ 0 := N.ratio_cross_N_ne_zero n hn
  rw [N.DeltaN_factor n hn]
  simpa using mul_ne_zero (mul_ne_zero h4B hQ) hd

end NesterenkoPadicInputs

/-! ### The tail valuation from the valuation of the linear form -/

/-- A more primitive form of the imported `2`-adic Nesterenko package: instead of the tail
`𝒢₂ - C_n/(4B_n)` one gives the valuation of the *linear form* `J_n = 4 B_n 𝒢₂ - C_n`, which is
what Sections 11–13 of the dossier compute from the hypergeometric representation (the
hypergeometric factor being a `2`-adic unit, `v₂(J_n) = 14n + 2 - s₂(n) - s₂(3n)`). -/
structure NesterenkoFormInputs where
  /-- The Nesterenko denominator sequence `B_n`. -/
  BN : ℕ → ℚ
  /-- The Nesterenko numerator sequence `C_n`. -/
  CN : ℕ → ℚ
  /-- The integer normalization `a_n = 4^{7n+1} B_n` of the denominator row. -/
  aN : ℕ → ℤ
  /-- The integer normalization `Y_n = 4^{7n} D_{6n}² C_n` of the numerator row. -/
  yN : ℕ → ℤ
  BN_ne_zero : ∀ n, 1 ≤ n → BN n ≠ 0
  aN_eq : ∀ n, ((aN n : ℤ) : ℚ) = 4 ^ (7 * n + 1) * BN n
  yN_eq : ∀ n, ((yN n : ℤ) : ℚ) = 4 ^ (7 * n) * (Sfac n : ℚ) * CN n
  /-- Section 14: `v₂(4 B_n) = 3 + s₂(n) + s₂(3n) - 14n`. -/
  val_four_BN : ∀ n, 1 ≤ n →
    padicValRat 2 (4 * BN n) = 3 + (s2 n : ℤ) + (s2 (3 * n) : ℤ) - 14 * (n : ℤ)
  /-- The linear form `J_n = 4 B_n 𝒢₂ - C_n` does not vanish. -/
  Jform_ne_zero : ∀ n, 1 ≤ n →
    ((4 * BN n : ℚ) : ℚ_[2]) * GZ2 - ((CN n : ℚ) : ℚ_[2]) ≠ 0
  /-- Equation (13.2): `v₂(J_n) = 14n + 2 - s₂(n) - s₂(3n)`. -/
  val_Jform : ∀ n, 1 ≤ n →
    Padic.valuation (((4 * BN n : ℚ) : ℚ_[2]) * GZ2 - ((CN n : ℚ) : ℚ_[2]))
      = 14 * (n : ℤ) + 2 - (s2 n : ℤ) - (s2 (3 * n) : ℤ)

namespace NesterenkoFormInputs

variable (N : NesterenkoFormInputs)

lemma four_BN_ne_zero {n : ℕ} (hn : 1 ≤ n) : (4 : ℚ) * N.BN n ≠ 0 :=
  mul_ne_zero (by norm_num) (N.BN_ne_zero n hn)

lemma tail_eq (n : ℕ) (hn : 1 ≤ n) :
    GZ2 - ((N.CN n / (4 * N.BN n) : ℚ) : ℚ_[2])
      = (((4 * N.BN n : ℚ) : ℚ_[2]) * GZ2 - ((N.CN n : ℚ) : ℚ_[2]))
        * (((4 * N.BN n : ℚ) : ℚ_[2]))⁻¹ := by
  have hB : ((N.BN n : ℚ) : ℚ_[2]) ≠ 0 := by
    exact_mod_cast Rat.cast_ne_zero.mpr (N.BN_ne_zero n hn)
  push_cast
  field_simp

/-- Section 15: the slope-`28` tail valuation, derived from `v₂(J_n)` and `v₂(4B_n)`. -/
theorem val_tail_of_form (n : ℕ) (hn : 1 ≤ n) :
    Padic.valuation (GZ2 - ((N.CN n / (4 * N.BN n) : ℚ) : ℚ_[2]))
      = 28 * (n : ℤ) - 1 - 2 * (s2 n : ℤ) - 2 * (s2 (3 * n) : ℤ) := by
  have h4 : ((4 * N.BN n : ℚ) : ℚ_[2]) ≠ 0 := by
    exact_mod_cast Rat.cast_ne_zero.mpr (N.four_BN_ne_zero hn)
  have hJ := N.Jform_ne_zero n hn
  rw [N.tail_eq n hn, Padic.valuation_mul hJ (inv_ne_zero h4), Padic.valuation_inv,
    Padic.valuation_ratCast, N.val_Jform n hn, N.val_four_BN n hn]
  ring

theorem tail_ne_zero_of_form (n : ℕ) (hn : 1 ≤ n) :
    GZ2 - ((N.CN n / (4 * N.BN n) : ℚ) : ℚ_[2]) ≠ 0 := by
  have h4 : ((4 * N.BN n : ℚ) : ℚ_[2]) ≠ 0 := by
    exact_mod_cast Rat.cast_ne_zero.mpr (N.four_BN_ne_zero hn)
  rw [N.tail_eq n hn]
  exact mul_ne_zero (N.Jform_ne_zero n hn) (inv_ne_zero h4)

/-- The `2`-adic package derived from the linear-form package. -/
def toPadic : NesterenkoPadicInputs where
  BN := N.BN
  CN := N.CN
  aN := N.aN
  yN := N.yN
  BN_ne_zero := N.BN_ne_zero
  aN_eq := N.aN_eq
  yN_eq := N.yN_eq
  val_four_BN := N.val_four_BN
  tail_ne_zero := N.tail_ne_zero_of_form
  val_tail := N.val_tail_of_form

@[simp] lemma toPadic_aN : N.toPadic.aN = N.aN := rfl

@[simp] lemma toPadic_yN : N.toPadic.yN = N.yN := rfl

end NesterenkoFormInputs

/-! ### Section 19–20: the integer-normalized Plücker determinant -/

/-- A sharper lower bound for the Zudilin clearing exponent:
`e_{3n} ≥ 12n + 3 + ⌊log₂ 3n⌋`. -/
theorem eZud_three_mul_lb_log (n : ℕ) (hn : 1 ≤ n) :
    12 * n + 3 + Nat.log 2 (3 * n) ≤ eZud (3 * n) := by
  have hlog_le : Nat.log 2 (3 * n) ≤ 3 * n - 1 := by
    have := Nat.log_lt_self 2 (show 3 * n ≠ 0 by omega)
    omega
  have hmono : Nat.log 2 (3 * n) ≤ Nat.log 2 (2 * (3 * n) - 1) :=
    Nat.log_mono_right (by omega)
  simp only [eZud, le_min_iff]
  constructor
  · omega
  · omega

/-- Equation (20.3): `2^{24n}` divides the reduced cross determinant of the Zudilin row and
the Nesterenko row. -/
theorem dvd_reduced_cross_N (N : NesterenkoPadicInputs) (n : ℕ) :
    (2 : ℤ) ^ (24 * n) ∣ a2row n * N.yN n - N.aN n * y2row n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · simp [hn]
  -- the rational identity (19.2)
  have hcast : ((a2row n * N.yN n - N.aN n * y2row n : ℤ) : ℚ)
      = -((2 : ℚ) ^ (eZud (3 * n) + 14 * n) * (Sfac n : ℚ) * N.DeltaN n) := by
    have ha := a2row_eq n
    have hy := y2row_eq n
    rw [Y2row] at hy
    have h4 : ((4 : ℚ) ^ (7 * n)) = (2 : ℚ) ^ (14 * n) := by
      rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul]
      ring_nf
    push_cast
    rw [ha, hy, N.aN_eq n, N.yN_eq n, NesterenkoPadicInputs.DeltaN, pow_add, pow_succ, h4]
    ring
  -- the valuation estimate
  have hS : ((Sfac n : ℚ)) ≠ 0 := by
    have := Sfac_pos n
    positivity
  have hD : N.DeltaN n ≠ 0 := N.DeltaN_ne_zero n hn
  have hpow : ((2 : ℚ) ^ (eZud (3 * n) + 14 * n)) ≠ 0 := by positivity
  have hval : (24 : ℤ) * n ≤ padicValRat 2 ((a2row n * N.yN n - N.aN n * y2row n : ℤ) : ℚ) := by
    rw [hcast, padicValRat.neg, padicValRat.mul (mul_ne_zero hpow hS) hD,
      padicValRat.mul hpow hS, padicValRat_two_pow, N.val_DeltaN n hn]
    have hSnn := padicValRat_Sfac_nonneg n
    have he : (12 * n + 3 + Nat.log 2 (3 * n) : ℤ) ≤ (eZud (3 * n) : ℤ) := by
      exact_mod_cast eZud_three_mul_lb_log n hn
    have hs2 : (s2 (3 * n) : ℤ) ≤ (Nat.log 2 (3 * n) : ℤ) + 1 := by
      have := s2_le_log_succ (3 * n) (by omega)
      exact_mod_cast this
    have hs2n : (0 : ℤ) ≤ (s2 n : ℤ) := by positivity
    push_cast at he ⊢
    omega
  rw [padicValRat.of_int] at hval
  have hvi : 24 * n ≤ padicValInt 2 (a2row n * N.yN n - N.aN n * y2row n) := by
    exact_mod_cast hval
  exact (padicValInt_dvd_iff (p := 2) (24 * n) _).mpr (Or.inr hvi)

end Catalan
