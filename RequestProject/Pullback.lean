import Mathlib

/-!
# The quadratic pullback of Beukers' Padé equation onto the modular `E`-equation

Section 6 of the unconditional note.

Working with formal power series over an arbitrary commutative ring we introduce

* `LBop`, four times Beukers' operator at `x = 1/2`,
  `L_B = t(t-1)² d²/dt² + (3t-1)(t-1) d/dt + (t - 3/4)`;
* `LEop`, the modular `E`-operator `θ² - z(12θ² + 12θ + 4) + 32z²(θ+1)²` written in terms of
  `d/dz`;
* `Tsub = 16z(1-4z)` and `Gser = 1 - 8z`.

The main result is `LEop_pullback` (Lemma 6.1):
`𝓛_E [g · y(t(z))] = 16 z (L_B y)(t(z))`, in the scaled form `LEop (G * substT Y) = 4X * substT (LBop Y)`.

We also compute all coefficients of `LBop` and `LEop`, which turns the two operator equations
into the two Catalan recurrences, and prove the uniqueness statement needed to identify the
generating functions.
-/

namespace Catalan

open PowerSeries

variable {R : Type*} [CommRing R]

/-! ### Derivative and coefficient toolkit -/

@[simp] lemma derivative_ofNat' (n : ℕ) [n.AtLeastTwo] :
    d⁄dX R (no_index (OfNat.ofNat n) : R⟦X⟧) = 0 := by
  rw [show (OfNat.ofNat n : R⟦X⟧) = C (OfNat.ofNat n : R) from PowerSeries.ext (congrFun rfl),
    derivative_C]

/-- The formal derivative, as a plain function. -/
noncomputable def Dser (f : R⟦X⟧) : R⟦X⟧ := d⁄dX R f

lemma coeff_Xpow_mul (j n : ℕ) (f : R⟦X⟧) :
    coeff n (X ^ j * f) = if j ≤ n then coeff (n - j) f else 0 := by
  by_cases h : j ≤ n
  · rw [if_pos h, show n = (n - j) + j by omega]
    simp [PowerSeries.coeff_X_pow_mul, show n - j + j - j = n - j by omega]
  · rw [if_neg h, PowerSeries.coeff_mul]
    apply Finset.sum_eq_zero
    intro p hp
    have hp' := Finset.HasAntidiagonal.antidiagonal.fst_le hp
    have hz : coeff p.1 (X ^ j : R⟦X⟧) = 0 := by
      rw [PowerSeries.coeff_X_pow]
      exact if_neg (by omega)
    simp [hz]

lemma coeff_Dser (f : R⟦X⟧) (n : ℕ) : coeff n (Dser f) = ((n : R) + 1) * coeff (n + 1) f := by
  rw [Dser, coeff_derivative]
  ring

@[simp] lemma constantCoeff_Dser (f : R⟦X⟧) : constantCoeff (Dser f) = coeff 1 f := by
  have := coeff_Dser f 0
  simpa using this

@[simp] lemma constantCoeff_ofNat' (k : ℕ) [k.AtLeastTwo] :
    constantCoeff (no_index (OfNat.ofNat k) : R⟦X⟧) = (OfNat.ofNat k : R) := by
  rw [show (OfNat.ofNat k : R⟦X⟧) = C (OfNat.ofNat k : R) from PowerSeries.ext (congrFun rfl)]
  simp

lemma coeff_Dser_Dser (f : R⟦X⟧) (n : ℕ) :
    coeff n (Dser (Dser f)) = ((n : R) + 1) * ((n : R) + 2) * coeff (n + 2) f := by
  rw [coeff_Dser, coeff_Dser]
  push_cast
  ring

lemma coeff_ofNat_mul (k : ℕ) [k.AtLeastTwo] (n : ℕ) (f : R⟦X⟧) :
    coeff n ((no_index (OfNat.ofNat k) : R⟦X⟧) * f) = (OfNat.ofNat k : R) * coeff n f := by
  rw [show (OfNat.ofNat k : R⟦X⟧) = C (OfNat.ofNat k : R) from PowerSeries.ext (congrFun rfl),
    coeff_C_mul]

/-! ### The two operators and the substitution -/

/-- `t = 16z(1-4z)`. -/
noncomputable def Tsub : R⟦X⟧ := 16 * X - 64 * X ^ 2

/-- `g = 1 - 8z`. -/
noncomputable def Gser : R⟦X⟧ := 1 - 8 * X

lemma hasSubst_T : HasSubst (Tsub : R⟦X⟧) := by
  apply HasSubst.of_constantCoeff_zero'
  simp [Tsub, sq]

/-- Substitution `y ↦ y(t(z))`. -/
noncomputable def substT (f : R⟦X⟧) : R⟦X⟧ := substAlgHom (hasSubst_T (R := R)) f

@[simp] lemma substT_add (f g : R⟦X⟧) : substT (f + g) = substT f + substT g := map_add _ _ _
@[simp] lemma substT_sub (f g : R⟦X⟧) : substT (f - g) = substT f - substT g := map_sub _ _ _
@[simp] lemma substT_mul (f g : R⟦X⟧) : substT (f * g) = substT f * substT g := map_mul _ _ _
@[simp] lemma substT_pow (f : R⟦X⟧) (n : ℕ) : substT (f ^ n) = (substT f) ^ n := map_pow _ _ _
@[simp] lemma substT_one : substT (1 : R⟦X⟧) = 1 := map_one _
@[simp] lemma substT_zero : substT (0 : R⟦X⟧) = 0 := map_zero _
@[simp] lemma substT_ofNat (n : ℕ) [n.AtLeastTwo] :
    substT (no_index (OfNat.ofNat n) : R⟦X⟧) = OfNat.ofNat n := map_ofNat _ _
@[simp] lemma substT_X : substT (X : R⟦X⟧) = Tsub := by
  rw [substT, substAlgHom_X]
@[simp] lemma substT_C (r : R) : substT (C r : R⟦X⟧) = C r :=
  (substAlgHom (hasSubst_T (R := R))).commutes r

lemma substT_eq (f : R⟦X⟧) : substT f = f.subst (Tsub : R⟦X⟧) := by
  rw [substT, coe_substAlgHom]

lemma Dser_Tsub : Dser (Tsub : R⟦X⟧) = 16 - 128 * X := by
  simp [Dser, Tsub, Derivation.leibniz, sq]
  ring

lemma chain_rule (f : R⟦X⟧) : Dser (substT f) = substT (Dser f) * (16 - 128 * X) := by
  rw [substT_eq, substT_eq, Dser, Dser, derivative_subst R hasSubst_T]
  rw [show (d⁄dX R) (Tsub : R⟦X⟧) = 16 - 128 * X from Dser_Tsub]

/-- Four times Beukers' operator at `x = 1/2`. -/
noncomputable def LBop (Y : R⟦X⟧) : R⟦X⟧ :=
  (4 * X ^ 3 - 8 * X ^ 2 + 4 * X : R⟦X⟧) * Dser (Dser Y)
    + (12 * X ^ 2 - 16 * X + 4 : R⟦X⟧) * Dser Y + (4 * X - 3 : R⟦X⟧) * Y

/-- The modular `E` operator. -/
noncomputable def LEop (f : R⟦X⟧) : R⟦X⟧ :=
  (X ^ 2 - 12 * X ^ 3 + 32 * X ^ 4 : R⟦X⟧) * Dser (Dser f)
    + (X - 24 * X ^ 2 + 96 * X ^ 3 : R⟦X⟧) * Dser f + (-4 * X + 32 * X ^ 2 : R⟦X⟧) * f

/-- Lemma 6.1, the exact quadratic pullback. -/
theorem LEop_pullback (Y : R⟦X⟧) :
    LEop (Gser * substT Y) = 4 * X * substT (LBop Y) := by
  set u := substT Y with hu
  set u1 := substT (Dser Y) with hu1
  set u2 := substT (Dser (Dser Y)) with hu2
  have h1 : Dser u = u1 * (16 - 128 * X) := chain_rule Y
  have h2 : Dser u1 = u2 * (16 - 128 * X) := chain_rule (Dser Y)
  have e1 : Dser (Gser * u) = -8 * u + Gser * Dser u := by
    simp [Dser, Gser, Derivation.leibniz]
    ring
  have e2 : Dser (-8 * u + Gser * (u1 * (16 - 128 * X)))
      = -8 * Dser u + (-8 * (u1 * (16 - 128 * X))
        + Gser * (Dser u1 * (16 - 128 * X) + u1 * (-128))) := by
    simp [Dser, Gser, Derivation.leibniz]
    ring
  have hsub : substT (LBop Y)
      = (4 * (Tsub : R⟦X⟧) ^ 3 - 8 * Tsub ^ 2 + 4 * Tsub) * u2
        + (12 * (Tsub : R⟦X⟧) ^ 2 - 16 * Tsub + 4) * u1 + (4 * (Tsub : R⟦X⟧) - 3) * u := by
    simp [LBop, hu, hu1, hu2]
  have hDf : Dser (Gser * u) = -8 * u + Gser * (u1 * (16 - 128 * X)) := by rw [e1, h1]
  have hDDf : Dser (Dser (Gser * u))
      = -8 * (u1 * (16 - 128 * X)) + (-8 * (u1 * (16 - 128 * X))
        + Gser * (u2 * (16 - 128 * X) * (16 - 128 * X) + u1 * (-128))) := by
    rw [hDf, e2, h1, h2]
  rw [LEop, hDDf, hDf, hsub, Gser, Tsub]
  ring

/-! ### Coefficients of the two operators -/

lemma LEop_expand (f : R⟦X⟧) :
    LEop f = (X ^ 2 * Dser (Dser f) - 12 * (X ^ 3 * Dser (Dser f)) + 32 * (X ^ 4 * Dser (Dser f)))
      + (X ^ 1 * Dser f - 24 * (X ^ 2 * Dser f) + 96 * (X ^ 3 * Dser f))
      + (-(4 * (X ^ 1 * f)) + 32 * (X ^ 2 * f)) := by
  rw [LEop]; ring

lemma LBop_expand (Y : R⟦X⟧) :
    LBop Y = (4 * (X ^ 3 * Dser (Dser Y)) - 8 * (X ^ 2 * Dser (Dser Y))
        + 4 * (X ^ 1 * Dser (Dser Y)))
      + (12 * (X ^ 2 * Dser Y) - 16 * (X ^ 1 * Dser Y) + 4 * Dser Y)
      + (4 * (X ^ 1 * Y) - 3 * Y) := by
  rw [LBop]; ring

lemma coeff_LEop_zero (f : R⟦X⟧) : coeff 0 (LEop f) = 0 := by
  rw [LEop_expand]
  simp

lemma coeff_LEop_one (f : R⟦X⟧) : coeff 1 (LEop f) = coeff 1 f - 4 * coeff 0 f := by
  rw [LEop_expand]
  simp [coeff_Xpow_mul, coeff_ofNat_mul, coeff_Dser]
  ring

lemma coeff_LEop_add_two (f : R⟦X⟧) (m : ℕ) :
    coeff (m + 2) (LEop f)
      = ((m : R) + 2) ^ 2 * coeff (m + 2) f
        - (12 * ((m : R) + 1) * ((m : R) + 2) + 4) * coeff (m + 1) f
        + 32 * ((m : R) + 1) ^ 2 * coeff m f := by
  rw [LEop_expand]
  match m with
  | 0 =>
      simp [coeff_Xpow_mul, coeff_ofNat_mul, coeff_Dser]
      ring
  | 1 =>
      simp [coeff_Xpow_mul, coeff_ofNat_mul, coeff_Dser]
      ring
  | (k + 2) =>
      simp [coeff_Xpow_mul, coeff_ofNat_mul, coeff_Dser,
        show k + 2 + 2 - 3 = k + 1 by omega, show k + 2 + 2 - 4 = k by omega]
      ring

lemma coeff_LBop_zero (Y : R⟦X⟧) : coeff 0 (LBop Y) = 4 * coeff 1 Y - 3 * coeff 0 Y := by
  rw [LBop_expand]
  simp [coeff_Dser]
  ring

lemma coeff_LBop_add_one (Y : R⟦X⟧) (m : ℕ) :
    coeff (m + 1) (LBop Y)
      = 4 * ((m : R) + 2) ^ 2 * coeff (m + 2) Y
        - (8 * ((m : R) + 1) ^ 2 + 8 * ((m : R) + 1) + 3) * coeff (m + 1) Y
        + 4 * ((m : R) + 1) ^ 2 * coeff m Y := by
  rw [LBop_expand]
  match m with
  | 0 =>
      simp [coeff_Xpow_mul, coeff_ofNat_mul, coeff_Dser]
      ring
  | 1 =>
      simp [coeff_Xpow_mul, coeff_ofNat_mul, coeff_Dser]
      ring
  | (k + 2) =>
      simp [coeff_Xpow_mul, coeff_ofNat_mul, coeff_Dser,
        show k + 2 + 1 - 2 = k + 1 by omega, show k + 2 + 1 - 3 = k by omega]
      ring

/-! ### Recurrences versus operator equations -/

/-- If a sequence satisfies Beukers' recurrence at `x = 1/2` then its generating function
satisfies `LBop Y = C c`, where `c = 4 y₁ - 3 y₀`. -/
lemma LBop_mk (y : ℕ → R)
    (hrec : ∀ m : ℕ, 4 * ((m : R) + 2) ^ 2 * y (m + 2)
      = (8 * ((m : R) + 1) ^ 2 + 8 * ((m : R) + 1) + 3) * y (m + 1) - 4 * ((m : R) + 1) ^ 2 * y m) :
    LBop (mk y) = C (4 * y 1 - 3 * y 0) := by
  ext n
  match n with
  | 0 => simpa using coeff_LBop_zero (mk y)
  | (m + 1) =>
      rw [coeff_LBop_add_one]
      simp only [coeff_mk, coeff_C]
      rw [if_neg (by omega)]
      linear_combination hrec m

/-- If a sequence satisfies the modular `E` recurrence then its generating function satisfies
`LEop F = C c * X`, where `c = y₁ - 4 y₀`. -/
lemma LEop_mk (y : ℕ → R)
    (hrec : ∀ m : ℕ, ((m : R) + 2) ^ 2 * y (m + 2)
      = (12 * ((m : R) + 1) * ((m : R) + 2) + 4) * y (m + 1) - 32 * ((m : R) + 1) ^ 2 * y m) :
    LEop (mk y) = C (y 1 - 4 * y 0) * X := by
  ext n
  match n with
  | 0 => simpa using coeff_LEop_zero (mk y)
  | 1 =>
      rw [coeff_LEop_one]
      simp
  | (m + 2) =>
      rw [coeff_LEop_add_two]
      simp only [coeff_mk]
      rw [show ((C (y 1 - 4 * y 0) : R⟦X⟧) * X) = X * C (y 1 - 4 * y 0) by ring,
        PowerSeries.coeff_succ_X_mul]
      simp only [coeff_C]
      rw [if_neg (by omega)]
      linear_combination hrec m

/-! ### Uniqueness -/

/-- Over a field of characteristic zero the equation `LEop f = g` together with the constant
coefficient determines `f`. -/
theorem LEop_injective {K : Type*} [Field K] [CharZero K] {f g : K⟦X⟧}
    (hop : LEop f = LEop g) (h0 : coeff 0 f = coeff 0 g) : f = g := by
  have key : ∀ n : ℕ, coeff n f = coeff n g ∧ coeff (n + 1) f = coeff (n + 1) g := by
    intro n
    induction n with
    | zero =>
        refine ⟨h0, ?_⟩
        have h1 := congrArg (fun s => coeff 1 s) hop
        simp only [coeff_LEop_one] at h1
        linear_combination h1 + 4 * h0
    | succ m ih =>
        refine ⟨ih.2, ?_⟩
        have h2 := congrArg (fun s => coeff (m + 2) s) hop
        simp only [coeff_LEop_add_two] at h2
        have hcoef : ((m : K) + 2) ^ 2 ≠ 0 := by
          have hne : ((m : K) + 2) ≠ 0 := by
            rw [show ((m : K) + 2) = ((m + 2 : ℕ) : K) by push_cast; ring]
            exact Nat.cast_ne_zero.mpr (by omega)
          exact pow_ne_zero _ hne
        have heq : ((m : K) + 2) ^ 2 * coeff (m + 2) f = ((m : K) + 2) ^ 2 * coeff (m + 2) g := by
          linear_combination h2 + (12 * ((m : K) + 1) * ((m : K) + 2) + 4) * ih.2
            - 32 * ((m : K) + 1) ^ 2 * ih.1
        exact mul_left_cancel₀ hcoef heq
  ext n
  exact (key n).1

end Catalan
