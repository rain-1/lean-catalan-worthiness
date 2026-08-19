import Mathlib

/-!
# The Legendre substitution `z = 16 t (1 - 4 t)`, as a polynomial toolkit

The modular `E`-family generating functions `A(t) = ∑ Aₙ tⁿ` and `B(t) = ∑ Bₙ tⁿ` are
pullbacks along the substitution `z = 16 t (1 - 4 t)` of solutions of a Gauss hypergeometric
equation.  This file sets up the finite (polynomial) version of that dictionary.

* `zq = 16 X - 64 X²` is the substitution polynomial, and `coeff_zq_pow` computes the
  coefficients of its powers, `[tⁿ] zᵏ = 16ᵏ (-4)^{n-k} C(k, n-k)`.
* `theta p = X · p'` is the Euler operator `θ = t d/dt`, with `coeff_theta : [tⁿ] θp = n [tⁿ]p`.
* `Lop` is the operator attached to the `E`-recurrence,
  `L = θ² - t(12θ² + 12θ + 4) + 32t²(θ+1)²`,
  whose coefficients read off that recurrence (`Lop_coeff`).
* `Mop = (1 - 8X) d/dX - 8` is the operator attached to `(1-z)^{-1/2}`.
* `Lop_zq_pow` and `Mop_zq_pow` are the two chain-rule identities

  `L[zᵏ] = 16t(1-8t) (k² z^{k-1} - (k + 1/2)² zᵏ)`,   `M[zᵏ] = 8 (2k z^{k-1} - (2k+1) zᵏ)`,

  the polynomial form of `L[H(z(t))] = 16t(1-8t) · 𝒢H` (`𝒢` the Gauss operator with parameters
  `(1/2, 1/2; 1)`) and of the Gauss equation for `(1-z)^{-1/2}`.  The first identity is stated
  in the cleared form `4 · L[zᵏ] = …` so that all coefficients are integral.
-/

namespace Catalan

open Polynomial Finset

/-- The substitution polynomial `z = 16 t (1 - 4 t)`. -/
noncomputable def zq : ℚ[X] := 16 * X - 64 * X ^ 2

lemma zq_eq_smul : zq = (16 : ℚ) • (X * (1 - 4 * X)) := by
  unfold zq
  rw [smul_eq_C_mul]
  have h16 : (C (16:ℚ)) = 16 := map_ofNat C 16
  rw [h16]; ring

lemma zq_pow_eq (k : ℕ) : zq ^ k = (16 : ℚ) ^ k • (X ^ k * (1 - 4 * X) ^ k) := by
  rw [zq_eq_smul, _root_.smul_pow, mul_pow]

lemma derivative_zq : derivative zq = 16 - 128 * X := by
  unfold zq; simp; ring

/-- The coefficients of `(1 - 4X)^k`. -/
lemma coeff_one_sub_four_X_pow (k d : ℕ) :
    ((1 - 4 * X : ℚ[X]) ^ k).coeff d = (-4 : ℚ) ^ d * (k.choose d) := by
  have hC4 : (C (-4 : ℚ)) = -4 := by rw [C_neg, map_ofNat]
  have h : (1 - 4 * X : ℚ[X]) = C (-4) * (X + C (-1/4)) := by
    rw [mul_add, ← C_mul, hC4]
    norm_num
    ring
  rw [h, mul_pow, ← C_pow, coeff_C_mul, coeff_X_add_C_pow]
  rcases le_or_gt d k with hd | hd
  · have hsplit : ((-4 : ℚ)) ^ k = (-4) ^ d * (-4) ^ (k - d) := by
      rw [← pow_add]; congr 1; omega
    have h4 : ((-4 : ℚ)) ^ (k - d) * (-1/4 : ℚ) ^ (k - d) = 1 := by
      rw [← mul_pow]; norm_num
    calc ((-4:ℚ)) ^ k * ((-1/4 : ℚ) ^ (k - d) * (k.choose d))
        = ((-4:ℚ)) ^ d * (((-4:ℚ)) ^ (k - d) * (-1/4 : ℚ) ^ (k - d)) * (k.choose d) := by
          rw [hsplit]; ring
      _ = (-4 : ℚ) ^ d * (k.choose d) := by rw [h4]; ring
  · rw [Nat.choose_eq_zero_of_lt hd]
    simp

/-- `[tⁿ] zᵏ = 16ᵏ (-4)^{n-k} C(k, n-k)` for `k ≤ n`, and `0` otherwise. -/
lemma coeff_zq_pow (k n : ℕ) :
    (zq ^ k).coeff n =
      if k ≤ n then (16 : ℚ) ^ k * ((-4 : ℚ) ^ (n - k) * (k.choose (n - k))) else 0 := by
  rw [zq_pow_eq, coeff_smul, mul_comm (X ^ k) _, coeff_mul_X_pow']
  split_ifs with h
  · rw [coeff_one_sub_four_X_pow]
    simp [smul_eq_mul]
  · simp

lemma coeff_zq_pow_of_lt {k n : ℕ} (h : n < k) : (zq ^ k).coeff n = 0 := by
  rw [coeff_zq_pow, if_neg (by omega)]

lemma coeff_zq_pow_of_le {k n : ℕ} (h : k ≤ n) :
    (zq ^ k).coeff n = (16 : ℚ) ^ k * ((-4 : ℚ) ^ (n - k) * (k.choose (n - k))) := by
  rw [coeff_zq_pow, if_pos h]

/-! ### The Euler operator -/

/-- The Euler operator `θ = t d/dt`. -/
noncomputable def theta (p : ℚ[X]) : ℚ[X] := X * derivative p

lemma coeff_theta (p : ℚ[X]) (n : ℕ) : (theta p).coeff n = (n : ℚ) * p.coeff n := by
  cases n with
  | zero => simp [theta]
  | succ m => simp [theta, coeff_X_mul, coeff_derivative]; ring

lemma coeff_X_mul_succ (p : ℚ[X]) (n : ℕ) : (X * p).coeff (n + 1) = p.coeff n := coeff_X_mul p n

lemma coeff_X_sq_mul (p : ℚ[X]) (n : ℕ) : ((X : ℚ[X]) ^ 2 * p).coeff (n + 2) = p.coeff n := by
  have : (X : ℚ[X]) ^ 2 * p = X * (X * p) := by ring
  rw [this, coeff_X_mul, coeff_X_mul]

/-! ### The two differential operators -/

/-- The operator `L = θ² - t(12θ² + 12θ + 4) + 32t²(θ+1)²` with `θ = t d/dt`. -/
noncomputable def Lop (p : ℚ[X]) : ℚ[X] :=
  theta (theta p) - X * (12 * theta (theta p) + 12 * theta p + 4 * p)
    + 32 * X ^ 2 * (theta (theta p) + 2 * theta p + p)

/-- The operator `M = (1 - 8X) d/dX - 8`. -/
noncomputable def Mop (p : ℚ[X]) : ℚ[X] := (1 - 8 * X) * derivative p - 8 * p

lemma theta_add (p q : ℚ[X]) : theta (p + q) = theta p + theta q := by
  unfold theta; simp only [derivative_add]; ring

lemma theta_smul (c : ℚ) (p : ℚ[X]) : theta (c • p) = c • theta p := by
  unfold theta
  simp only [derivative_smul]
  simp only [smul_eq_C_mul]
  ring

lemma Lop_add (p q : ℚ[X]) : Lop (p + q) = Lop p + Lop q := by
  unfold Lop; simp only [theta_add]; ring

lemma Lop_smul (c : ℚ) (p : ℚ[X]) : Lop (c • p) = c • Lop p := by
  unfold Lop
  simp only [theta_smul]
  simp only [smul_eq_C_mul]
  ring

lemma Mop_add (p q : ℚ[X]) : Mop (p + q) = Mop p + Mop q := by
  unfold Mop; simp only [derivative_add]; ring

lemma Mop_smul (c : ℚ) (p : ℚ[X]) : Mop (c • p) = c • Mop p := by
  unfold Mop
  simp only [derivative_smul]
  simp only [smul_eq_C_mul]
  ring

lemma Lop_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    Lop (∑ i ∈ s, f i) = ∑ i ∈ s, Lop (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [Lop, theta]
  | insert a s ha ih => rw [Finset.sum_insert ha, Lop_add, ih, Finset.sum_insert ha]

lemma Mop_sum {ι : Type*} (s : Finset ι) (f : ι → ℚ[X]) :
    Mop (∑ i ∈ s, f i) = ∑ i ∈ s, Mop (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [Mop]
  | insert a s ha ih => rw [Finset.sum_insert ha, Mop_add, ih, Finset.sum_insert ha]

/-! ### Reading off the recurrences -/

/-- `L` encodes the `E`-recurrence: its `(n+2)`-nd coefficient is
`(n+2)² pₙ₊₂ - (12(n+1)(n+2)+4) pₙ₊₁ + 32(n+1)² pₙ`. -/
lemma Lop_coeff (p : ℚ[X]) (n : ℕ) :
    (Lop p).coeff (n + 2) =
      ((n : ℚ) + 2) ^ 2 * p.coeff (n + 2)
        - (12 * ((n : ℚ) + 1) * ((n : ℚ) + 2) + 4) * p.coeff (n + 1)
        + 32 * ((n : ℚ) + 1) ^ 2 * p.coeff n := by
  have hX : ∀ q : ℚ[X], (X * (12 * theta (theta q) + 12 * theta q + 4 * q)).coeff (n + 2)
      = 12 * (theta (theta q)).coeff (n + 1) + 12 * (theta q).coeff (n + 1)
        + 4 * q.coeff (n + 1) := by
    intro q
    rw [show (n + 2) = (n + 1) + 1 by ring, coeff_X_mul]
    simp
  have hX2 : ∀ q : ℚ[X], ((32 : ℚ[X]) * X ^ 2 * (theta (theta q) + 2 * theta q + q)).coeff (n + 2)
      = 32 * ((theta (theta q)).coeff n + 2 * (theta q).coeff n + q.coeff n) := by
    intro q
    have : (32 : ℚ[X]) * X ^ 2 * (theta (theta q) + 2 * theta q + q)
        = 32 * (X ^ 2 * (theta (theta q) + 2 * theta q + q)) := by ring
    rw [this]
    simp
  rw [Lop, coeff_add, coeff_sub, hX, hX2]
  simp only [coeff_theta]
  push_cast
  ring

/-- `M` encodes the first-order recurrence for `(1-z)^{-1/2}`. -/
lemma Mop_coeff (p : ℚ[X]) (n : ℕ) :
    (Mop p).coeff n = ((n : ℚ) + 1) * p.coeff (n + 1) - (8 * (n : ℚ) + 8) * p.coeff n := by
  have h : Mop p = derivative p - 8 * theta p - 8 * p := by
    unfold Mop theta; ring
  rw [h]
  simp [coeff_derivative, coeff_theta]
  ring

lemma coeff_prefactor (Q : ℚ[X]) (n : ℕ) :
    ((16 * X - 128 * X ^ 2) * Q).coeff (n + 2) = 16 * Q.coeff (n + 1) - 128 * Q.coeff n := by
  have h : (16 * X - 128 * X ^ 2 : ℚ[X]) * Q = 16 * (X * Q) - 128 * (X ^ 2 * Q) := by ring
  rw [h, coeff_sub]
  simp [show n + 2 = (n + 1) + 1 from rfl, coeff_X_mul]

/-! ### The two chain-rule identities -/

lemma derivative_zq_pow_succ (k : ℕ) :
    derivative (zq ^ (k + 1)) = ((k : ℚ[X]) + 1) * zq ^ k * (16 - 128 * X) := by
  rw [derivative_pow, derivative_zq]
  push_cast [map_ofNat]
  simp

lemma derivative_zq_pow_two_add (k : ℕ) :
    derivative (zq ^ (k + 2)) = ((k : ℚ[X]) + 2) * zq ^ (k + 1) * (16 - 128 * X) := by
  rw [derivative_pow, derivative_zq]
  push_cast [map_ofNat]
  simp
  exact Or.inl (Or.inl (map_ofNat C 2))

/-- The chain rule `4 L[z^{k+2}] = 16t(1-8t) (4(k+2)² z^{k+1} - (2k+5)² z^{k+2})`. -/
lemma Lop_zq_pow_two_add (k : ℕ) :
    4 * Lop (zq ^ (k + 2)) = (16 * X - 128 * X ^ 2) *
      (4 * ((k : ℚ[X]) + 2) ^ 2 * zq ^ (k + 1) - (2 * (k : ℚ[X]) + 5) ^ 2 * zq ^ (k + 2)) := by
  have h1 := derivative_zq_pow_two_add k
  have h2 : derivative (derivative (zq ^ (k + 2))) =
      ((k : ℚ[X]) + 2) * (((k : ℚ[X]) + 1) * zq ^ k * (16 - 128 * X) * (16 - 128 * X)
        + zq ^ (k + 1) * (-128)) := by
    rw [h1, derivative_mul, derivative_mul, derivative_zq_pow_succ]
    simp
    ring
  have hL : Lop (zq ^ (k + 2)) =
      (1 - 12 * X + 32 * X ^ 2) * (X * derivative (zq ^ (k + 2))
        + X ^ 2 * derivative (derivative (zq ^ (k + 2))))
      + (-12 * X + 64 * X ^ 2) * (X * derivative (zq ^ (k + 2)))
      + (-4 * X + 32 * X ^ 2) * zq ^ (k + 2) := by
    unfold Lop theta
    simp only [derivative_mul, derivative_X]
    ring
  rw [hL, h2, h1]
  have e1 : zq ^ (k + 2) = zq ^ k * zq * zq := by ring
  have e2 : zq ^ (k + 1) = zq ^ k * zq := by ring
  rw [e1, e2]
  unfold zq
  ring

lemma Lop_zq_pow_zero :
    4 * Lop (zq ^ 0) = (16 * X - 128 * X ^ 2) * (-(1 : ℚ[X]) * zq ^ 0) := by
  simp [Lop, theta, zq]
  ring

lemma Lop_zq_pow_one :
    4 * Lop (zq ^ 1) =
      (16 * X - 128 * X ^ 2) * (4 * (1 : ℚ[X]) * zq ^ 0 - 9 * zq ^ 1) := by
  simp [Lop, theta, zq]
  ring

/-- The chain rule `M[z^{k+1}] = 8 (2(k+1) z^k - (2(k+1)+1) z^{k+1})`. -/
lemma Mop_zq_pow_succ (k : ℕ) :
    Mop (zq ^ (k + 1)) =
      8 * (2 * ((k : ℚ[X]) + 1) * zq ^ k - (2 * ((k : ℚ[X]) + 1) + 1) * zq ^ (k + 1)) := by
  rw [Mop, derivative_zq_pow_succ]
  have e2 : zq ^ (k + 1) = zq ^ k * zq := by ring
  rw [e2]
  unfold zq
  ring

lemma Mop_zq_pow_zero : Mop (zq ^ 0) = 8 * (-(1 : ℚ[X]) * zq ^ 0) := by simp [Mop]

end Catalan
