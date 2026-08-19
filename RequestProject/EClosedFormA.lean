import RequestProject.EClosedForm

/-!
# A closed form for the modular `E`-family denominator `A_n` in the Legendre variable

`EIntegrality.lean` proves the closed form `A_n = ∑_k C(n,k) C(2k,k) C(2n-2k, n-k)`.  Here we
prove the *Legendre* closed form

`A_n = ∑_{k ≤ n} C(2k,k)² (-4)^{n-k} C(k, n-k)`,

i.e. that `∑_n A_n t^n = F(t(1-4t))` with `F(w) = ∑_k C(2k,k)² w^k`, in the truncated
(polynomial) form used in `EClosedForm.lean`.  The proof is the same "Legendre substitution"
argument as for `B_n`, but the coefficient recurrence

`4(k+1)² g_{k+1} = (2k+1)² g_k`,   `g_k = C(2k,k)²/16^k`,

is now homogeneous, so the telescoped operator identity has no `PW` term.
-/

namespace Catalan

open Polynomial Finset

/-- `g_k = C(2k,k)²/16^k`, the coefficient sequence of the first solution. -/
noncomputable def gco (k : ℕ) : ℚ := (Nat.centralBinom k : ℚ) ^ 2 / 16 ^ k

@[simp] lemma gco_zero : gco 0 = 1 := by norm_num [gco, Nat.centralBinom]

lemma gco_one : gco 1 = 1 / 4 := by norm_num [gco, Nat.centralBinom]

/-- The recurrence `4(k+1)² g_{k+1} = (2k+1)² g_k`. -/
lemma gco_rec (k : ℕ) :
    4 * ((k : ℚ) + 1) ^ 2 * gco (k + 1) = (2 * k + 1) ^ 2 * gco k := by
  have hb : (Nat.centralBinom k : ℚ) ≠ 0 := centralBinom_ne_zero k
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hB : (Nat.centralBinom (k + 1) : ℚ)
      = 2 * (2 * (k : ℚ) + 1) * (Nat.centralBinom k : ℚ) / ((k : ℚ) + 1) := by
    rw [eq_div_iff hk1]
    linarith [centralBinom_succ_cast k]
  have h16 : ((16 : ℚ)) ^ (k + 1) = 16 * 16 ^ k := by ring
  have h16k : ((16 : ℚ)) ^ k ≠ 0 := by positivity
  unfold gco
  rw [hB, h16]
  field_simp
  ring

/-- `PG N = ∑_{k<N} g_k z^k`. -/
noncomputable def PG (N : ℕ) : ℚ[X] := ∑ k ∈ range N, C (gco k) * zq ^ k

/-- The telescoped identity for `L`: `4 L[PG (N+1)] = -16t(1-8t) (2N+1)² g_N z^N`. -/
lemma Lop_PG (N : ℕ) :
    4 * Lop (PG (N + 1)) =
      (16 * X - 128 * X ^ 2) * (-(C ((2 * (N : ℚ) + 1) ^ 2 * gco N) * zq ^ N)) := by
  induction N with
  | zero => simp [PG, Lop, theta]; ring
  | succ M ih =>
      have hsplit : PG (M + 2) = PG (M + 1) + C (gco (M + 1)) * zq ^ (M + 1) := by
        simp [PG, Finset.sum_range_succ]
      rw [hsplit, Lop_add, mul_add, ih, Lop_C_mul]
      have hLz : 4 * (C (gco (M + 1)) * Lop (zq ^ (M + 1)))
          = C (gco (M + 1)) * ((16 * X - 128 * X ^ 2) *
            (4 * ((M : ℚ[X]) + 1) ^ 2 * zq ^ M - (2 * (M : ℚ[X]) + 3) ^ 2 * zq ^ (M + 1))) := by
        rw [← Lop_zq_pow_succ M]
        ring
      rw [hLz]
      have hrec := gco_rec M
      have hC : C (4 * ((M : ℚ) + 1) ^ 2 * gco (M + 1)) = C ((2 * (M : ℚ) + 1) ^ 2 * gco M) := by
        rw [hrec]
      simp only [map_mul, map_add, map_ofNat, map_natCast, map_pow, map_one] at hC ⊢
      push_cast
      linear_combination ((16 * X - 128 * X ^ 2) * zq ^ M) * hC

/-- The truncated coefficient sum `Ã_n = [tⁿ] PG (n+1)`. -/
noncomputable def Atil (n : ℕ) : ℚ := (PG (n + 1)).coeff n

lemma coeff_PG_eq (N n : ℕ) (h : n < N) : (PG N).coeff n = Atil n := by
  have key : ∀ M : ℕ, n < M → (PG M).coeff n = ∑ k ∈ range (n + 1), gco k * (zq ^ k).coeff n := by
    intro M hM
    unfold PG
    rw [Polynomial.finset_sum_coeff]
    have hsub : range (n + 1) ⊆ range M := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have hzero : ∀ k ∈ range M, k ∉ range (n + 1) → (C (gco k) * zq ^ k).coeff n = 0 := by
      intro k _ hk
      simp only [Finset.mem_range, not_lt] at hk
      rw [coeff_C_mul, coeff_zq_pow_of_lt (by omega), mul_zero]
    rw [← Finset.sum_subset hsub hzero]
    exact Finset.sum_congr rfl (fun k _ => by rw [coeff_C_mul])
  rw [key N h, Atil, key (n + 1) (by omega)]

@[simp] lemma Atil_zero : Atil 0 = 1 := by
  simp [Atil, PG]

@[simp] lemma Atil_one : Atil 1 = 4 := by
  have h : PG 2 = C (gco 0) * zq ^ 0 + C (gco 1) * zq ^ 1 := by
    simp [PG, Finset.sum_range_succ]
  simp [Atil, h, zq, gco_one, coeff_add, coeff_C_mul, Polynomial.coeff_one]
  norm_num

/-- The `E`-recurrence for `Ã`. -/
lemma Atil_rec (n : ℕ) :
    ((n : ℚ) + 2) ^ 2 * Atil (n + 2) - (12 * ((n : ℚ) + 1) * ((n : ℚ) + 2) + 4) * Atil (n + 1)
      + 32 * ((n : ℚ) + 1) ^ 2 * Atil n = 0 := by
  set N := n + 2 with hN
  have hmain := congrArg (fun p : ℚ[X] => p.coeff (n + 2)) (Lop_PG N)
  have hLHS : (4 * Lop (PG (N + 1))).coeff (n + 2)
      = 4 * (((n : ℚ) + 2) ^ 2 * (PG (N + 1)).coeff (n + 2)
          - (12 * ((n : ℚ) + 1) * ((n : ℚ) + 2) + 4) * (PG (N + 1)).coeff (n + 1)
          + 32 * ((n : ℚ) + 1) ^ 2 * (PG (N + 1)).coeff n) := by
    rw [show (4 : ℚ[X]) * Lop (PG (N + 1)) = C (4 : ℚ) * Lop (PG (N + 1)) by
      rw [map_ofNat]]
    rw [coeff_C_mul, Lop_coeff]
  have hRHS : ((16 * X - 128 * X ^ 2) *
      (-(C ((2 * (N : ℚ) + 1) ^ 2 * gco N) * zq ^ N))).coeff (n + 2) = 0 := by
    rw [coeff_prefactor]
    have h1 : (-(C ((2 * (N : ℚ) + 1) ^ 2 * gco N) * zq ^ N)).coeff (n + 1) = 0 := by
      rw [coeff_neg, coeff_C_mul, coeff_zq_pow_of_lt (by omega), mul_zero, neg_zero]
    have h0 : (-(C ((2 * (N : ℚ) + 1) ^ 2 * gco N) * zq ^ N)).coeff n = 0 := by
      rw [coeff_neg, coeff_C_mul, coeff_zq_pow_of_lt (by omega), mul_zero, neg_zero]
    rw [h1, h0]
    ring
  rw [hLHS, hRHS] at hmain
  rw [coeff_PG_eq (N + 1) (n + 2) (by omega), coeff_PG_eq (N + 1) (n + 1) (by omega),
    coeff_PG_eq (N + 1) n (by omega)] at hmain
  linarith [hmain]

/-- `A_n` is the coefficient sequence `Ã_n`. -/
theorem Ae_eq_Atil (n : ℕ) : Ae n = Atil n := by
  have h := rec2_unique (fun n => (LE n : ℚ)) (fun n => (CE n : ℚ)) (fun n => (RE n : ℚ)) 1 4
    Atil Atil_zero Atil_one
    (fun m => by
      show ((LE (m + 1) : ℤ) : ℚ) ≠ 0
      exact_mod_cast LE_ne_zero (m + 1))
    (fun m => by
      show ((LE (m + 1) : ℤ) : ℚ) * Atil (m + 2)
        = ((CE (m + 1) : ℤ) : ℚ) * Atil (m + 1) + ((RE (m + 1) : ℤ) : ℚ) * Atil m
      have hr := Atil_rec m
      have hL : ((LE (m + 1) : ℤ) : ℚ) = ((m : ℚ) + 2) ^ 2 := by unfold LE; push_cast; ring
      have hC : ((CE (m + 1) : ℤ) : ℚ) = 12 * ((m : ℚ) + 1) * ((m : ℚ) + 2) + 4 := by
        unfold CE; push_cast; ring
      have hR : ((RE (m + 1) : ℤ) : ℚ) = -32 * ((m : ℚ) + 1) ^ 2 := by unfold RE; push_cast; ring
      rw [hL, hC, hR]
      linarith [hr])
  rw [Ae, ← h n]

/-- **The Legendre closed form for the modular `E`-family denominator**:
`A_n = ∑_{k ≤ n} C(2k,k)² (-4)^{n-k} C(k, n-k)`. -/
theorem Ae_closed_form (n : ℕ) :
    Ae n = ∑ k ∈ range (n + 1),
      (Nat.centralBinom k : ℚ) ^ 2 * ((-4 : ℚ) ^ (n - k) * (k.choose (n - k))) := by
  rw [Ae_eq_Atil, Atil]
  unfold PG
  rw [Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_range] at hk
  rw [coeff_C_mul, coeff_zq_pow_of_le (by omega)]
  have h16 : ((16 : ℚ)) ^ k ≠ 0 := by positivity
  unfold gco
  field_simp

end Catalan
