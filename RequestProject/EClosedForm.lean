import RequestProject.ZPoly
import RequestProject.EFamily

/-!
# A closed form for the modular `E`-family numerator `B_n`

The denominator sequence `A_n` of the `E`-recurrence

`(n+1)² u_{n+1} = (12 n (n+1) + 4) u_n - 32 n² u_{n-1}`

has the closed form proved in `EIntegrality.lean`.  Here we prove the closed form of the
*numerator* solution `B_n` (`B_0 = 0`, `B_1 = 1`):

`B_n = ∑_{k ≤ n} C(2k,k)² c_k (-4)^{n-k} C(k, n-k)`,   `c_k = (1/4) ∑_{j<k} 4^j/(C(2j,j)(2j+1)²)`.

The proof is the polynomial ("Legendre substitution") argument.  Put `z = 16t(1-4t)` (`zq`) and

`w_k = C(2k,k)/(16·4^k)`,  `h_k = C(2k,k)² c_k / 16^k`,
`PW N = ∑_{k<N} w_k z^k`,  `PB N = ∑_{k<N} h_k z^k`.

The two chain-rule identities of `ZPoly.lean` turn the coefficient recurrences

`2(k+1) w_{k+1} = (2k+1) w_k`,   `4(k+1)² h_{k+1} - (2k+1)² h_k = 4 w_k`

into the two *telescoped* operator identities `Mop_PW` and `Lop_PB`.  Reading off coefficients
gives `[tⁿ] PW = 8ⁿ/16` and the `E`-recurrence for `[tⁿ] PB`; since `[t⁰]PB = 0`, `[t¹]PB = 1`,
uniqueness of the solution of a two-term recurrence (`rec2_unique`) identifies `[tⁿ]PB` with
`B_n`.
-/

namespace Catalan

open Polynomial Finset

/-! ### The two coefficient sequences -/

/-- `w_k = C(2k,k) / (16 · 4^k)`, the coefficient sequence of `(1-z)^{-1/2}/16`. -/
noncomputable def wco (k : ℕ) : ℚ := (Nat.centralBinom k : ℚ) / (16 * 4 ^ k)

/-- `c_k = (1/4) ∑_{j<k} 4^j / (C(2j,j) (2j+1)²)`, the harmonic-type weight. -/
noncomputable def cCoef (k : ℕ) : ℚ :=
  (1 / 4) * ∑ j ∈ range k, (4 : ℚ) ^ j / ((Nat.centralBinom j : ℚ) * (2 * j + 1) ^ 2)

/-- `h_k = C(2k,k)² c_k / 16^k`, the coefficient sequence of the second solution. -/
noncomputable def hco (k : ℕ) : ℚ := (Nat.centralBinom k : ℚ) ^ 2 * cCoef k / 16 ^ k

lemma centralBinom_ne_zero (k : ℕ) : (Nat.centralBinom k : ℚ) ≠ 0 := by
  exact_mod_cast (Nat.centralBinom_pos k).ne'

@[simp] lemma cCoef_zero : cCoef 0 = 0 := by simp [cCoef]

@[simp] lemma hco_zero : hco 0 = 0 := by simp [hco]

@[simp] lemma wco_zero : wco 0 = 1 / 16 := by norm_num [wco, Nat.centralBinom]

lemma cCoef_succ (k : ℕ) :
    cCoef (k + 1) = cCoef k + (1 / 4) * (4 : ℚ) ^ k / ((Nat.centralBinom k : ℚ) * (2 * k + 1) ^ 2) := by
  unfold cCoef
  rw [Finset.sum_range_succ]
  ring

lemma centralBinom_succ_cast (k : ℕ) :
    ((k : ℚ) + 1) * (Nat.centralBinom (k + 1) : ℚ) = 2 * (2 * k + 1) * (Nat.centralBinom k : ℚ) := by
  have h := Nat.succ_mul_centralBinom_succ k
  have := congrArg (fun m : ℕ => (m : ℚ)) h
  push_cast at this
  linarith [this]

/-- The recurrence `2(k+1) w_{k+1} = (2k+1) w_k`. -/
lemma wco_rec (k : ℕ) : 2 * ((k : ℚ) + 1) * wco (k + 1) = (2 * k + 1) * wco k := by
  have hc := centralBinom_succ_cast k
  have h4 : ((4 : ℚ)) ^ (k + 1) = 4 * 4 ^ k := by ring
  unfold wco
  rw [h4]
  have hpos : ((4 : ℚ)) ^ k ≠ 0 := by positivity
  field_simp
  linarith [hc]

/-- The recurrence `4(k+1)² h_{k+1} - (2k+1)² h_k = 4 w_k`. -/
lemma hco_rec (k : ℕ) :
    4 * ((k : ℚ) + 1) ^ 2 * hco (k + 1) - (2 * k + 1) ^ 2 * hco k = 4 * wco k := by
  have hb : (Nat.centralBinom k : ℚ) ≠ 0 := centralBinom_ne_zero k
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have h2k1 : (2 * (k : ℚ) + 1) ≠ 0 := by positivity
  have hB : (Nat.centralBinom (k + 1) : ℚ)
      = 2 * (2 * (k : ℚ) + 1) * (Nat.centralBinom k : ℚ) / ((k : ℚ) + 1) := by
    rw [eq_div_iff hk1]
    linarith [centralBinom_succ_cast k]
  obtain ⟨t, htne, hteq⟩ : ∃ t : ℚ, t ≠ 0 ∧ (4 : ℚ) ^ k = t := ⟨4 ^ k, by positivity, rfl⟩
  have h16k : ((16 : ℚ)) ^ k = t * t := by
    rw [← hteq, ← mul_pow]
    norm_num
  have h16s : ((16 : ℚ)) ^ (k + 1) = 16 * (t * t) := by
    rw [pow_succ, h16k]
    ring
  unfold hco wco
  rw [cCoef_succ, hB, h16s, h16k, hteq]
  field_simp
  ring

/-! ### The two truncated polynomials -/

/-- `PW N = ∑_{k<N} w_k z^k`. -/
noncomputable def PW (N : ℕ) : ℚ[X] := ∑ k ∈ range N, C (wco k) * zq ^ k

/-- `PB N = ∑_{k<N} h_k z^k`. -/
noncomputable def PB (N : ℕ) : ℚ[X] := ∑ k ∈ range N, C (hco k) * zq ^ k

lemma Mop_C_mul (a : ℚ) (p : ℚ[X]) : Mop (C a * p) = C a * Mop p := by
  have h := Mop_smul a p
  simpa [smul_eq_C_mul] using h

lemma Lop_C_mul (a : ℚ) (p : ℚ[X]) : Lop (C a * p) = C a * Lop p := by
  have h := Lop_smul a p
  simpa [smul_eq_C_mul] using h

/-- The unified chain-rule identity for `L`. -/
lemma Lop_zq_pow_succ (k : ℕ) :
    4 * Lop (zq ^ (k + 1)) = (16 * X - 128 * X ^ 2) *
      (4 * ((k : ℚ[X]) + 1) ^ 2 * zq ^ k - (2 * (k : ℚ[X]) + 3) ^ 2 * zq ^ (k + 1)) := by
  cases k with
  | zero =>
      rw [show (0 : ℕ) + 1 = 1 from rfl, Lop_zq_pow_one]
      norm_num
  | succ m =>
      have h := Lop_zq_pow_two_add m
      rw [show m + 1 + 1 = m + 2 from rfl]
      rw [h]
      push_cast
      ring

/-- The telescoped identity for `M`: `M[PW (N+1)] = -8(2N+1) w_N z^N`. -/
lemma Mop_PW (N : ℕ) : Mop (PW (N + 1)) = C (-8 * (2 * (N : ℚ) + 1) * wco N) * zq ^ N := by
  induction N with
  | zero =>
      have hPW : PW (0 + 1) = C (wco 0) * zq ^ 0 := by simp [PW]
      have hC8 : (C (-8 : ℚ)) = -8 := by rw [map_neg, map_ofNat]
      have hM : Mop (zq ^ 0) = C (-8 : ℚ) := by rw [hC8]; simp [Mop]
      have harg : wco 0 * (-8 : ℚ) = -8 * (2 * ((0 : ℕ) : ℚ) + 1) * wco 0 := by
        push_cast
        ring
      rw [hPW, Mop_C_mul, hM, ← map_mul, pow_zero, mul_one, harg]
  | succ M ih =>
      have hsplit : PW (M + 2) = PW (M + 1) + C (wco (M + 1)) * zq ^ (M + 1) := by
        simp [PW, Finset.sum_range_succ]
      rw [hsplit, Mop_add, ih, Mop_C_mul, Mop_zq_pow_succ]
      have hrec := wco_rec M
      have hC : C (2 * ((M : ℚ) + 1) * wco (M + 1)) = C ((2 * (M : ℚ) + 1) * wco M) := by
        rw [hrec]
      simp only [map_mul, map_add, map_ofNat, map_natCast, map_neg, map_one] at hC ⊢
      push_cast
      linear_combination (8 * zq ^ M) * hC

/-- The telescoped identity for `L`:
`4 L[PB (N+1)] = 16t(1-8t) (4 PW N - (2N+1)² h_N z^N)`. -/
lemma Lop_PB (N : ℕ) :
    4 * Lop (PB (N + 1)) =
      (16 * X - 128 * X ^ 2) * (4 * PW N - C ((2 * (N : ℚ) + 1) ^ 2 * hco N) * zq ^ N) := by
  induction N with
  | zero => simp [PB, PW, Lop, theta]
  | succ M ih =>
      have hsplitB : PB (M + 2) = PB (M + 1) + C (hco (M + 1)) * zq ^ (M + 1) := by
        simp [PB, Finset.sum_range_succ]
      have hsplitW : PW (M + 1) = PW M + C (wco M) * zq ^ M := by
        simp [PW, Finset.sum_range_succ]
      rw [hsplitB, Lop_add, mul_add, ih, Lop_C_mul, hsplitW]
      have hLz : 4 * (C (hco (M + 1)) * Lop (zq ^ (M + 1)))
          = C (hco (M + 1)) * ((16 * X - 128 * X ^ 2) *
            (4 * ((M : ℚ[X]) + 1) ^ 2 * zq ^ M - (2 * (M : ℚ[X]) + 3) ^ 2 * zq ^ (M + 1))) := by
        rw [← Lop_zq_pow_succ M]
        ring
      rw [hLz]
      have hrec := hco_rec M
      have hC : C (4 * ((M : ℚ) + 1) ^ 2 * hco (M + 1) - (2 * (M : ℚ) + 1) ^ 2 * hco M)
          = C (4 * wco M) := by rw [hrec]
      simp only [map_mul, map_add, map_sub, map_ofNat, map_natCast, map_pow, map_one] at hC ⊢
      push_cast
      linear_combination ((16 * X - 128 * X ^ 2) * zq ^ M) * hC

/-! ### Reading off the coefficients -/

lemma coeff_PW_zero (N : ℕ) : (PW (N + 1)).coeff 0 = 1 / 16 := by
  unfold PW
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    rw [coeff_C_mul, coeff_zq_pow_of_lt (by omega), mul_zero]
  · intro h
    simp at h

/-- `[tⁿ] PW N = 8ⁿ/16` for `n < N`. -/
lemma coeff_PW (N n : ℕ) (h : n < N) : (PW N).coeff n = 8 ^ n / 16 := by
  induction n generalizing N with
  | zero =>
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      simpa using coeff_PW_zero M
  | succ m ih =>
      obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
      have hM : m < M := by omega
      have hmM : m < M + 1 := by omega
      have hstep := congrArg (fun p : ℚ[X] => p.coeff m) (Mop_PW M)
      simp only [Mop_coeff, coeff_C_mul, coeff_zq_pow_of_lt hM, mul_zero] at hstep
      have hm := ih (M + 1) hmM
      rw [hm] at hstep
      have hne : ((m : ℚ) + 1) ≠ 0 := by positivity
      have hstep2 : ((m : ℚ) + 1) * (PW (M + 1)).coeff (m + 1)
          = ((m : ℚ) + 1) * (8 ^ (m + 1) / 16) := by linear_combination hstep
      exact mul_left_cancel₀ hne hstep2

/-! ### The `E`-recurrence for the coefficients of `PB` -/

/-- The truncated coefficient sum `B̃_n = [tⁿ] PB (n+1)`. -/
noncomputable def Btil (n : ℕ) : ℚ := (PB (n + 1)).coeff n

lemma coeff_PB_eq (N n : ℕ) (h : n < N) : (PB N).coeff n = Btil n := by
  have key : ∀ M : ℕ, n < M → (PB M).coeff n = ∑ k ∈ range (n + 1), hco k * (zq ^ k).coeff n := by
    intro M hM
    unfold PB
    rw [Polynomial.finset_sum_coeff]
    have hsub : range (n + 1) ⊆ range M := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    have hzero : ∀ k ∈ range M, k ∉ range (n + 1) → (C (hco k) * zq ^ k).coeff n = 0 := by
      intro k _ hk
      simp only [Finset.mem_range, not_lt] at hk
      rw [coeff_C_mul, coeff_zq_pow_of_lt (by omega), mul_zero]
    rw [← Finset.sum_subset hsub hzero]
    exact Finset.sum_congr rfl (fun k _ => by rw [coeff_C_mul])
  rw [key N h, Btil, key (n + 1) (by omega)]

@[simp] lemma Btil_zero : Btil 0 = 0 := by
  simp [Btil, PB]

@[simp] lemma Btil_one : Btil 1 = 1 := by
  have h : PB 2 = C (hco 0) * zq ^ 0 + C (hco 1) * zq ^ 1 := by
    simp [PB, Finset.sum_range_succ]
  have hh1 : hco 1 = 1 / 16 := by
    norm_num [hco, cCoef, Nat.centralBinom]
  simp only [Btil, h, coeff_C_mul, hco_zero, map_zero, zero_mul, zero_add, hh1,
    pow_one]
  rw [show (zq : ℚ[X]) = zq ^ 1 by ring, coeff_zq_pow_of_le (by norm_num)]
  norm_num

/-- The `E`-recurrence for `B̃`. -/
lemma Btil_rec (n : ℕ) :
    ((n : ℚ) + 2) ^ 2 * Btil (n + 2) - (12 * ((n : ℚ) + 1) * ((n : ℚ) + 2) + 4) * Btil (n + 1)
      + 32 * ((n : ℚ) + 1) ^ 2 * Btil n = 0 := by
  set N := n + 2 with hN
  have hmain := congrArg (fun p : ℚ[X] => p.coeff (n + 2)) (Lop_PB N)
  -- left-hand side
  have hLHS : (4 * Lop (PB (N + 1))).coeff (n + 2)
      = 4 * (((n : ℚ) + 2) ^ 2 * (PB (N + 1)).coeff (n + 2)
          - (12 * ((n : ℚ) + 1) * ((n : ℚ) + 2) + 4) * (PB (N + 1)).coeff (n + 1)
          + 32 * ((n : ℚ) + 1) ^ 2 * (PB (N + 1)).coeff n) := by
    rw [show (4 : ℚ[X]) * Lop (PB (N + 1)) = C (4 : ℚ) * Lop (PB (N + 1)) by
      rw [map_ofNat]]
    rw [coeff_C_mul, Lop_coeff]
  -- right-hand side
  have hRHS : ((16 * X - 128 * X ^ 2) *
      (4 * PW N - C ((2 * (N : ℚ) + 1) ^ 2 * hco N) * zq ^ N)).coeff (n + 2) = 0 := by
    rw [coeff_prefactor]
    have h1 : (4 * PW N - C ((2 * (N : ℚ) + 1) ^ 2 * hco N) * zq ^ N).coeff (n + 1)
        = 4 * (8 ^ (n + 1) / 16) := by
      rw [coeff_sub, coeff_C_mul, coeff_zq_pow_of_lt (by omega), mul_zero, sub_zero,
        show (4 : ℚ[X]) * PW N = C (4 : ℚ) * PW N by rw [map_ofNat], coeff_C_mul,
        coeff_PW N (n + 1) (by omega)]
    have h0 : (4 * PW N - C ((2 * (N : ℚ) + 1) ^ 2 * hco N) * zq ^ N).coeff n
        = 4 * (8 ^ n / 16) := by
      rw [coeff_sub, coeff_C_mul, coeff_zq_pow_of_lt (by omega), mul_zero, sub_zero,
        show (4 : ℚ[X]) * PW N = C (4 : ℚ) * PW N by rw [map_ofNat], coeff_C_mul,
        coeff_PW N n (by omega)]
    rw [h1, h0]
    ring
  rw [hLHS, hRHS] at hmain
  rw [coeff_PB_eq (N + 1) (n + 2) (by omega), coeff_PB_eq (N + 1) (n + 1) (by omega),
    coeff_PB_eq (N + 1) n (by omega)] at hmain
  linarith [hmain]

/-- `B_n` is the coefficient sequence `B̃_n`. -/
theorem Be_eq_Btil (n : ℕ) : Be n = Btil n := by
  have h := rec2_unique (fun n => (LE n : ℚ)) (fun n => (CE n : ℚ)) (fun n => (RE n : ℚ)) 0 1
    Btil Btil_zero Btil_one
    (fun m => by
      show ((LE (m + 1) : ℤ) : ℚ) ≠ 0
      exact_mod_cast LE_ne_zero (m + 1))
    (fun m => by
      show ((LE (m + 1) : ℤ) : ℚ) * Btil (m + 2)
        = ((CE (m + 1) : ℤ) : ℚ) * Btil (m + 1) + ((RE (m + 1) : ℤ) : ℚ) * Btil m
      have hr := Btil_rec m
      have hL : ((LE (m + 1) : ℤ) : ℚ) = ((m : ℚ) + 2) ^ 2 := by unfold LE; push_cast; ring
      have hC : ((CE (m + 1) : ℤ) : ℚ) = 12 * ((m : ℚ) + 1) * ((m : ℚ) + 2) + 4 := by
        unfold CE; push_cast; ring
      have hR : ((RE (m + 1) : ℤ) : ℚ) = -32 * ((m : ℚ) + 1) ^ 2 := by unfold RE; push_cast; ring
      rw [hL, hC, hR]
      linarith [hr])
  rw [Be, ← h n]

/-- **The closed form for the modular `E`-family numerator**:
`B_n = ∑_{k ≤ n} C(2k,k)² c_k (-4)^{n-k} C(k, n-k)`. -/
theorem Be_closed_form (n : ℕ) :
    Be n = ∑ k ∈ range (n + 1),
      (Nat.centralBinom k : ℚ) ^ 2 * cCoef k * ((-4 : ℚ) ^ (n - k) * (k.choose (n - k))) := by
  rw [Be_eq_Btil, Btil]
  unfold PB
  rw [Polynomial.finset_sum_coeff]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  simp only [Finset.mem_range] at hk
  rw [coeff_C_mul, coeff_zq_pow_of_le (by omega)]
  have h16 : ((16 : ℚ)) ^ k ≠ 0 := by positivity
  unfold hco
  field_simp

end Catalan
