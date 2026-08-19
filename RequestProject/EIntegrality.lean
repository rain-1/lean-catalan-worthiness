import RequestProject.EFamily

/-!
# Integrality of the modular `E`-family denominators

The denominator sequence `A_n` of the modular `E`-recurrence

`(n+1)² A_{n+1} = (12 n (n+1) + 4) A_n - 32 n² A_{n-1}`,  `A_0 = 1`, `A_1 = 4`

is defined by that recurrence, hence a priori only rational.  Here we prove the closed form

`A_n = ∑_{k ≤ n} C(n,k) C(2k,k) C(2n-2k, n-k)`,

which exhibits `A_n` as a *natural number*: this is the integrality half of Imported Theorem E.

The proof is a creative-telescoping (Zeilberger) computation.  With

`T(n,k) = C(n,k) C(2k,k) C(2(n-k), n-k)`,
`G(n,k) = 2k² (2kn - 2n² - n + 1) T(n,k) / (n+1-k)²`,

one has, for `k + 1 ≤ n`,

`(n+1)² T(n+1,k) - (12n(n+1)+4) T(n,k) + 32 n² T(n-1,k) = G(n,k+1) - G(n,k)`,

which is `eT_telescope`.  Summing over `k` and adding the two boundary terms `k = n`, `k = n+1`
gives the recurrence for the sum (`eSum_rec`), and uniqueness of the solution of a two-term
recurrence identifies it with `A_n` (`Ae_eq_eSum`).
-/

namespace Catalan

open Finset

/-- The summand `T(n,k) = C(n,k) C(2k,k) C(2(n-k), n-k)`. -/
def eT (n k : ℕ) : ℕ := n.choose k * Nat.centralBinom k * Nat.centralBinom (n - k)

/-- The closed form `∑_{k ≤ n} T(n,k)`, a natural number. -/
def eSum (n : ℕ) : ℕ := ∑ k ∈ range (n + 1), eT n k

lemma eT_eq_zero_of_lt {n k : ℕ} (h : n < k) : eT n k = 0 := by
  unfold eT
  rw [Nat.choose_eq_zero_of_lt h]
  ring

@[simp] lemma eT_self (n : ℕ) : eT n n = Nat.centralBinom n := by
  simp [eT, Nat.centralBinom]

/-- The telescoping certificate `G(n,k) = 2k² (2kn - 2n² - n + 1) T(n,k) / (n+1-k)²`. -/
def gT (n k : ℕ) : ℚ :=
  2 * (k : ℚ) ^ 2 * (2 * (k : ℚ) * (n : ℚ) - 2 * (n : ℚ) ^ 2 - (n : ℚ) + 1) * (eT n k : ℚ)
    / ((n : ℚ) + 1 - (k : ℚ)) ^ 2

@[simp] lemma gT_zero (n : ℕ) : gT n 0 = 0 := by simp [gT]

/-! ### The creative-telescoping step -/

/-- The Zeilberger telescoping relation, for `k ≤ m` (i.e. `k + 1 ≤ n` with `n = m + 1`). -/
lemma eT_telescope (m k : ℕ) (hk : k ≤ m) :
    ((m : ℚ) + 2) ^ 2 * (eT (m + 2) k : ℚ)
      - (12 * ((m : ℚ) + 1) * ((m : ℚ) + 2) + 4) * (eT (m + 1) k : ℚ)
      + 32 * ((m : ℚ) + 1) ^ 2 * (eT m k : ℚ)
      = gT (m + 1) (k + 1) - gT (m + 1) k := by
  obtain ⟨i, rfl⟩ : ∃ i, m = k + i := ⟨m - k, by omega⟩
  -- the natural-number contiguity relations
  have n1 : (k + i + 1).choose k * (k + i + 2) = (k + i + 2).choose k * (i + 2) := by
    have h := Nat.choose_mul_succ_eq (k + i + 1) k
    have he : k + i + 1 + 1 - k = i + 2 := by omega
    rw [he] at h
    simpa [Nat.add_assoc] using h
  have n2 : (k + i).choose k * (k + i + 1) = (k + i + 1).choose k * (i + 1) := by
    have h := Nat.choose_mul_succ_eq (k + i) k
    have he : k + i + 1 - k = i + 1 := by omega
    rw [he] at h
    exact h
  have n3 : (k + i + 1).choose (k + 1) * (k + 1) = (k + i + 1).choose k * (i + 1) := by
    have h := Nat.choose_succ_right_eq (k + i + 1) k
    have he : k + i + 1 - k = i + 1 := by omega
    rw [he] at h
    exact h
  have n4 : (i + 1) * Nat.centralBinom (i + 1) = 2 * (2 * i + 1) * Nat.centralBinom i :=
    Nat.succ_mul_centralBinom_succ i
  have n5 : (i + 2) * Nat.centralBinom (i + 2) = 2 * (2 * i + 3) * Nat.centralBinom (i + 1) := by
    have h := Nat.succ_mul_centralBinom_succ (i + 1)
    simpa [Nat.add_assoc, show 2 * (i + 1) + 1 = 2 * i + 3 by ring] using h
  have n6 : (k + 1) * Nat.centralBinom (k + 1) = 2 * (2 * k + 1) * Nat.centralBinom k :=
    Nat.succ_mul_centralBinom_succ k
  -- the four values of `T`
  have t1 : eT (k + i + 2) k
      = (k + i + 2).choose k * Nat.centralBinom k * Nat.centralBinom (i + 2) := by
    unfold eT
    congr 2
    omega
  have t2 : eT (k + i + 1) k
      = (k + i + 1).choose k * Nat.centralBinom k * Nat.centralBinom (i + 1) := by
    unfold eT
    congr 2
    omega
  have t3 : eT (k + i) k = (k + i).choose k * Nat.centralBinom k * Nat.centralBinom i := by
    unfold eT
    congr 2
    omega
  have t4 : eT (k + i + 1) (k + 1)
      = (k + i + 1).choose (k + 1) * Nat.centralBinom (k + 1) * Nat.centralBinom i := by
    unfold eT
    congr 2
    omega
  -- move to `ℚ`
  have q1 : ((k + i + 2).choose k : ℚ) * ((i : ℚ) + 2)
      = ((k + i + 1).choose k : ℚ) * ((k : ℚ) + (i : ℚ) + 2) := by
    have := congrArg (fun z : ℕ => (z : ℚ)) n1
    push_cast at this
    linarith [this]
  have q2 : ((k + i).choose k : ℚ) * ((k : ℚ) + (i : ℚ) + 1)
      = ((k + i + 1).choose k : ℚ) * ((i : ℚ) + 1) := by
    have := congrArg (fun z : ℕ => (z : ℚ)) n2
    push_cast at this
    linarith [this]
  have q3 : ((k + i + 1).choose (k + 1) : ℚ) * ((k : ℚ) + 1)
      = ((k + i + 1).choose k : ℚ) * ((i : ℚ) + 1) := by
    have := congrArg (fun z : ℕ => (z : ℚ)) n3
    push_cast at this
    linarith [this]
  have q4 : ((i : ℚ) + 1) * (Nat.centralBinom (i + 1) : ℚ)
      = 2 * (2 * (i : ℚ) + 1) * (Nat.centralBinom i : ℚ) := by
    have := congrArg (fun z : ℕ => (z : ℚ)) n4
    push_cast at this
    linarith [this]
  have q5 : ((i : ℚ) + 2) * (Nat.centralBinom (i + 2) : ℚ)
      = 2 * (2 * (i : ℚ) + 3) * (Nat.centralBinom (i + 1) : ℚ) := by
    have := congrArg (fun z : ℕ => (z : ℚ)) n5
    push_cast at this
    linarith [this]
  have q6 : ((k : ℚ) + 1) * (Nat.centralBinom (k + 1) : ℚ)
      = 2 * (2 * (k : ℚ) + 1) * (Nat.centralBinom k : ℚ) := by
    have := congrArg (fun z : ℕ => (z : ℚ)) n6
    push_cast at this
    linarith [this]
  -- solve for the shifted quantities
  have hi1 : ((i : ℚ) + 1) ≠ 0 := by positivity
  have hi2 : ((i : ℚ) + 2) ≠ 0 := by positivity
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hn1 : ((k : ℚ) + (i : ℚ) + 1) ≠ 0 := by positivity
  have e1 : ((k + i + 2).choose k : ℚ)
      = ((k + i + 1).choose k : ℚ) * ((k : ℚ) + (i : ℚ) + 2) / ((i : ℚ) + 2) := by
    field_simp
    linarith [q1]
  have e2 : ((k + i).choose k : ℚ)
      = ((k + i + 1).choose k : ℚ) * ((i : ℚ) + 1) / ((k : ℚ) + (i : ℚ) + 1) := by
    field_simp
    linarith [q2]
  have e3 : ((k + i + 1).choose (k + 1) : ℚ)
      = ((k + i + 1).choose k : ℚ) * ((i : ℚ) + 1) / ((k : ℚ) + 1) := by
    field_simp
    linarith [q3]
  have e4 : (Nat.centralBinom (i + 1) : ℚ)
      = 2 * (2 * (i : ℚ) + 1) * (Nat.centralBinom i : ℚ) / ((i : ℚ) + 1) := by
    field_simp
    linarith [q4]
  have e5 : (Nat.centralBinom (i + 2) : ℚ)
      = 4 * (2 * (i : ℚ) + 1) * (2 * (i : ℚ) + 3) * (Nat.centralBinom i : ℚ)
          / (((i : ℚ) + 1) * ((i : ℚ) + 2)) := by
    rw [show (Nat.centralBinom (i + 2) : ℚ)
        = 2 * (2 * (i : ℚ) + 3) * (Nat.centralBinom (i + 1) : ℚ) / ((i : ℚ) + 2) by
      field_simp; linarith [q5], e4]
    field_simp
    ring
  have e6 : (Nat.centralBinom (k + 1) : ℚ)
      = 2 * (2 * (k : ℚ) + 1) * (Nat.centralBinom k : ℚ) / ((k : ℚ) + 1) := by
    field_simp
    linarith [q6]
  -- expand everything
  have hcast : ∀ a b c : ℕ, ((a * b * c : ℕ) : ℚ) = (a : ℚ) * (b : ℚ) * (c : ℚ) := by
    intro a b c; push_cast; ring
  unfold gT
  rw [t1, t2, t3, t4, hcast, hcast, hcast, hcast, e1, e2, e3, e4, e5, e6]
  have hd1 : ((k : ℚ) + (i : ℚ) + 1) + 1 - (k : ℚ) = (i : ℚ) + 2 := by ring
  have hd2 : ((k : ℚ) + (i : ℚ) + 1) + 1 - ((k : ℚ) + 1) = (i : ℚ) + 1 := by ring
  push_cast
  rw [show ((k : ℚ) + (i : ℚ) + 1 + 1 - (k : ℚ)) = (i : ℚ) + 2 by ring,
    show ((k : ℚ) + (i : ℚ) + 1 + 1 - ((k : ℚ) + 1)) = (i : ℚ) + 1 by ring]
  field_simp
  ring

/-! ### The recurrence for the closed form -/

lemma eSum_rec (m : ℕ) :
    ((m : ℚ) + 2) ^ 2 * (eSum (m + 2) : ℚ)
      = (12 * ((m : ℚ) + 1) * ((m : ℚ) + 2) + 4) * (eSum (m + 1) : ℚ)
        - 32 * ((m : ℚ) + 1) ^ 2 * (eSum m : ℚ) := by
  -- all three sums over the common range `range (m+3)`
  have hs2 : (eSum (m + 2) : ℚ) = ∑ k ∈ range (m + 3), (eT (m + 2) k : ℚ) := by
    unfold eSum
    push_cast
    rfl
  have hs1 : (eSum (m + 1) : ℚ) = ∑ k ∈ range (m + 3), (eT (m + 1) k : ℚ) := by
    rw [show m + 3 = (m + 2) + 1 from rfl, Finset.sum_range_succ,
      eT_eq_zero_of_lt (show m + 1 < m + 2 by omega)]
    simp [eSum]
  have hs0 : (eSum m : ℚ) = ∑ k ∈ range (m + 3), (eT m k : ℚ) := by
    rw [show m + 3 = ((m + 1) + 1) + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
      eT_eq_zero_of_lt (show m < m + 2 by omega), eT_eq_zero_of_lt (show m < m + 1 by omega)]
    simp [eSum]
  have hsplit : ∑ k ∈ range (m + 3),
      (((m : ℚ) + 2) ^ 2 * (eT (m + 2) k : ℚ)
        - (12 * ((m : ℚ) + 1) * ((m : ℚ) + 2) + 4) * (eT (m + 1) k : ℚ)
        + 32 * ((m : ℚ) + 1) ^ 2 * (eT m k : ℚ)) = 0 := by
    rw [show m + 3 = ((m + 1) + 1) + 1 from rfl, Finset.sum_range_succ, Finset.sum_range_succ]
    have htel : ∑ k ∈ range (m + 1),
        (((m : ℚ) + 2) ^ 2 * (eT (m + 2) k : ℚ)
          - (12 * ((m : ℚ) + 1) * ((m : ℚ) + 2) + 4) * (eT (m + 1) k : ℚ)
          + 32 * ((m : ℚ) + 1) ^ 2 * (eT m k : ℚ))
        = gT (m + 1) (m + 1) - gT (m + 1) 0 := by
      rw [← Finset.sum_range_sub (fun k => gT (m + 1) k) (m + 1)]
      refine Finset.sum_congr rfl (fun k hk => ?_)
      exact eT_telescope m k (by have := Finset.mem_range.mp hk; omega)
    rw [htel, gT_zero]
    -- the two boundary terms
    have hb1 : eT (m + 2) (m + 1) = (m + 2) * Nat.centralBinom (m + 1) * 2 := by
      unfold eT
      rw [show m + 2 - (m + 1) = 1 by omega, Nat.choose_succ_self_right]
      simp [Nat.centralBinom]
    have hb2 : eT (m + 1) (m + 1) = Nat.centralBinom (m + 1) := eT_self (m + 1)
    have hb3 : eT m (m + 1) = 0 := eT_eq_zero_of_lt (by omega)
    have hb4 : eT (m + 2) (m + 2) = Nat.centralBinom (m + 2) := eT_self (m + 2)
    have hb5 : eT (m + 1) (m + 2) = 0 := eT_eq_zero_of_lt (by omega)
    have hb6 : eT m (m + 2) = 0 := eT_eq_zero_of_lt (by omega)
    have hgT : gT (m + 1) (m + 1)
        = -2 * ((m : ℚ) + 1) ^ 2 * (m : ℚ) * (Nat.centralBinom (m + 1) : ℚ) := by
      unfold gT
      rw [eT_self]
      push_cast
      rw [show ((m : ℚ) + 1 + 1 - ((m : ℚ) + 1)) = 1 by ring]
      ring
    have hc : ((m : ℚ) + 2) * (Nat.centralBinom (m + 2) : ℚ)
        = 2 * (2 * (m : ℚ) + 3) * (Nat.centralBinom (m + 1) : ℚ) := by
      have h := Nat.succ_mul_centralBinom_succ (m + 1)
      have := congrArg (fun z : ℕ => (z : ℚ)) h
      push_cast at this
      linarith [this]
    rw [hgT, hb1, hb2, hb3, hb4, hb5, hb6]
    push_cast
    nlinarith [hc, sq_nonneg ((m : ℚ) + 2)]
  rw [hs0, hs1, hs2]
  have := hsplit
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum] at this
  linarith [this]

/-! ### Identification with `A_n` -/

@[simp] lemma eSum_zero : eSum 0 = 1 := by decide

@[simp] lemma eSum_one : eSum 1 = 4 := by decide

/-- The closed form: `A_n = ∑_{k ≤ n} C(n,k) C(2k,k) C(2n-2k, n-k)`. -/
theorem Ae_eq_eSum (n : ℕ) : Ae n = (eSum n : ℚ) := by
  refine (rec2_unique (fun n => (LE n : ℚ)) (fun n => (CE n : ℚ)) (fun n => (RE n : ℚ)) 1 4
    (fun n => (eSum n : ℚ)) (by simp) (by simp)
    (fun m => by show ((LE (m + 1) : ℤ) : ℚ) ≠ 0; exact_mod_cast LE_ne_zero (m + 1)) (fun m => ?_) n).symm
  have h := eSum_rec m
  unfold LE CE RE
  push_cast
  nlinarith [h]

/-- The integrality half of Imported Theorem E: `A_n` is a natural number. -/
theorem Ae_isNat (n : ℕ) : ∃ z : ℕ, Ae n = (z : ℚ) := ⟨eSum n, Ae_eq_eSum n⟩

/-- `A_n` as an integer. -/
def AeInt (n : ℕ) : ℤ := (eSum n : ℤ)

@[simp] theorem AeInt_cast (n : ℕ) : ((AeInt n : ℤ) : ℚ) = Ae n := by
  rw [AeInt, Ae_eq_eSum]
  push_cast
  ring

/-- The integer first row `A_{6n}` of Definition 15.1, no longer an imported hypothesis. -/
def a1row (n : ℕ) : ℤ := AeInt (6 * n)

@[simp] theorem a1row_cast (n : ℕ) : ((a1row n : ℤ) : ℚ) = Ae (6 * n) := AeInt_cast (6 * n)

end Catalan
