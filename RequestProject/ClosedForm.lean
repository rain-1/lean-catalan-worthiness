import RequestProject.PadeRec

/-!
# A closed form for Beukers' Padé denominators

Beukers' Padé denominator `q_n(x)` (`bq` of `Beukers.lean`) is the solution of

`(n+1)² u_{n+1} = (2n(n+1) + 1 - x + x²) u_n - n² u_{n-1}`,  `u_0 = 1`, `u_1 = x² - x + 1`.

Since the recurrence only involves `x` through `y = x² - x`, the solution is a polynomial in
`y`, and in the basis `β_k(y) = ∏_{j<k} (y - j(j+1))` it has the explicit form

`q_n(x) = ∑_{k=0}^{n} (n choose k) β_k(y) / (k!)²`.

This is proved here (`bq_eq_qSum`) by checking that the right-hand side satisfies the same
recurrence; the verification is a telescoping (Zeilberger-style) computation with the explicit
certificate `F k = -k(k+1) (n choose k) β_k(y)/(k!)²`.
-/

namespace Catalan

open Finset

/-- `β_k(y) = ∏_{j<k} (y - j(j+1))`. -/
def betaCoef (y : ℚ) (k : ℕ) : ℚ := ∏ j ∈ range k, (y - (j : ℚ) * ((j : ℚ) + 1))

/-- `g_k(y) = β_k(y)/(k!)²`. -/
def gCoef (y : ℚ) (k : ℕ) : ℚ := betaCoef y k / (k.factorial : ℚ) ^ 2

@[simp] lemma betaCoef_zero (y : ℚ) : betaCoef y 0 = 1 := by simp [betaCoef]

@[simp] lemma gCoef_zero (y : ℚ) : gCoef y 0 = 1 := by simp [gCoef]

lemma betaCoef_succ (y : ℚ) (k : ℕ) :
    betaCoef y (k + 1) = betaCoef y k * (y - (k : ℚ) * ((k : ℚ) + 1)) :=
  prod_range_succ _ _

lemma factorial_ne_zero_rat (k : ℕ) : ((k.factorial : ℚ)) ≠ 0 := by
  exact_mod_cast (Nat.factorial_pos k).ne'

lemma gCoef_succ (y : ℚ) (k : ℕ) :
    ((k : ℚ) + 1) ^ 2 * gCoef y (k + 1) = (y - (k : ℚ) * ((k : ℚ) + 1)) * gCoef y k := by
  have hk := factorial_ne_zero_rat k
  unfold gCoef
  rw [betaCoef_succ, Nat.factorial_succ]
  push_cast
  field_simp

/-! ### Two binomial identities, over `ℚ` -/

/-- `(n+1) · C(n,k) = (n+1-k) · C(n+1,k)`, over `ℚ` (so valid for every `k`). -/
lemma cast_choose_pred (i k : ℕ) :
    ((i : ℚ) + 1) * (i.choose k : ℚ) = ((i : ℚ) + 1 - (k : ℚ)) * ((i + 1).choose k : ℚ) := by
  rcases le_or_gt k (i + 1) with hk | hk
  · have hnat : (i + 1) * i.choose k = (i + 1).choose k * ((i + 1) - k) := by
      have h1 : (i + 1) * i.choose k = (i + 1).choose (k + 1) * (k + 1) :=
        Nat.add_one_mul_choose_eq i k
      have h2 : (i + 1).choose (k + 1) * (k + 1) = (i + 1).choose k * ((i + 1) - k) :=
        Nat.choose_succ_right_eq _ _
      rw [h1, h2]
    have := congrArg (fun n : ℕ => (n : ℚ)) hnat
    push_cast [Nat.cast_sub hk] at this
    linarith [this]
  · have h1 : i.choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have h2 : (i + 1).choose k = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h1, h2]
    simp

/-- `(k+1) · C(n,k+1) = (n-k) · C(n,k)`, over `ℚ` (so valid for every `k`). -/
lemma cast_choose_succ (n k : ℕ) :
    ((k : ℚ) + 1) * (n.choose (k + 1) : ℚ) = ((n : ℚ) - (k : ℚ)) * (n.choose k : ℚ) := by
  rcases le_or_gt k n with hk | hk
  · have hnat : n.choose (k + 1) * (k + 1) = n.choose k * (n - k) := Nat.choose_succ_right_eq _ _
    have := congrArg (fun m : ℕ => (m : ℚ)) hnat
    push_cast [Nat.cast_sub hk] at this
    linarith [this]
  · have h1 : n.choose k = 0 := Nat.choose_eq_zero_of_lt hk
    have h2 : n.choose (k + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h1, h2]
    simp

/-! ### The closed-form sum -/

/-- The closed-form sum, truncated at `N`. -/
def qPart (y : ℚ) (n N : ℕ) : ℚ := ∑ k ∈ range N, (n.choose k : ℚ) * gCoef y k

/-- The closed form `∑_{k≤n} (n choose k) β_k(y)/(k!)²`. -/
def qSum (y : ℚ) (n : ℕ) : ℚ := qPart y n (n + 1)

lemma qPart_eq_qSum (y : ℚ) {n N : ℕ} (h : n + 1 ≤ N) : qPart y n N = qSum y n := by
  unfold qPart qSum qPart
  refine (Finset.sum_subset (by simpa using h) ?_).symm
  intro k _ hk
  have : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by simpa using hk)
  simp [this]

/-- The Pascal step: `S_{n+1} = S_n + A_n` with `A_n = ∑_k C(n,k) g_{k+1}`. -/
lemma qPart_succ (y : ℚ) (n N : ℕ) :
    qPart y (n + 1) (N + 1) =
      qPart y n (N + 1) + ∑ k ∈ range N, (n.choose k : ℚ) * gCoef y (k + 1) := by
  unfold qPart
  rw [sum_range_succ' (fun k => ((n + 1).choose k : ℚ) * gCoef y k) N,
    sum_range_succ' (fun k => (n.choose k : ℚ) * gCoef y k) N]
  have : ∀ k ∈ range N, ((n + 1).choose (k + 1) : ℚ) * gCoef y (k + 1) =
      (n.choose (k + 1) : ℚ) * gCoef y (k + 1) + (n.choose k : ℚ) * gCoef y (k + 1) := by
    intro k _
    rw [Nat.choose_succ_succ n k]
    push_cast
    ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
  simp
  ring

/-- The telescoping certificate. -/
def qCert (y : ℚ) (i k : ℕ) : ℚ :=
  -((k : ℚ) * ((k : ℚ) + 1)) * ((i + 1).choose k : ℚ) * gCoef y k

lemma qCert_zero (y : ℚ) (i : ℕ) : qCert y i 0 = 0 := by simp [qCert]

/-- The termwise telescoping identity behind the recurrence. -/
lemma qCert_step (y : ℚ) (i k : ℕ) :
    ((i : ℚ) + 2) ^ 2 * (((i + 1).choose k : ℚ) * gCoef y (k + 1))
      - ((i : ℚ) + 1) ^ 2 * ((i.choose k : ℚ) * gCoef y (k + 1))
      - y * (((i + 1).choose k : ℚ) * gCoef y k)
    = qCert y i k - qCert y i (k + 1) := by
  have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hi1 : ((i : ℚ) + 1) ≠ 0 := by positivity
  have hg : gCoef y (k + 1) = (y - (k : ℚ) * ((k : ℚ) + 1)) * gCoef y k / ((k : ℚ) + 1) ^ 2 := by
    have := gCoef_succ y k
    field_simp at this ⊢
    linarith [this]
  have hc1 : (i.choose k : ℚ) =
      ((i : ℚ) + 1 - (k : ℚ)) * ((i + 1).choose k : ℚ) / ((i : ℚ) + 1) := by
    have := cast_choose_pred i k
    field_simp
    linarith [this]
  have hc2 : ((i + 1).choose (k + 1) : ℚ) =
      (((i : ℚ) + 1) - (k : ℚ)) * ((i + 1).choose k : ℚ) / ((k : ℚ) + 1) := by
    have := cast_choose_succ (i + 1) k
    push_cast at this
    field_simp
    linarith [this]
  unfold qCert
  rw [hg, hc1, hc2]
  push_cast
  field_simp
  ring

/-- The recurrence satisfied by the closed-form sum. -/
lemma qSum_rec (y : ℚ) (i : ℕ) :
    ((i : ℚ) + 2) ^ 2 * qSum y (i + 2) =
      (2 * ((i : ℚ) + 1) * ((i : ℚ) + 2) + 1 + y) * qSum y (i + 1) - ((i : ℚ) + 1) ^ 2 * qSum y i := by
  set N := i + 2 with hN
  have htel : ∑ k ∈ range N,
      (((i : ℚ) + 2) ^ 2 * (((i + 1).choose k : ℚ) * gCoef y (k + 1))
        - ((i : ℚ) + 1) ^ 2 * ((i.choose k : ℚ) * gCoef y (k + 1))
        - y * (((i + 1).choose k : ℚ) * gCoef y k))
      = qCert y i 0 - qCert y i N := by
    rw [Finset.sum_congr rfl (fun k _ => qCert_step y i k)]
    exact sum_range_sub' (qCert y i) N
  have hcertN : qCert y i N = 0 := by
    have : (i + 1).choose N = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [qCert, this]
  rw [qCert_zero, hcertN] at htel
  -- unfold the three sums
  have hsplit : ∑ k ∈ range N,
      (((i : ℚ) + 2) ^ 2 * (((i + 1).choose k : ℚ) * gCoef y (k + 1))
        - ((i : ℚ) + 1) ^ 2 * ((i.choose k : ℚ) * gCoef y (k + 1))
        - y * (((i + 1).choose k : ℚ) * gCoef y k))
      = ((i : ℚ) + 2) ^ 2 * (∑ k ∈ range N, ((i + 1).choose k : ℚ) * gCoef y (k + 1))
        - ((i : ℚ) + 1) ^ 2 * (∑ k ∈ range N, (i.choose k : ℚ) * gCoef y (k + 1))
        - y * qPart y (i + 1) N := by
    unfold qPart
    simp [Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsplit] at htel
  have hA1 : ∑ k ∈ range N, ((i + 1).choose k : ℚ) * gCoef y (k + 1)
      = qPart y (i + 2) (N + 1) - qPart y (i + 1) (N + 1) := by
    have := qPart_succ y (i + 1) N
    linarith [this]
  have hA0 : ∑ k ∈ range N, (i.choose k : ℚ) * gCoef y (k + 1)
      = qPart y (i + 1) (N + 1) - qPart y i (N + 1) := by
    have := qPart_succ y i N
    linarith [this]
  rw [hA1, hA0] at htel
  rw [qPart_eq_qSum y (n := i + 2) (N := N + 1) (by omega),
    qPart_eq_qSum y (n := i + 1) (N := N + 1) (by omega),
    qPart_eq_qSum y (n := i) (N := N + 1) (by omega),
    qPart_eq_qSum y (n := i + 1) (N := N) (by omega)] at htel
  linarith [htel]

@[simp] lemma qSum_zero (y : ℚ) : qSum y 0 = 1 := by
  simp [qSum, qPart]

@[simp] lemma qSum_one (y : ℚ) : qSum y 1 = 1 + y := by
  simp [qSum, qPart, Finset.sum_range_succ, gCoef, betaCoef]

/-- The closed form for Beukers' Padé denominator. -/
theorem bq_eq_qSum (x : ℚ) (n : ℕ) : bq x n = qSum (x ^ 2 - x) n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp [add_comm]
    | (i + 2) =>
        have h1 := ih (i + 1) (by omega)
        have h0 := ih i (by omega)
        have hrec := bq_rec x i
        have hL : bL (i + 1) = ((i : ℚ) + 2) ^ 2 := by
          unfold bL; push_cast; ring
        have hC : bC x (i + 1) = 2 * ((i : ℚ) + 1) * ((i : ℚ) + 2) + 1 + (x ^ 2 - x) := by
          unfold bC; push_cast; ring
        have hR : bR (i + 1) = -(((i : ℚ) + 1) ^ 2) := by
          unfold bR; push_cast; ring
        rw [hL, hC, hR, h1, h0] at hrec
        have hq := qSum_rec (x ^ 2 - x) i
        have hpos : ((i : ℚ) + 2) ^ 2 ≠ 0 := by positivity
        refine mul_left_cancel₀ hpos ?_
        rw [hrec, hq]
        ring

end Catalan
