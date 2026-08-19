import RequestProject.ClosedForm
import RequestProject.XiSeries

/-!
# A closed form for Beukers' Padé numerators

`ClosedForm.lean` proves the closed form

`q_n(x) = ∑_{k=0}^{n} (n choose k) β_k(y) / (k!)²`,   `y = x² - x`,  `β_k(y) = ∏_{j<k}(y - j(j+1))`

for the Padé *denominator*.  Here we prove the companion closed form for the *numerator*
`p_n(x)` (the second solution of the same recurrence, with `p_0 = 0`, `p_1 = 1`):

`p_n(x) = -∑_{k=0}^{n} (n choose k) (β_k(y)/(k!)²) h_k(x)`,   `h_k(x) = ∑_{j<k} [j/x][j/(1-x)]`,

where `[j/x]` is Beukers' bracket of `XiSeries.lean`, so that `h_k` is the `k`-th partial sum of
the series defining `Ξ`.  This is the exact analogue of the closed form for the modular
`E`-family numerator proved in `EClosedForm.lean`.

The verification is again a telescoping (Zeilberger-style) computation.  Writing
`w_k = (β_k(y)/(k!)²) h_k` for the weight, the certificate is
`pCert i k = -k(k+1) (i+1 choose k) w_k`, and the termwise identity carries one extra term,

`… = pCert i k - pCert i (k+1) + (-1)^{k+1} (i+1 choose k)`,

coming from `h_{k+1} - h_k = [k/x][k/(1-x)]` together with the evaluation
`(β_k(y)/(k!)²)(y - k(k+1))·[k/x][k/(1-x)] = (-1)^{k+1}`.  Summing over `k` the extra terms add
up to the vanishing alternating binomial sum, so the closed form satisfies the *same*
homogeneous recurrence as `q_n`, and the initial values `0`, `1` identify it with `p_n`.
-/

namespace Catalan

open Finset

/-! ### The partial sums of Beukers' series -/

/-- `h_k(x) = ∑_{j<k} [j/x][j/(1-x)]`, the `k`-th partial sum of the series (2.2). -/
def xiPart (x : ℚ) (k : ℕ) : ℚ := ∑ j ∈ range k, xiTerm x j

@[simp] lemma xiPart_zero (x : ℚ) : xiPart x 0 = 0 := by simp [xiPart]

lemma xiPart_succ (x : ℚ) (k : ℕ) : xiPart x (k + 1) = xiPart x k + xiTerm x k :=
  sum_range_succ _ _

/-- `β_{k+1}(y) = (-1)^{k+1} · (x(x+1)⋯(x+k)) · ((1-x)(2-x)⋯(1-x+k))` for `y = x² - x`. -/
lemma betaCoef_succ_eq (x : ℚ) (k : ℕ) :
    betaCoef (x ^ 2 - x) (k + 1) = (-1 : ℚ) ^ (k + 1) * (brkDen x k * brkDen (1 - x) k) := by
  unfold betaCoef brkDen
  rw [← Finset.prod_mul_distrib,
    show ((-1 : ℚ) ^ (k + 1)) = ∏ _j ∈ range (k + 1), (-1 : ℚ) by simp,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl ?_
  intro j _
  ring

/-- The evaluation behind the extra term of the certificate:
`(β_k(y)/(k!)²)·(y - k(k+1))·[k/x][k/(1-x)] = (-1)^{k+1}`. -/
lemma gCoef_mul_xiTerm {x : ℚ} (hx : HalfOdd x) (k : ℕ) :
    gCoef (x ^ 2 - x) k * ((x ^ 2 - x) - (k : ℚ) * ((k : ℚ) + 1)) * xiTerm x k
      = (-1 : ℚ) ^ (k + 1) := by
  have hfac : ((k.factorial : ℚ)) ≠ 0 := factorial_ne_zero_rat k
  have hd1 : brkDen x k ≠ 0 := brkDen_ne_zero hx k
  have hd2 : brkDen (1 - x) k ≠ 0 := brkDen_ne_zero hx.one_sub k
  have hbeta : betaCoef (x ^ 2 - x) k * ((x ^ 2 - x) - (k : ℚ) * ((k : ℚ) + 1))
      = (-1 : ℚ) ^ (k + 1) * (brkDen x k * brkDen (1 - x) k) := by
    rw [← betaCoef_succ_eq x k, betaCoef_succ]
  have h1 : gCoef (x ^ 2 - x) k * ((x ^ 2 - x) - (k : ℚ) * ((k : ℚ) + 1))
      = (-1 : ℚ) ^ (k + 1) * (brkDen x k * brkDen (1 - x) k) / (k.factorial : ℚ) ^ 2 := by
    unfold gCoef
    rw [div_mul_eq_mul_div, hbeta]
  rw [h1]
  unfold xiTerm brk
  field_simp

/-! ### The closed-form sum -/

/-- The weight `w_k = (β_k(y)/(k!)²)·h_k(x)` of the numerator closed form. -/
def pWeight (x : ℚ) (k : ℕ) : ℚ := gCoef (x ^ 2 - x) k * xiPart x k

@[simp] lemma pWeight_zero (x : ℚ) : pWeight x 0 = 0 := by simp [pWeight]

/-- The closed-form sum, truncated at `N`. -/
def pPart (x : ℚ) (n N : ℕ) : ℚ := ∑ k ∈ range N, (n.choose k : ℚ) * pWeight x k

/-- The closed form `-∑_{k≤n} (n choose k) (β_k(y)/(k!)²) h_k`. -/
def pSum (x : ℚ) (n : ℕ) : ℚ := -pPart x n (n + 1)

lemma pPart_eq_pSum (x : ℚ) {n N : ℕ} (h : n + 1 ≤ N) : pPart x n N = -pSum x n := by
  unfold pPart pSum pPart
  rw [neg_neg]
  refine (Finset.sum_subset (by simpa using h) ?_).symm
  intro k _ hk
  have : n.choose k = 0 := Nat.choose_eq_zero_of_lt (by simpa using hk)
  simp [this]

/-- The Pascal step. -/
lemma pPart_succ (x : ℚ) (n N : ℕ) :
    pPart x (n + 1) (N + 1) =
      pPart x n (N + 1) + ∑ k ∈ range N, (n.choose k : ℚ) * pWeight x (k + 1) := by
  unfold pPart
  rw [sum_range_succ' (fun k => ((n + 1).choose k : ℚ) * pWeight x k) N,
    sum_range_succ' (fun k => (n.choose k : ℚ) * pWeight x k) N]
  have : ∀ k ∈ range N, ((n + 1).choose (k + 1) : ℚ) * pWeight x (k + 1) =
      (n.choose (k + 1) : ℚ) * pWeight x (k + 1) + (n.choose k : ℚ) * pWeight x (k + 1) := by
    intro k _
    rw [Nat.choose_succ_succ n k]
    push_cast
    ring
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
  simp

/-- The telescoping certificate. -/
def pCert (x : ℚ) (i k : ℕ) : ℚ :=
  -((k : ℚ) * ((k : ℚ) + 1)) * ((i + 1).choose k : ℚ) * pWeight x k

lemma pCert_zero (x : ℚ) (i : ℕ) : pCert x i 0 = 0 := by simp [pCert]

lemma pCert_eq (x : ℚ) (i k : ℕ) : pCert x i k = qCert (x ^ 2 - x) i k * xiPart x k := by
  unfold pCert qCert pWeight
  ring

/-- The termwise telescoping identity behind the recurrence, with its inhomogeneous term. -/
lemma pCert_step {x : ℚ} (hx : HalfOdd x) (i k : ℕ) :
    ((i : ℚ) + 2) ^ 2 * (((i + 1).choose k : ℚ) * pWeight x (k + 1))
      - ((i : ℚ) + 1) ^ 2 * ((i.choose k : ℚ) * pWeight x (k + 1))
      - (x ^ 2 - x) * (((i + 1).choose k : ℚ) * pWeight x k)
    = pCert x i k - pCert x i (k + 1)
        + (-1 : ℚ) ^ (k + 1) * ((i + 1).choose k : ℚ) := by
  have hq := qCert_step (x ^ 2 - x) i k
  have hu := gCoef_mul_xiTerm hx k
  rw [pCert_eq, pCert_eq]
  simp only [pWeight, xiPart_succ]
  simp only [qCert] at hq ⊢
  linear_combination (xiPart x k + xiTerm x k) * hq + ((i + 1).choose k : ℚ) * hu

/-- The recurrence satisfied by the closed-form sum: the same one as for `q_n`. -/
lemma pSum_rec {x : ℚ} (hx : HalfOdd x) (i : ℕ) :
    ((i : ℚ) + 2) ^ 2 * pSum x (i + 2) =
      (2 * ((i : ℚ) + 1) * ((i : ℚ) + 2) + 1 + (x ^ 2 - x)) * pSum x (i + 1)
        - ((i : ℚ) + 1) ^ 2 * pSum x i := by
  set y := x ^ 2 - x with hy
  set N := i + 2 with hN
  have htel : ∑ k ∈ range N,
      (((i : ℚ) + 2) ^ 2 * (((i + 1).choose k : ℚ) * pWeight x (k + 1))
        - ((i : ℚ) + 1) ^ 2 * ((i.choose k : ℚ) * pWeight x (k + 1))
        - y * (((i + 1).choose k : ℚ) * pWeight x k))
      = (pCert x i 0 - pCert x i N)
        + ∑ k ∈ range N, (-1 : ℚ) ^ (k + 1) * ((i + 1).choose k : ℚ) := by
    rw [Finset.sum_congr rfl (fun k _ => pCert_step hx i k), Finset.sum_add_distrib,
      sum_range_sub' (pCert x i) N]
  have hcertN : pCert x i N = 0 := by
    have : (i + 1).choose N = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [pCert, this]
  have halt : ∑ k ∈ range N, (-1 : ℚ) ^ (k + 1) * ((i + 1).choose k : ℚ) = 0 := by
    have hz : (∑ k ∈ range (i + 1 + 1), ((-1) ^ k * ((i + 1).choose k) : ℤ)) = 0 :=
      Int.alternating_sum_range_choose_of_ne (by omega)
    have hcast := congrArg (fun z : ℤ => (z : ℚ)) hz
    push_cast at hcast
    have : ∑ k ∈ range N, (-1 : ℚ) ^ (k + 1) * ((i + 1).choose k : ℚ)
        = -∑ k ∈ range (i + 1 + 1), ((-1 : ℚ) ^ k * ((i + 1).choose k : ℚ)) := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr (by rw [hN]) ?_
      intro k _
      ring
    rw [this, hcast]
    ring
  rw [pCert_zero, hcertN, halt] at htel
  have hsplit : ∑ k ∈ range N,
      (((i : ℚ) + 2) ^ 2 * (((i + 1).choose k : ℚ) * pWeight x (k + 1))
        - ((i : ℚ) + 1) ^ 2 * ((i.choose k : ℚ) * pWeight x (k + 1))
        - y * (((i + 1).choose k : ℚ) * pWeight x k))
      = ((i : ℚ) + 2) ^ 2 * (∑ k ∈ range N, ((i + 1).choose k : ℚ) * pWeight x (k + 1))
        - ((i : ℚ) + 1) ^ 2 * (∑ k ∈ range N, (i.choose k : ℚ) * pWeight x (k + 1))
        - y * pPart x (i + 1) N := by
    unfold pPart
    simp [Finset.mul_sum, Finset.sum_sub_distrib]
  rw [hsplit] at htel
  have hA1 : ∑ k ∈ range N, ((i + 1).choose k : ℚ) * pWeight x (k + 1)
      = pPart x (i + 2) (N + 1) - pPart x (i + 1) (N + 1) := by
    have := pPart_succ x (i + 1) N
    linarith [this]
  have hA0 : ∑ k ∈ range N, (i.choose k : ℚ) * pWeight x (k + 1)
      = pPart x (i + 1) (N + 1) - pPart x i (N + 1) := by
    have := pPart_succ x i N
    linarith [this]
  rw [hA1, hA0] at htel
  rw [pPart_eq_pSum x (n := i + 2) (N := N + 1) (by omega),
    pPart_eq_pSum x (n := i + 1) (N := N + 1) (by omega),
    pPart_eq_pSum x (n := i) (N := N + 1) (by omega),
    pPart_eq_pSum x (n := i + 1) (N := N) (by omega)] at htel
  linarith [htel]

@[simp] lemma pSum_zero (x : ℚ) : pSum x 0 = 0 := by
  simp [pSum, pPart]

lemma gCoef_one (y : ℚ) : gCoef y 1 = y := by
  simp [gCoef, betaCoef]

@[simp] lemma pSum_one {x : ℚ} (hx : HalfOdd x) : pSum x 1 = 1 := by
  have hu := gCoef_mul_xiTerm hx 0
  simp only [gCoef_zero, Nat.cast_zero, one_mul, mul_one, sub_zero, zero_add, pow_one] at hu
  have h1 : pSum x 1 = -(gCoef (x ^ 2 - x) 1 * xiTerm x 0) := by
    simp [pSum, pPart, Finset.sum_range_succ, pWeight, xiPart_succ]
  rw [h1, gCoef_one]
  linarith [hu]

/-- The closed form for Beukers' Padé numerator. -/
theorem bp_eq_pSum {x : ℚ} (hx : HalfOdd x) (n : ℕ) : bp x n = pSum x n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp [pSum_one hx]
    | (i + 2) =>
        have h1 := ih (i + 1) (by omega)
        have h0 := ih i (by omega)
        have hrec := bp_rec x i
        have hL : bL (i + 1) = ((i : ℚ) + 2) ^ 2 := by
          unfold bL; push_cast; ring
        have hC : bC x (i + 1) = 2 * ((i : ℚ) + 1) * ((i : ℚ) + 2) + 1 + (x ^ 2 - x) := by
          unfold bC; push_cast; ring
        have hR : bR (i + 1) = -(((i : ℚ) + 1) ^ 2) := by
          unfold bR; push_cast; ring
        rw [hL, hC, hR, h1, h0] at hrec
        have hp := pSum_rec hx i
        have hpos : ((i : ℚ) + 2) ^ 2 ≠ 0 := by positivity
        refine mul_left_cancel₀ hpos ?_
        rw [hrec, hp]
        ring

end Catalan
