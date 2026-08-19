import RequestProject.PadeRec

/-!
# Contiguity relations for Beukers' Padé pair

Beukers' recurrence (3.1) has the two solutions `q_n(x)` (`bq`) and `p_n(x)` (`bp`).
Because the Padé function `Ξ` satisfies the functional equation `Ξ(x-1) + Ξ(x) = 2/(x-1)²`
(Lemma 2.1), the pair at the *shifted* point `x - 1` is a fixed linear combination of the pair
at `x`.  Concretely, with

`c_n(x) = x² - 2(n+1)x + 2n² + 2n + 1`,

we prove the two polynomial identities

* `bq_contig` : `(x-1)² q_n(x-1) = c_n(x) q_n(x) - 2n² q_{n-1}(x)`,
* `bp_contig` : `2 q_n(x-1) - (x-1)² p_n(x-1) = c_n(x) p_n(x) - 2n² p_{n-1}(x)`,

for `n ≥ 1`.  Both are proved by a two-step induction on `n`: the induction step is pure algebra,
using Beukers' recurrence at `x` and at `x - 1`.

These relations are the engine of `RivoalP.lean`, where they are used along the moving orbit
`x_m = 1/2 - m` (so that `x_m - 1 = x_{m+1}`) to prove Rivoal's identity (4.9).
-/

namespace Catalan

/-- The contiguity coefficient `c_n(x) = x² - 2(n+1)x + 2n² + 2n + 1`. -/
def cCon (n : ℕ) (x : ℚ) : ℚ :=
  x ^ 2 - 2 * ((n : ℚ) + 1) * x + 2 * (n : ℚ) ^ 2 + 2 * (n : ℚ) + 1

/-- The contiguity relation for Beukers' Padé denominator:
`(x-1)² q_{n+1}(x-1) = c_{n+1}(x) q_{n+1}(x) - 2(n+1)² q_n(x)`. -/
theorem bq_contig (x : ℚ) (n : ℕ) :
    (x - 1) ^ 2 * bq (x - 1) (n + 1)
      = cCon (n + 1) x * bq x (n + 1) - 2 * ((n : ℚ) + 1) ^ 2 * bq x n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
        have e1 : bq (x - 1) (0 + 1) = (x - 1) ^ 2 - (x - 1) + 1 := bq_one _
        have e2 : bq x (0 + 1) = x ^ 2 - x + 1 := bq_one _
        rw [e1, e2, bq_zero]
        simp only [cCon]
        push_cast
        ring
    | 1 =>
        have h1 := bq_rec x 0
        have h2 := bq_rec (x - 1) 0
        have e1 : bq (x - 1) (0 + 1) = (x - 1) ^ 2 - (x - 1) + 1 := bq_one _
        have e2 : bq x (0 + 1) = x ^ 2 - x + 1 := bq_one _
        have e3 : bq x 1 = x ^ 2 - x + 1 := bq_one _
        rw [e2, bq_zero] at h1
        rw [e1, bq_zero] at h2
        rw [e3]
        simp only [bL, bC, bR] at h1 h2
        simp only [cCon]
        push_cast at h1 h2 ⊢
        linear_combination ((x - 1) ^ 2 / 4) * h2 - ((x ^ 2 - 6 * x + 13) / 4) * h1
    | (i + 2) =>
        have h1 := ih (i + 1) (by omega)
        have h0 := ih i (by omega)
        have r1 := bq_rec (x - 1) (i + 1)
        have r2 := bq_rec x (i + 1)
        have r3 := bq_rec x i
        simp only [bL, bC, bR, cCon] at h1 h0 r1 r2 r3 ⊢
        push_cast at h1 h0 r1 r2 r3 ⊢
        have hL : (((i : ℚ) + 3) ^ 2) ≠ 0 := by positivity
        refine mul_left_cancel₀ hL ?_
        linear_combination ((x - 1) ^ 2) * r1
          + (2 * ((i : ℚ) + 2) * ((i : ℚ) + 3) + 1 - (x - 1) + (x - 1) ^ 2) * h1
          + (-(((i : ℚ) + 2) ^ 2)) * h0
          - (x ^ 2 - 2 * ((i : ℚ) + 4) * x + 2 * ((i : ℚ) + 3) ^ 2 + 2 * ((i : ℚ) + 3) + 1) * r2
          + (2 * ((i : ℚ) + 2) ^ 2) * r3

/-- The contiguity relation for Beukers' Padé numerator:
`2 q_{n+1}(x-1) - (x-1)² p_{n+1}(x-1) = c_{n+1}(x) p_{n+1}(x) - 2(n+1)² p_n(x)`. -/
theorem bp_contig (x : ℚ) (n : ℕ) :
    2 * bq (x - 1) (n + 1) - (x - 1) ^ 2 * bp (x - 1) (n + 1)
      = cCon (n + 1) x * bp x (n + 1) - 2 * ((n : ℚ) + 1) ^ 2 * bp x n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 =>
        have e1 : bq (x - 1) (0 + 1) = (x - 1) ^ 2 - (x - 1) + 1 := bq_one _
        have e2 : bp (x - 1) (0 + 1) = 1 := bp_one _
        have e3 : bp x (0 + 1) = 1 := bp_one _
        rw [e1, e2, e3, bp_zero]
        simp only [cCon]
        push_cast
        ring
    | 1 =>
        have h1 := bq_rec (x - 1) 0
        have h2 := bp_rec (x - 1) 0
        have h3 := bp_rec x 0
        have e1 : bq (x - 1) (0 + 1) = (x - 1) ^ 2 - (x - 1) + 1 := bq_one _
        have e2 : bp (x - 1) (0 + 1) = 1 := bp_one _
        have e3 : bp x (0 + 1) = 1 := bp_one _
        have e4 : bp x 1 = 1 := bp_one _
        rw [e1, bq_zero] at h1
        rw [e2, bp_zero] at h2
        rw [e3, bp_zero] at h3
        rw [e4]
        simp only [bL, bC, bR] at h1 h2 h3
        simp only [cCon]
        push_cast at h1 h2 h3 ⊢
        linear_combination (2 / 4 : ℚ) * h1 - ((x - 1) ^ 2 / 4) * h2
          - ((x ^ 2 - 6 * x + 13) / 4) * h3
    | (i + 2) =>
        have h1 := ih (i + 1) (by omega)
        have h0 := ih i (by omega)
        have r0 := bq_rec (x - 1) (i + 1)
        have r1 := bp_rec (x - 1) (i + 1)
        have r2 := bp_rec x (i + 1)
        have r3 := bp_rec x i
        simp only [bL, bC, bR, cCon] at h1 h0 r0 r1 r2 r3 ⊢
        push_cast at h1 h0 r0 r1 r2 r3 ⊢
        have hL : (((i : ℚ) + 3) ^ 2) ≠ 0 := by positivity
        refine mul_left_cancel₀ hL ?_
        linear_combination (2 : ℚ) * r0 - ((x - 1) ^ 2) * r1
          + (2 * ((i : ℚ) + 2) * ((i : ℚ) + 3) + 1 - (x - 1) + (x - 1) ^ 2) * h1
          + (-(((i : ℚ) + 2) ^ 2)) * h0
          - (x ^ 2 - 2 * ((i : ℚ) + 4) * x + 2 * ((i : ℚ) + 3) ^ 2 + 2 * ((i : ℚ) + 3) + 1) * r2
          + (2 * ((i : ℚ) + 2) ^ 2) * r3

end Catalan
