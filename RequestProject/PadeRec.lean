import RequestProject.Limits

/-!
# Beukers' Padé recurrence and the moving half-integer orbit

Sections 2--3 of the unconditional note: the two solutions `bq x`, `bp x` of Beukers' Padé
recurrence (3.1), the partial sums `sigmaCat m = ∑_{k<m} (-1)^k/(2k+1)²` of Catalan's series,
and the moving Padé point `xpt m = 1/2 - m`.
-/

namespace Catalan

open Filter Topology

/-! ### Beukers' Padé recurrence -/

/-- Leading coefficient of Beukers' Padé recurrence `(n+1)²`. -/
def bL (n : ℕ) : ℚ := ((n : ℚ) + 1) ^ 2

/-- Middle coefficient `2n(n+1) + 1 - x + x²`. -/
def bC (x : ℚ) (n : ℕ) : ℚ := 2 * (n : ℚ) * ((n : ℚ) + 1) + 1 - x + x ^ 2

/-- Trailing coefficient `-n²`. -/
def bR (n : ℕ) : ℚ := -((n : ℚ) ^ 2)

/-- Beukers' Padé denominator `q_n(x)`. -/
noncomputable def bq (x : ℚ) : ℕ → ℚ := rec2 bL (bC x) bR 1 (x ^ 2 - x + 1)

/-- Beukers' Padé numerator `p_n(x)`. -/
noncomputable def bp (x : ℚ) : ℕ → ℚ := rec2 bL (bC x) bR 0 1

@[simp] lemma bq_zero (x : ℚ) : bq x 0 = 1 := rfl
@[simp] lemma bq_one (x : ℚ) : bq x 1 = x ^ 2 - x + 1 := rfl
@[simp] lemma bp_zero (x : ℚ) : bp x 0 = 0 := rfl
@[simp] lemma bp_one (x : ℚ) : bp x 1 = 1 := rfl

lemma bL_ne_zero (n : ℕ) : bL n ≠ 0 := by
  unfold bL
  have : ((n : ℚ) + 1) ≠ 0 := by positivity
  exact pow_ne_zero _ this

lemma bq_rec (x : ℚ) (n : ℕ) :
    bL (n + 1) * bq x (n + 2) = bC x (n + 1) * bq x (n + 1) + bR (n + 1) * bq x n :=
  rec2_rec bL (bC x) bR 1 (x ^ 2 - x + 1) n (bL_ne_zero (n + 1))

lemma bp_rec (x : ℚ) (n : ℕ) :
    bL (n + 1) * bp x (n + 2) = bC x (n + 1) * bp x (n + 1) + bR (n + 1) * bp x n :=
  rec2_rec bL (bC x) bR 0 1 n (bL_ne_zero (n + 1))

/-! ### The moving half-integer orbit -/

/-- The partial sums `σ_m = ∑_{k<m} (-1)^k/(2k+1)²` of Catalan's series. -/
def sigmaCat (m : ℕ) : ℚ := ∑ k ∈ Finset.range m, (-1 : ℚ) ^ k / (2 * (k : ℚ) + 1) ^ 2

@[simp] lemma sigmaCat_zero : sigmaCat 0 = 0 := by simp [sigmaCat]

lemma sigmaCat_succ (m : ℕ) :
    sigmaCat (m + 1) = sigmaCat m + (-1 : ℚ) ^ m / (2 * (m : ℚ) + 1) ^ 2 := by
  simp [sigmaCat, Finset.sum_range_succ]

/-- The moving Padé point `x_m = 1/2 - m`. -/
def xpt (m : ℕ) : ℚ := 1 / 2 - (m : ℚ)

@[simp] lemma xpt_zero : xpt 0 = 1 / 2 := by simp [xpt]

lemma xpt_succ_add_one (m : ℕ) : xpt (m + 1) + 1 = xpt m := by
  unfold xpt; push_cast; ring

lemma xpt_eq_odd_div_two (m : ℕ) : xpt m = ((1 - 2 * (m : ℤ) : ℤ) : ℚ) / 2 := by
  unfold xpt; push_cast; ring

end Catalan
