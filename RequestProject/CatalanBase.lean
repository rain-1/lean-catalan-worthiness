import RequestProject.ZudilinLimit
import RequestProject.EClosedForm

/-!
# The accelerated series for Catalan's constant

The weights `c_k = (1/4) ∑_{j<k} 4^j / (C(2j,j) (2j+1)^2)` of the closed form of the modular
numerator `B_n` (`EClosedForm.lean`) converge to `G/2`, where `G = ∑ (-1)^k/(2k+1)^2` is
Catalan's constant (`Catalan.catalanReal`).  Equivalently

`∑_{j ≥ 0} 4^j / (C(2j,j) (2j+1)^2) = 2 G`.

This is the classical "central binomial" acceleration of Catalan's constant.  This file sets up
the elementary part:

* the lower bound `16^k ≤ C(2k,k)^2 (4k+1)`, proved by induction from the recurrence
  `(k+1) C(2k+2,k+1) = 2(2k+1) C(2k,k)`;
* the auxiliary sequence `uR j = 4^j/((2j+1) C(2j,j))`, which satisfies
  `uR (j+1) = 2(j+1)/(2j+3) · uR j`, whence `wR j ≤ 3 (uR j - uR (j+1))` and the series `∑ wR`
  converges (with sum at most `3`).

The evaluation `∑ wR = 2G` is proved in `CatalanIntegral.lean`.
-/

namespace Catalan

open Filter Topology Finset

/-- `wR j = 4^j / (C(2j,j) (2j+1)^2)`, the `j`-th term of the accelerated series. -/
noncomputable def wR (j : ℕ) : ℝ :=
  (4 : ℝ) ^ j / ((Nat.centralBinom j : ℝ) * (2 * j + 1) ^ 2)

/-- `uR j = 4^j / ((2j+1) C(2j,j)) = ∫_0^1 (1-y²)^j dy`. -/
noncomputable def uR (j : ℕ) : ℝ :=
  (4 : ℝ) ^ j / ((2 * j + 1) * (Nat.centralBinom j : ℝ))

lemma centralBinom_cast_pos (j : ℕ) : (0 : ℝ) < (Nat.centralBinom j : ℝ) := by
  exact_mod_cast Nat.centralBinom_pos j

lemma wR_nonneg (j : ℕ) : 0 ≤ wR j := by
  have := centralBinom_cast_pos j
  unfold wR
  positivity

lemma uR_pos (j : ℕ) : 0 < uR j := by
  have := centralBinom_cast_pos j
  unfold uR
  positivity

lemma centralBinom_rec (k : ℕ) :
    ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ) = 2 * (2 * k + 1) * (Nat.centralBinom k : ℝ) := by
  have := Nat.succ_mul_centralBinom_succ k
  have : ((k + 1) * Nat.centralBinom (k + 1) : ℕ) = ((2 * (2 * k + 1) * Nat.centralBinom k : ℕ)) :=
    this
  exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) this

/-- The elementary lower bound `16^k ≤ C(2k,k)^2 (4k+1)`, i.e. `4^k/C(2k,k) ≤ √(4k+1)`. -/
theorem sixteen_pow_le_centralBinom_sq (k : ℕ) :
    (16 : ℝ) ^ k ≤ (Nat.centralBinom k : ℝ) ^ 2 * (4 * k + 1) := by
  induction k with
  | zero => norm_num [Nat.centralBinom]
  | succ k ih =>
      set c : ℝ := (Nat.centralBinom k : ℝ) with hc
      set c' : ℝ := (Nat.centralBinom (k + 1) : ℝ) with hc'
      have hcpos : 0 < c := centralBinom_cast_pos k
      have hc'pos : 0 < c' := centralBinom_cast_pos (k + 1)
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have hrec : ((k : ℝ) + 1) * c' = 2 * (2 * k + 1) * c := centralBinom_rec k
      have hsq : ((k : ℝ) + 1) ^ 2 * c' ^ 2 = 4 * (2 * k + 1) ^ 2 * c ^ 2 :=
        calc ((k : ℝ) + 1) ^ 2 * c' ^ 2 = (((k : ℝ) + 1) * c') ^ 2 := by ring
          _ = (2 * (2 * (k : ℝ) + 1) * c) ^ 2 := by rw [hrec]
          _ = 4 * (2 * (k : ℝ) + 1) ^ 2 * c ^ 2 := by ring
      have h16 : (0 : ℝ) < (16 : ℝ) ^ k := by positivity
      have hkey : 16 * ((k : ℝ) + 1) ^ 2 * (4 * k + 1) ≤ 4 * (2 * k + 1) ^ 2 * (4 * k + 5) := by
        nlinarith
      -- `4(2k+1)²(4k+5) c² ≥ (k+1)² 16^{k+1}`
      have h1 : 4 * (2 * (k : ℝ) + 1) ^ 2 * (4 * k + 5) * (16 : ℝ) ^ k
          ≤ 4 * (2 * (k : ℝ) + 1) ^ 2 * (4 * k + 5) * (c ^ 2 * (4 * k + 1)) := by
        have hpos : (0 : ℝ) ≤ 4 * (2 * (k : ℝ) + 1) ^ 2 * (4 * k + 5) := by positivity
        exact mul_le_mul_of_nonneg_left ih hpos
      have h2 : 16 * ((k : ℝ) + 1) ^ 2 * (4 * k + 1) * (16 : ℝ) ^ k
          ≤ 4 * (2 * (k : ℝ) + 1) ^ 2 * (4 * k + 5) * (16 : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right hkey h16.le
      have h41 : (0 : ℝ) < 4 * (k : ℝ) + 1 := by positivity
      have h3 : 16 * ((k : ℝ) + 1) ^ 2 * (16 : ℝ) ^ k * (4 * k + 1)
          ≤ 4 * (2 * (k : ℝ) + 1) ^ 2 * c ^ 2 * (4 * k + 5) * (4 * k + 1) := by nlinarith
      have h4 : 16 * ((k : ℝ) + 1) ^ 2 * (16 : ℝ) ^ k
          ≤ 4 * (2 * (k : ℝ) + 1) ^ 2 * c ^ 2 * (4 * k + 5) :=
        le_of_mul_le_mul_right (by linarith [h3]) h41
      have hk1 : (0 : ℝ) < ((k : ℝ) + 1) ^ 2 := by positivity
      have hval : ((k : ℝ) + 1) ^ 2 * (c' ^ 2 * (4 * ((k : ℝ) + 1) + 1))
          = 4 * (2 * (k : ℝ) + 1) ^ 2 * c ^ 2 * (4 * k + 5) := by
        rw [show ((k : ℝ) + 1) ^ 2 * (c' ^ 2 * (4 * ((k : ℝ) + 1) + 1))
          = (((k : ℝ) + 1) ^ 2 * c' ^ 2) * (4 * (k : ℝ) + 5) by ring, hsq]
      have h5 : ((k : ℝ) + 1) ^ 2 * ((16 : ℝ) ^ (k + 1))
          ≤ ((k : ℝ) + 1) ^ 2 * (c' ^ 2 * (4 * ((k : ℝ) + 1) + 1)) := by
        rw [hval]
        calc ((k : ℝ) + 1) ^ 2 * ((16 : ℝ) ^ (k + 1)) = 16 * ((k : ℝ) + 1) ^ 2 * (16 : ℝ) ^ k := by
              rw [pow_succ]; ring
          _ ≤ 4 * (2 * (k : ℝ) + 1) ^ 2 * c ^ 2 * (4 * k + 5) := h4
      have hfin := le_of_mul_le_mul_left h5 hk1
      push_cast
      linarith [hfin]

lemma wR_eq_uR_div (j : ℕ) : wR j = uR j / (2 * j + 1) := by
  have hc := (centralBinom_cast_pos j).ne'
  have h2 : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
  unfold wR uR
  field_simp

lemma uR_succ (j : ℕ) : uR (j + 1) = uR j * (2 * ((j : ℝ) + 1)) / (2 * j + 3) := by
  have hc := (centralBinom_cast_pos j).ne'
  have hc' := (centralBinom_cast_pos (j + 1)).ne'
  have hrec : ((j : ℝ) + 1) * (Nat.centralBinom (j + 1) : ℝ)
      = 2 * (2 * j + 1) * (Nat.centralBinom j : ℝ) := centralBinom_rec j
  have h1 : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
  have h3 : (2 * (j : ℝ) + 3) ≠ 0 := by positivity
  have hj1 : ((j : ℝ) + 1) ≠ 0 := by positivity
  unfold uR
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity)]
  have hcc : (Nat.centralBinom (j + 1) : ℝ) = 2 * (2 * j + 1) * (Nat.centralBinom j : ℝ) / ((j : ℝ) + 1) := by
    field_simp at hrec ⊢
    linarith [hrec]
  rw [hcc]
  field_simp
  ring

lemma wR_le_telescope (j : ℕ) : wR j ≤ 3 * (uR j - uR (j + 1)) := by
  have hu := (uR_pos j).le
  have h1 : (0 : ℝ) < 2 * (j : ℝ) + 1 := by positivity
  have h3 : (0 : ℝ) < 2 * (j : ℝ) + 3 := by positivity
  have hdiff : 3 * (uR j - uR (j + 1)) = 3 * uR j / (2 * j + 3) := by
    rw [uR_succ]
    field_simp
    ring
  rw [wR_eq_uR_div, hdiff, div_le_div_iff₀ h1 h3]
  nlinarith

lemma sum_wR_le (n : ℕ) : ∑ j ∈ range n, wR j ≤ 3 := by
  have htel : ∑ j ∈ range n, 3 * (uR j - uR (j + 1)) = 3 * (uR 0 - uR n) := by
    rw [← Finset.mul_sum, Finset.sum_range_sub' (f := uR)]
  have h1 : ∑ j ∈ range n, wR j ≤ ∑ j ∈ range n, 3 * (uR j - uR (j + 1)) :=
    Finset.sum_le_sum (fun j _ => wR_le_telescope j)
  have hu0 : uR 0 = 1 := by norm_num [uR, Nat.centralBinom]
  have hun : 0 < uR n := uR_pos n
  rw [htel, hu0] at h1
  linarith

theorem summable_wR : Summable wR :=
  summable_of_sum_range_le (fun j => wR_nonneg j) sum_wR_le


end Catalan
