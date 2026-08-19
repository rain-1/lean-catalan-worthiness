import RequestProject.Rec2
import RequestProject.Padic2

/-!
# Beukers' `2`-adic Padé function `Ξ` and its functional equation

Section 2 of the unconditional note.  Beukers' bracket is

`[k/x] = k! / (x (x+1) ⋯ (x+k))`,

and the sign-safe normalization (2.2) of the note is

`Ξ(x) = - ∑_{k ≥ 0} [k/x] [k/(1-x)]`.

For a *half-odd* rational `x = a/2` (`a` odd) every factor `x + j` has `2`-adic valuation `-1`,
so `|[k/x]|₂ ≤ 2^{-(k+1)}` and the series converges in `ℚ₂`.  Here `Ξ` is *defined* by this
series (`XiPade`), and Lemma 2.1,

`Ξ(x+1) + Ξ(x) = 2/x²`,

is *proved* (`XiPade_funeq`) by the telescoping

`u_k(x) + u_k(x+1) = g_k(x) - g_{k+1}(x)`,
`u_k(x) = [k/x][k/(1-x)]`,  `g_k(x) = -2 (k+1-x) u_k(x) / x`,  `g_0(x) = -2/x²`.
-/

namespace Catalan

open Filter Topology Finset

/-! ### Half-odd rationals -/

/-- `x` is a half-odd rational: `x = a/2` with `a` an odd integer. -/
def HalfOdd (x : ℚ) : Prop := ∃ a : ℤ, Odd a ∧ x = (a : ℚ) / 2

lemma HalfOdd.ne_zero {x : ℚ} (hx : HalfOdd x) : x ≠ 0 := by
  obtain ⟨a, ha, rfl⟩ := hx
  have : a ≠ 0 := by rintro rfl; simp at ha
  simpa using this

lemma HalfOdd.add_intCast {x : ℚ} (hx : HalfOdd x) (n : ℤ) : HalfOdd (x + (n : ℚ)) := by
  obtain ⟨a, ha, rfl⟩ := hx
  refine ⟨a + 2 * n, ?_, by push_cast; ring⟩
  rcases ha with ⟨b, hb⟩
  exact ⟨b + n, by omega⟩

lemma HalfOdd.add_natCast {x : ℚ} (hx : HalfOdd x) (n : ℕ) : HalfOdd (x + (n : ℚ)) := by
  simpa using hx.add_intCast (n : ℤ)

lemma HalfOdd.neg {x : ℚ} (hx : HalfOdd x) : HalfOdd (-x) := by
  obtain ⟨a, ha, rfl⟩ := hx
  exact ⟨-a, ha.neg, by push_cast; ring⟩

lemma HalfOdd.one_sub {x : ℚ} (hx : HalfOdd x) : HalfOdd (1 - x) := by
  have := (hx.neg).add_intCast 1
  simpa [sub_eq_neg_add, add_comm] using this

lemma HalfOdd.padicValRat_eq {x : ℚ} (hx : HalfOdd x) : padicValRat 2 x = -1 := by
  obtain ⟨a, ha, rfl⟩ := hx
  have ha0 : (a : ℚ) ≠ 0 := by
    have : a ≠ 0 := by rintro rfl; simp at ha
    exact_mod_cast this
  have h2 : padicValRat 2 (2 : ℚ) = 1 := by simpa using padicValRat_two_two_pow 1
  rw [padicValRat.div ha0 (by norm_num), padicValRat_two_of_odd_int ha, h2]
  norm_num

/-- Half-odd rationals have `2`-adic absolute value `2`. -/
lemma HalfOdd.norm_cast {x : ℚ} (hx : HalfOdd x) : ‖((x : ℚ) : ℚ_[2])‖ = 2 := by
  rw [norm_ratCast_padic2 hx.ne_zero, hx.padicValRat_eq]
  norm_num

/-! ### Beukers' bracket -/

/-- The denominator `x (x+1) ⋯ (x+k)` of Beukers' bracket. -/
def brkDen (x : ℚ) (k : ℕ) : ℚ := ∏ j ∈ range (k + 1), (x + (j : ℚ))

/-- Beukers' bracket `[k/x] = k!/(x (x+1) ⋯ (x+k))`, equation (2.1). -/
def brk (x : ℚ) (k : ℕ) : ℚ := (k.factorial : ℚ) / brkDen x k

/-- The `k`-th term `u_k(x) = [k/x][k/(1-x)]` of the series (2.2). -/
def xiTerm (x : ℚ) (k : ℕ) : ℚ := brk x k * brk (1 - x) k

lemma brkDen_ne_zero {x : ℚ} (hx : HalfOdd x) (k : ℕ) : brkDen x k ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun j _ => (hx.add_natCast j).ne_zero)

lemma brkDen_succ (x : ℚ) (k : ℕ) :
    brkDen x (k + 1) = brkDen x k * (x + ((k : ℚ) + 1)) := by
  unfold brkDen
  rw [prod_range_succ]
  push_cast
  ring

/-- Peeling the first factor: `x · ((x+1)⋯(x+1+k)) = x (x+1) ⋯ (x+k+1)`. -/
lemma brkDen_shift (x : ℚ) (k : ℕ) : x * brkDen (x + 1) k = brkDen x (k + 1) := by
  unfold brkDen
  rw [prod_range_succ' (fun j => (x + (j : ℚ))) (k + 1)]
  have h : ∀ j ∈ range (k + 1), (x + (((j + 1 : ℕ)) : ℚ)) = (x + 1) + (j : ℚ) := by
    intro j _; push_cast; ring
  rw [prod_congr rfl h]
  push_cast
  ring

/-- `(x+k+1) [k+1/x] = (k+1) [k/x]`. -/
lemma brk_succ_mul {x : ℚ} (hx : HalfOdd x) (k : ℕ) :
    (x + ((k : ℚ) + 1)) * brk x (k + 1) = ((k : ℚ) + 1) * brk x k := by
  have h1 : brkDen x k ≠ 0 := brkDen_ne_zero hx k
  have h2 : (x + ((k : ℚ) + 1)) ≠ 0 := by
    simpa using (hx.add_natCast (k + 1)).ne_zero
  unfold brk
  rw [brkDen_succ, Nat.factorial_succ]
  push_cast
  field_simp

/-- `(x+k+1) [k/(x+1)] = x [k/x]`. -/
lemma brk_shift_mul {x : ℚ} (hx : HalfOdd x) (k : ℕ) :
    (x + ((k : ℚ) + 1)) * brk (x + 1) k = x * brk x k := by
  have hxne := hx.ne_zero
  have h1 : brkDen x k ≠ 0 := brkDen_ne_zero hx k
  have h2 : (x + ((k : ℚ) + 1)) ≠ 0 := by
    simpa using (hx.add_natCast (k + 1)).ne_zero
  have hrep : brk (x + 1) k = x * (k.factorial : ℚ) / brkDen x (k + 1) := by
    rw [← brkDen_shift x k, brk, mul_div_mul_left _ _ hxne]
  rw [hrep, brkDen_succ, brk]
  field_simp

/-! ### The shift relation and the telescoping -/

/-- `(x+k+1) · u_k(x+1) = -(k+1-x) · u_k(x)`. -/
lemma xiTerm_shift {x : ℚ} (hx : HalfOdd x) (k : ℕ) :
    (x + ((k : ℚ) + 1)) * xiTerm (x + 1) k = -(((k : ℚ) + 1) - x) * xiTerm x k := by
  have hone : (1 : ℚ) - (x + 1) = -x := by ring
  have hA := brk_shift_mul hx k
  have hB : (-x) * brk (-x) k = (((k : ℚ) + 1) - x) * brk (1 - x) k := by
    have h := brk_shift_mul hx.neg k
    rw [show (-x) + 1 = 1 - x by ring] at h
    linear_combination -h
  unfold xiTerm
  rw [hone]
  linear_combination (brk (-x) k) * hA - (brk x k) * hB

/-- The telescoping function `g_k(x) = -2 (k+1-x) u_k(x) / x`. -/
def gTerm (x : ℚ) (k : ℕ) : ℚ := -2 * (((k : ℚ) + 1) - x) * xiTerm x k / x

lemma gTerm_zero {x : ℚ} (hx : HalfOdd x) : gTerm x 0 = -2 / x ^ 2 := by
  have hxne := hx.ne_zero
  have h1 : (1 : ℚ) - x ≠ 0 := hx.one_sub.ne_zero
  have hb0 : brk x 0 = 1 / x := by simp [brk, brkDen]
  have hb1 : brk (1 - x) 0 = 1 / (1 - x) := by simp [brk, brkDen]
  unfold gTerm xiTerm
  rw [hb0, hb1]
  push_cast
  field_simp
  ring

/-- The telescoping identity: `u_k(x) + u_k(x+1) = g_k(x) - g_{k+1}(x)`. -/
lemma xiTerm_add_telescope {x : ℚ} (hx : HalfOdd x) (k : ℕ) :
    xiTerm x k + xiTerm (x + 1) k = gTerm x k - gTerm x (k + 1) := by
  have hxne := hx.ne_zero
  have hk1 : (x + ((k : ℚ) + 1)) ≠ 0 := by simpa using (hx.add_natCast (k + 1)).ne_zero
  have hk2 : ((k : ℚ) + 2 - x) ≠ 0 := by
    have h := (hx.one_sub.add_natCast (k + 1)).ne_zero
    intro hc; apply h; push_cast at hc ⊢; linarith
  have h1 := xiTerm_shift hx k
  have h2 : (x + ((k : ℚ) + 1)) * (((k : ℚ) + 2 - x) * xiTerm x (k + 1))
      = (((k : ℚ) + 1) ^ 2) * xiTerm x k := by
    have ha := brk_succ_mul hx k
    have hb := brk_succ_mul hx.one_sub k
    rw [show ((1 - x) + ((k : ℚ) + 1)) = ((k : ℚ) + 2 - x) by ring] at hb
    unfold xiTerm
    linear_combination (((k : ℚ) + 2 - x) * brk (1 - x) (k + 1)) * ha
      + (((k : ℚ) + 1) * brk x k) * hb
  have hgk : x * gTerm x k = -2 * (((k : ℚ) + 1) - x) * xiTerm x k := by
    unfold gTerm; field_simp
  have hgk1 : x * gTerm x (k + 1) = -2 * (((k : ℚ) + 2) - x) * xiTerm x (k + 1) := by
    unfold gTerm
    push_cast
    field_simp
    ring
  refine mul_left_cancel₀ hxne ?_
  rw [mul_sub, hgk, hgk1]
  refine mul_left_cancel₀ (mul_ne_zero hk1 hk2) ?_
  linear_combination (x * (((k : ℚ) + 2 - x))) * h1 - (2 * (((k : ℚ) + 2 - x))) * h2

/-! ### Convergence -/

lemma norm_brk_le {x : ℚ} (hx : HalfOdd x) (k : ℕ) :
    ‖((brk x k : ℚ) : ℚ_[2])‖ ≤ (1 / 2 : ℝ) ^ (k + 1) := by
  have hden : ((brkDen x k : ℚ) : ℚ_[2]) = ∏ j ∈ range (k + 1), ((x : ℚ_[2]) + (j : ℚ_[2])) := by
    unfold brkDen
    push_cast
    ring
  have hcast : ((brk x k : ℚ) : ℚ_[2])
      = ((k.factorial : ℚ) : ℚ_[2]) / ((brkDen x k : ℚ) : ℚ_[2]) := by
    unfold brk
    push_cast
    ring
  have hnormden : ‖((brkDen x k : ℚ) : ℚ_[2])‖ = 2 ^ (k + 1) := by
    rw [hden, norm_prod]
    have h : ∀ j ∈ range (k + 1), ‖((x : ℚ_[2]) + (j : ℚ_[2]))‖ = 2 := by
      intro j _
      have hj := (hx.add_natCast j).norm_cast
      have hc : (((x + (j : ℚ) : ℚ)) : ℚ_[2]) = (x : ℚ_[2]) + (j : ℚ_[2]) := by push_cast; ring
      rwa [hc] at hj
    rw [prod_congr rfl h]
    simp
  have hfac : ‖((k.factorial : ℚ) : ℚ_[2])‖ ≤ 1 := by
    have hc : (((k.factorial : ℚ)) : ℚ_[2]) = ((k.factorial : ℤ) : ℚ_[2]) := by push_cast; ring
    rw [hc]
    exact Padic.norm_int_le_one _
  rw [hcast, norm_div, hnormden]
  have hpos : (0 : ℝ) < 2 ^ (k + 1) := by positivity
  rw [div_le_iff₀ hpos]
  calc ‖((k.factorial : ℚ) : ℚ_[2])‖ ≤ 1 := hfac
    _ = (1 / 2 : ℝ) ^ (k + 1) * 2 ^ (k + 1) := by
        rw [div_pow, one_pow]
        field_simp

lemma norm_xiTerm_le {x : ℚ} (hx : HalfOdd x) (k : ℕ) :
    ‖((xiTerm x k : ℚ) : ℚ_[2])‖ ≤ (1 / 4 : ℝ) ^ (k + 1) := by
  have hcast : ((xiTerm x k : ℚ) : ℚ_[2])
      = ((brk x k : ℚ) : ℚ_[2]) * ((brk (1 - x) k : ℚ) : ℚ_[2]) := by
    unfold xiTerm; push_cast; ring
  rw [hcast, norm_mul]
  have h1 := norm_brk_le hx k
  have h2 := norm_brk_le hx.one_sub k
  calc ‖((brk x k : ℚ) : ℚ_[2])‖ * ‖((brk (1 - x) k : ℚ) : ℚ_[2])‖
      ≤ (1 / 2 : ℝ) ^ (k + 1) * (1 / 2 : ℝ) ^ (k + 1) :=
        mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
    _ = (1 / 4 : ℝ) ^ (k + 1) := by
        rw [← mul_pow]
        norm_num

lemma summable_geom_quarter : Summable (fun k : ℕ => (1 / 4 : ℝ) ^ (k + 1)) := by
  have h : Summable (fun k : ℕ => (1 / 4 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  simpa [pow_succ] using h.mul_right (1 / 4 : ℝ)

lemma summable_xiTerm {x : ℚ} (hx : HalfOdd x) :
    Summable (fun k : ℕ => ((xiTerm x k : ℚ) : ℚ_[2])) :=
  Summable.of_norm_bounded summable_geom_quarter (fun k => norm_xiTerm_le hx k)

lemma norm_gTerm_le {x : ℚ} (hx : HalfOdd x) (N : ℕ) :
    ‖((gTerm x N : ℚ) : ℚ_[2])‖ ≤ (1 / 4 : ℝ) ^ (N + 1) := by
  obtain ⟨a, _, hxa⟩ := id hx
  have hxne := hx.ne_zero
  have hzq : (-2 * (((N : ℚ) + 1) - x)) = (((-2 * ((N : ℤ) + 1) + a : ℤ)) : ℚ) := by
    rw [hxa]; push_cast; ring
  have hcast : ((gTerm x N : ℚ) : ℚ_[2])
      = (((-2 * (((N : ℚ) + 1) - x)) : ℚ) : ℚ_[2]) * ((xiTerm x N : ℚ) : ℚ_[2])
          / ((x : ℚ) : ℚ_[2]) := by
    unfold gTerm
    push_cast
    ring
  rw [hcast, norm_div, norm_mul, hx.norm_cast, hzq]
  have hint : ‖((((-2 * ((N : ℤ) + 1) + a : ℤ)) : ℚ) : ℚ_[2])‖ ≤ 1 := by
    have hc : ((((-2 * ((N : ℤ) + 1) + a : ℤ)) : ℚ) : ℚ_[2])
        = (((-2 * ((N : ℤ) + 1) + a : ℤ)) : ℚ_[2]) := by push_cast; ring
    rw [hc]
    exact Padic.norm_int_le_one _
  have hu := norm_xiTerm_le hx N
  have hprod : ‖((((-2 * ((N : ℤ) + 1) + a : ℤ)) : ℚ) : ℚ_[2])‖ * ‖((xiTerm x N : ℚ) : ℚ_[2])‖
      ≤ 1 * (1 / 4 : ℝ) ^ (N + 1) :=
    mul_le_mul hint hu (norm_nonneg _) (by norm_num)
  have hpos : (0 : ℝ) < 2 := by norm_num
  rw [div_le_iff₀ hpos]
  nlinarith [hprod, pow_pos (show (0:ℝ) < 1/4 by norm_num) (N + 1)]

lemma tendsto_gTerm {x : ℚ} (hx : HalfOdd x) :
    Tendsto (fun N : ℕ => ((gTerm x N : ℚ) : ℚ_[2])) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => norm_gTerm_le hx N) ?_
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  exact h.comp (tendsto_add_atTop_nat 1)

/-! ### The Padé function and Lemma 2.1 -/

/-- Beukers' `2`-adic Padé function, equation (2.2):
`Ξ(x) = -∑_{k ≥ 0} [k/x][k/(1-x)]`. -/
noncomputable def XiPade (x : ℚ) : ℚ_[2] := -∑' k : ℕ, ((xiTerm x k : ℚ) : ℚ_[2])

/-- `ξ = Ξ(1/2)`, equation (2.4). -/
noncomputable def xiCat : ℚ_[2] := XiPade (1 / 2)

lemma halfOdd_one_half : HalfOdd (1 / 2 : ℚ) := ⟨1, odd_one, by norm_num⟩

/-- Lemma 2.1, the functional equation `Ξ(x+1) + Ξ(x) = 2/x²`. -/
theorem XiPade_funeq {x : ℚ} (hx : HalfOdd x) :
    XiPade (x + 1) + XiPade x = ((2 / x ^ 2 : ℚ) : ℚ_[2]) := by
  have hx1 : HalfOdd (x + 1) := by simpa using hx.add_natCast 1
  have hs1 := summable_xiTerm hx
  have hs2 := summable_xiTerm hx1
  have hsum : HasSum (fun k : ℕ => ((xiTerm x k : ℚ) : ℚ_[2]) + ((xiTerm (x + 1) k : ℚ) : ℚ_[2]))
      (∑' k, ((xiTerm x k : ℚ) : ℚ_[2]) + ∑' k, ((xiTerm (x + 1) k : ℚ) : ℚ_[2])) :=
    (hs1.hasSum).add (hs2.hasSum)
  have hpartial := hsum.tendsto_sum_nat
  have heq : ∀ N : ℕ,
      ∑ k ∈ range N, (((xiTerm x k : ℚ) : ℚ_[2]) + ((xiTerm (x + 1) k : ℚ) : ℚ_[2]))
        = ((gTerm x 0 : ℚ) : ℚ_[2]) - ((gTerm x N : ℚ) : ℚ_[2]) := by
    intro N
    induction N with
    | zero => simp
    | succ M ih =>
        rw [Finset.sum_range_succ, ih]
        have htel := xiTerm_add_telescope hx M
        have hc : ((xiTerm x M : ℚ) : ℚ_[2]) + ((xiTerm (x + 1) M : ℚ) : ℚ_[2])
            = ((gTerm x M : ℚ) : ℚ_[2]) - ((gTerm x (M + 1) : ℚ) : ℚ_[2]) := by
          rw [show ((xiTerm x M : ℚ) : ℚ_[2]) + ((xiTerm (x + 1) M : ℚ) : ℚ_[2])
              = (((xiTerm x M + xiTerm (x + 1) M : ℚ)) : ℚ_[2]) by push_cast; ring, htel]
          push_cast
          ring
        rw [hc]
        ring
  have hlim2 : Tendsto (fun N : ℕ =>
      ∑ k ∈ range N, (((xiTerm x k : ℚ) : ℚ_[2]) + ((xiTerm (x + 1) k : ℚ) : ℚ_[2])))
      atTop (𝓝 (((gTerm x 0 : ℚ) : ℚ_[2]) - 0)) := by
    simp only [heq]
    exact tendsto_const_nhds.sub (tendsto_gTerm hx)
  have hkey := tendsto_nhds_unique hpartial hlim2
  have hg0 : ((gTerm x 0 : ℚ) : ℚ_[2]) = ((-2 / x ^ 2 : ℚ) : ℚ_[2]) := by rw [gTerm_zero hx]
  unfold XiPade
  rw [show -∑' k, ((xiTerm (x + 1) k : ℚ) : ℚ_[2]) + -∑' k, ((xiTerm x k : ℚ) : ℚ_[2])
      = -(∑' k, ((xiTerm x k : ℚ) : ℚ_[2]) + ∑' k, ((xiTerm (x + 1) k : ℚ) : ℚ_[2])) by ring,
    hkey, sub_zero, hg0]
  push_cast
  ring

end Catalan
