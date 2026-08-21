import RequestProject.NesterenkoHypergeometric

/-!
# The exact Nesterenko period series

This file begins the unconditional proof of the bridge between the audited
partial-fraction row and the intrinsic `2`-adic hypergeometric factor.  The
series used in Nesterenko's proof has coefficient

`ν! / (3/2)_(ν-1) * R_n(ν)`.

After the zero block of length `4n`, put `ν = 4n+k`.  The theorem
`nestRSeriesTerm_succ` proves directly that the resulting rational term has
the same consecutive quotient as `nestHyperTerm`.
-/

namespace Catalan

open scoped BigOperators

/-- The continued weight `ν!/(3/2)_(ν-1)`, written without a negative
Pochhammer index.  The formula also gives the required value `1/2` at `ν=0`. -/
noncomputable def nestRWeight (ν : ℕ) : ℚ :=
  (Nat.factorial ν : ℚ) * ((ν : ℚ) + 1 / 2) /
    nestPochhammerThreeHalves ν

/-- The audited specialized rational function `R_n(t)`, evaluated at a
natural argument. -/
noncomputable def nestRAt (n t : ℕ) : ℚ :=
  ((Nat.factorial (3 * n) : ℚ) * nestPochhammerThreeHalves (3 * n - 1) /
      (Nat.factorial (4 * n) : ℚ)) *
    (∏ r ∈ Finset.range (4 * n), ((t : ℚ) - r)) /
    (∏ r ∈ Finset.range (3 * n + 1), ((t : ℚ) + r + 1 / 2)) ^ 2

/-- The shifted rational-series coefficient
`w_(4n+k) R_n(4n+k)`.  The numerator product of `R_n` has already been
cancelled to `(4n+k)!/k!`; retaining this cancellation in the definition
makes the hypergeometric quotient transparent. -/
noncomputable def nestRSeriesTerm (n k : ℕ) : ℚ :=
  ((Nat.factorial (3 * n) : ℚ) * nestPochhammerThreeHalves (3 * n - 1) /
      (Nat.factorial (4 * n) : ℚ)) *
    nestRWeight (4 * n + k) *
    ((Nat.factorial (4 * n + k) : ℚ) / (Nat.factorial k : ℚ)) /
    nestPochhammer ((4 * n + k : ℕ) + (1 : ℚ) / 2) (3 * n + 1) ^ 2

lemma nestRAt_eq_zero_of_lt (n t : ℕ) (ht : t < 4 * n) : nestRAt n t = 0 := by
  unfold nestRAt
  have hmem : t ∈ Finset.range (4 * n) := Finset.mem_range.mpr ht
  rw [Finset.prod_eq_zero hmem]
  · ring
  · push_cast
    ring

lemma nestRAt_numerator_shift (n k : ℕ) :
    (∏ r ∈ Finset.range (4 * n), (((4 * n + k : ℕ) : ℚ) - r)) =
      (Nat.factorial (4 * n + k) : ℚ) / (Nat.factorial k : ℚ) := by
  have hprod :
      (∏ r ∈ Finset.range (4 * n), (((4 * n + k : ℕ) : ℚ) - r)) =
        (((4 * n + k).descFactorial (4 * n) : ℕ) : ℚ) := by
    rw [Nat.descFactorial_eq_prod_range]
    push_cast
    apply Finset.prod_congr rfl
    intro r hr
    rw [Nat.cast_sub]
    · push_cast
      ring
    · have hr' := Finset.mem_range.mp hr
      exact (Nat.le_of_lt hr').trans (Nat.le_add_right (4 * n) k)
  rw [hprod]
  have hfac := Nat.factorial_mul_descFactorial (show 4 * n ≤ 4 * n + k by omega)
  rw [show 4 * n + k - 4 * n = k by omega] at hfac
  have hfacQ := congrArg (fun z : ℕ => (z : ℚ)) hfac
  push_cast at hfacQ
  field_simp
  simpa [mul_comm] using hfacQ

lemma nestRAt_denominator_shift (n k : ℕ) :
    (∏ r ∈ Finset.range (3 * n + 1),
        (((4 * n + k : ℕ) : ℚ) + r + 1 / 2)) =
      nestPochhammer (((4 * n + k : ℕ) : ℚ) + 1 / 2) (3 * n + 1) := by
  unfold nestPochhammer
  apply Finset.prod_congr rfl
  intro r _
  push_cast
  ring

/-- The shifted coefficient really is `w_(4n+k) R_n(4n+k)`. -/
theorem nestRSeriesTerm_eq_weight_mul_R (n k : ℕ) :
    nestRSeriesTerm n k = nestRWeight (4 * n + k) * nestRAt n (4 * n + k) := by
  rw [nestRSeriesTerm, nestRAt, nestRAt_numerator_shift,
    nestRAt_denominator_shift]
  ring

lemma nestRWeight_ne_zero (ν : ℕ) : nestRWeight ν ≠ 0 := by
  unfold nestRWeight
  apply div_ne_zero
  · apply mul_ne_zero
    · positivity
    · positivity
  · rw [nestPochhammerThreeHalves_eq]
    positivity

/-- Moving the starting point of a finite rising factorial by one. -/
lemma nestPochhammer_shift_mul (x : ℚ) (k : ℕ) :
    x * nestPochhammer (x + 1) k = nestPochhammer x k * (x + k) := by
  induction k with
  | zero => simp [nestPochhammer]
  | succ k ih =>
      rw [nestPochhammer_succ, nestPochhammer_succ]
      rw [← mul_assoc, ih]
      push_cast
      ring

lemma nestRWeight_succ (ν : ℕ) :
    nestRWeight (ν + 1) = nestRWeight ν *
      (((ν : ℚ) + 1) / ((ν : ℚ) + 1 / 2)) := by
  change (Nat.factorial (ν + 1) : ℚ) * (((ν + 1 : ℕ) : ℚ) + 1 / 2) /
      nestPochhammer (3 / 2) (ν + 1) =
    ((Nat.factorial ν : ℚ) * ((ν : ℚ) + 1 / 2) /
      nestPochhammer (3 / 2) ν) * (((ν : ℚ) + 1) / ((ν : ℚ) + 1 / 2))
  rw [nestPochhammer_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

private lemma series_step_algebra (W F a b c d P Q : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hshift : a * Q = P * b) :
    (W * (c / a)) * (F * c / d) / Q ^ 2 =
      (W * F / P ^ 2) * (a * c ^ 2 / (b ^ 2 * d)) := by
  have hsquare : a ^ 2 * Q ^ 2 = P ^ 2 * b ^ 2 := by
    calc
      a ^ 2 * Q ^ 2 = (a * Q) ^ 2 := by ring
      _ = (P * b) ^ 2 := by rw [hshift]
      _ = P ^ 2 * b ^ 2 := by ring
  field_simp [ha, hb, hd, hP, hQ]
  calc
    W * c ^ 2 * F * P ^ 2 * b ^ 2 = W * c ^ 2 * F * (P ^ 2 * b ^ 2) := by ring
    _ = W * c ^ 2 * F * (a ^ 2 * Q ^ 2) := by rw [hsquare]
    _ = W * c ^ 2 * a ^ 2 * F * Q ^ 2 := by ring

set_option maxHeartbeats 800000 in
/-- The exact consecutive quotient of the shifted rational-function series.
This is the quotient of the `₃F₂` term in `nestHyperTerm`. -/
theorem nestRSeriesTerm_succ (n k : ℕ) :
    nestRSeriesTerm n (k + 1) = nestRSeriesTerm n k *
      ((((4 * n + k : ℕ) : ℚ) + 1 / 2) *
          (((4 * n + k : ℕ) : ℚ) + 1) ^ 2 /
        (((((7 * n + k : ℕ) : ℚ) + 3 / 2) ^ 2) *
          (((k : ℕ) : ℚ) + 1))) := by
  have hstart : (((4 * n + k : ℕ) : ℚ) + 1 / 2) ≠ 0 := by positivity
  have hfac : (Nat.factorial k : ℚ) ≠ 0 := by positivity
  have hfac' : (Nat.factorial (k + 1) : ℚ) ≠ 0 := by positivity
  have hp : nestPochhammer
      (((4 * n + k : ℕ) : ℚ) + 1 / 2) (3 * n + 1) ≠ 0 := by
    apply nestPochhammer_ne_zero
    refine ⟨8 * (n : ℤ) + 2 * (k : ℤ) + 1, ?_, ?_⟩
    · exact ⟨4 * (n : ℤ) + (k : ℤ), by omega⟩
    · push_cast
      ring
  have hp' : nestPochhammer
      (((4 * n + (k + 1) : ℕ) : ℚ) + 1 / 2) (3 * n + 1) ≠ 0 := by
    apply nestPochhammer_ne_zero
    refine ⟨8 * (n : ℤ) + 2 * ((k + 1 : ℕ) : ℤ) + 1, ?_, ?_⟩
    · exact ⟨4 * (n : ℤ) + ((k + 1 : ℕ) : ℤ), by omega⟩
    · push_cast
      ring
  have hshift := nestPochhammer_shift_mul
    (((4 * n + k : ℕ) : ℚ) + 1 / 2) (3 * n + 1)
  rw [show (((4 * n + k : ℕ) : ℚ) + 1 / 2) + 1 =
      (((4 * n + (k + 1) : ℕ) : ℚ) + 1 / 2) by push_cast; ring] at hshift
  have hb : ((((7 * n + k : ℕ) : ℚ) + 3 / 2)) ≠ 0 := by positivity
  have hd : (((k : ℕ) : ℚ) + 1) ≠ 0 := by positivity
  let W : ℚ :=
    ((Nat.factorial (3 * n) : ℚ) * nestPochhammerThreeHalves (3 * n - 1) /
      (Nat.factorial (4 * n) : ℚ)) * nestRWeight (4 * n + k)
  let F : ℚ := (Nat.factorial (4 * n + k) : ℚ) / (Nat.factorial k : ℚ)
  have halg := series_step_algebra W F
    (((4 * n + k : ℕ) : ℚ) + 1 / 2)
    (((7 * n + k : ℕ) : ℚ) + 3 / 2)
    (((4 * n + k : ℕ) : ℚ) + 1)
    (((k : ℕ) : ℚ) + 1)
    (nestPochhammer (((4 * n + k : ℕ) : ℚ) + 1 / 2) (3 * n + 1))
    (nestPochhammer (((4 * n + (k + 1) : ℕ) : ℚ) + 1 / 2) (3 * n + 1))
    hstart hb hd hp hp' (by
      convert hshift using 1
      push_cast
      ring)
  rw [nestRSeriesTerm, nestRSeriesTerm,
    show 4 * n + (k + 1) = (4 * n + k) + 1 by omega,
    nestRWeight_succ, Nat.factorial_succ, Nat.factorial_succ]
  dsimp [W, F] at halg
  convert halg using 1 <;> push_cast <;>
    field_simp [hfac, hfac', hp, hp', hstart, hb, hd] <;> ring

/-- The intrinsic hypergeometric term has the same exact quotient. -/
theorem nestHyperTerm_succ_exact (n k : ℕ) :
    nestHyperTerm n (k + 1) = nestHyperTerm n k *
      ((((4 * n + k : ℕ) : ℚ) + 1 / 2) *
          (((4 * n + k : ℕ) : ℚ) + 1) ^ 2 /
        (((((7 * n + k : ℕ) : ℚ) + 3 / 2) ^ 2) *
          (((k : ℕ) : ℚ) + 1))) := by
  rw [nestHyperTerm, nestHyperTerm,
    nestPochhammer_succ, nestPochhammer_succ, nestPochhammer_succ,
    Nat.factorial_succ]
  push_cast
  field_simp
  ring

/-- Splitting a finite rising factorial after `m` factors. -/
lemma nestPochhammer_add (x : ℚ) (m k : ℕ) :
    nestPochhammer x (m + k) =
      nestPochhammer x m * nestPochhammer (x + m) k := by
  induction k with
  | zero => simp [nestPochhammer]
  | succ k ih =>
      rw [Nat.add_succ, nestPochhammer_succ, nestPochhammer_succ, ih]
      push_cast
      ring

/-- `(1/2)_m = (2m)!/(4^m m!)`. -/
lemma nestPochhammer_one_half_eq (m : ℕ) :
    nestPochhammer (1 / 2) m =
      (Nat.factorial (2 * m) : ℚ) /
        ((4 : ℚ) ^ m * (Nat.factorial m : ℚ)) := by
  induction m with
  | zero => norm_num [nestPochhammer]
  | succ m ih =>
      rw [nestPochhammer_succ, ih,
        show 2 * (m + 1) = (2 * m + 1) + 1 by omega,
        Nat.factorial_succ,
        show 2 * m + 1 = 2 * m + 1 by rfl,
        Nat.factorial_succ, Nat.factorial_succ m]
      push_cast
      field_simp
      ring

lemma nestPochhammer_four_n_half_eq (n : ℕ) :
    nestPochhammer ((4 * n : ℕ) + (1 : ℚ) / 2) (3 * n + 1) =
      ((Nat.factorial (14 * n + 2) : ℚ) *
          (4 : ℚ) ^ (4 * n) * (Nat.factorial (4 * n) : ℚ)) /
        ((4 : ℚ) ^ (7 * n + 1) * (Nat.factorial (7 * n + 1) : ℚ) *
          (Nat.factorial (8 * n) : ℚ)) := by
  have hsplit := nestPochhammer_add (1 / 2 : ℚ) (4 * n) (3 * n + 1)
  rw [show 4 * n + (3 * n + 1) = 7 * n + 1 by omega,
    nestPochhammer_one_half_eq, nestPochhammer_one_half_eq] at hsplit
  have hne : nestPochhammer (1 / 2 : ℚ) (4 * n) ≠ 0 :=
    nestPochhammer_ne_zero halfOdd_one_half _
  rw [show (1 / 2 : ℚ) + (4 * n : ℕ) =
      ((4 * n : ℕ) : ℚ) + 1 / 2 by push_cast; ring] at hsplit
  rw [show 2 * (7 * n + 1) = 14 * n + 2 by omega,
    show 2 * (4 * n) = 8 * n by omega] at hsplit
  field_simp at hsplit ⊢
  simpa only [mul_assoc, mul_comm, mul_left_comm] using hsplit.symm

/-- The first shifted rational-series term is the audited beta prefactor. -/
theorem nestRSeriesTerm_zero (n : ℕ) (hn : 1 ≤ n) :
    nestRSeriesTerm n 0 = nestPrefactor n := by
  rw [nestRSeriesTerm]
  simp only [Nat.add_zero]
  rw [nestRWeight, nestPochhammer_four_n_half_eq,
    nestPochhammerThreeHalves_eq, nestPochhammerThreeHalves_eq]
  simp only [Nat.add_zero, Nat.factorial_zero, Nat.cast_one, div_one]
  have h3 : 3 * n - 1 + 1 = 3 * n := by omega
  have h6 : 2 * (3 * n - 1) + 1 = 6 * n - 1 := by omega
  have h8 : 2 * (4 * n) + 1 = 8 * n + 1 := by omega
  rw [h6, h8]
  have hf3 : Nat.factorial (3 * n) =
      (3 * n) * Nat.factorial (3 * n - 1) := by
    simpa [h3] using Nat.factorial_succ (3 * n - 1)
  have hf6 : Nat.factorial (6 * n) =
      (6 * n) * Nat.factorial (6 * n - 1) := by
    have h6' : 6 * n - 1 + 1 = 6 * n := by omega
    simpa [h6'] using Nat.factorial_succ (6 * n - 1)
  have hf8 : Nat.factorial (8 * n + 1) =
      (8 * n + 1) * Nat.factorial (8 * n) := Nat.factorial_succ (8 * n)
  unfold nestPrefactor
  rw [hf3, hf6, hf8]
  push_cast
  field_simp
  have hpow3 : (4 : ℚ) ^ (3 * n) = 4 * 4 ^ (3 * n - 1) := by
    conv_lhs => rw [show 3 * n = (3 * n - 1) + 1 by omega, pow_succ]
    ring
  have hpow14 : (4 : ℚ) ^ (14 * n) = 4 ^ (11 * n) * 4 ^ (3 * n) := by
    rw [← pow_add]
    congr 1
    omega
  have hpowsq : ((4 : ℚ) ^ (7 * n + 1)) ^ 2 = 4 ^ (14 * n + 2) := by
    rw [← pow_mul]
    congr 1
    omega
  have hpowrhs : (4 : ℚ) ^ (3 * n - 1) * 4 ^ (4 * n) * 4 ^ (7 * n + 2) =
      4 ^ (14 * n + 1) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  have hpowstep : (4 : ℚ) ^ (14 * n + 2) = 4 * 4 ^ (14 * n + 1) := by
    rw [show 14 * n + 2 = (14 * n + 1) + 1 by omega, pow_succ]
    ring
  have hrhs : (4 : ℚ) ^ (3 * n - 1) * 2 * ((n : ℚ) * 8 + 1) * 4 ^ (4 * n) *
      4 ^ (7 * n + 2) = (2 * ((n : ℚ) * 8 + 1)) * 4 ^ (14 * n + 1) := by
    calc
      (4 : ℚ) ^ (3 * n - 1) * 2 * ((n : ℚ) * 8 + 1) * 4 ^ (4 * n) *
          4 ^ (7 * n + 2) =
        (2 * ((n : ℚ) * 8 + 1)) *
          (4 ^ (3 * n - 1) * 4 ^ (4 * n) * 4 ^ (7 * n + 2)) := by ring
      _ = (2 * ((n : ℚ) * 8 + 1)) * 4 ^ (14 * n + 1) := by rw [hpowrhs]
  rw [hpowsq]
  rw [hrhs]
  rw [hpowstep]
  ring

/-- Exact term-by-term identification of the rational-function series with
the intrinsic hypergeometric series. -/
theorem nestRSeriesTerm_eq (n k : ℕ) (hn : 1 ≤ n) :
    nestRSeriesTerm n k = nestPrefactor n * nestHyperTerm n k := by
  induction k with
  | zero => rw [nestRSeriesTerm_zero n hn, nestHyperTerm_zero, mul_one]
  | succ k ih =>
      rw [nestRSeriesTerm_succ, nestHyperTerm_succ_exact, ih]
      ring

lemma summable_nestRSeriesTerm (n : ℕ) (hn : 1 ≤ n) :
    Summable (fun k : ℕ => ((nestRSeriesTerm n k : ℚ) : ℚ_[2])) := by
  have h := (summable_nestHyperTerm n).mul_left
    (((nestPrefactor n : ℚ) : ℚ_[2]))
  refine h.congr (fun k => ?_)
  rw [nestRSeriesTerm_eq n k hn]
  push_cast
  ring

/-- `nestJ2` is exactly the `2`-adic sum of Nesterenko's shifted rational
function series. -/
theorem nestJ2_eq_tsum_R (n : ℕ) (hn : 1 ≤ n) :
    nestJ2 n = ∑' k : ℕ, ((nestRSeriesTerm n k : ℚ) : ℚ_[2]) := by
  rw [nestJ2, nestHyperFactor, ← tsum_mul_left]
  apply tsum_congr
  intro k
  rw [nestRSeriesTerm_eq n k hn]
  push_cast
  ring

/-! ### The `2`-adic Nielsen special-value series -/

/-- The coefficient of Nesterenko's `f₂(1)` series. -/
noncomputable def nestF2Term (k : ℕ) : ℚ :=
  (Nat.factorial k : ℚ) / nestPochhammerThreeHalves k /
    ((k : ℚ) + 1 / 2)

lemma nestF2Term_factorial (k : ℕ) :
    nestF2Term k =
      2 * (4 : ℚ) ^ k * (Nat.factorial k : ℚ) ^ 2 /
        ((Nat.factorial (2 * k + 1) : ℚ) * (2 * k + 1 : ℚ)) := by
  rw [nestF2Term, factorial_div_nestPochhammerThreeHalves]
  field_simp

lemma nestF2Term_ne_zero (k : ℕ) : nestF2Term k ≠ 0 := by
  rw [nestF2Term_factorial]
  positivity

/-- Exact valuation of the `f₂` coefficient. -/
theorem nestF2Term_v2 (k : ℕ) :
    padicValRat 2 (nestF2Term k) =
      2 * (k : ℤ) + 1 - (s2 k : ℤ) := by
  rw [nestF2Term_factorial,
    padicValRat.div (by positivity) (by positivity),
    padicValRat.mul (by norm_num) (by positivity),
    padicValRat.mul (by positivity) (by positivity),
    padicValRat.mul (by positivity) (by positivity),
    padicValRat.pow, padicValRat.pow, nest_val_factorial, nest_val_factorial]
  have h2 : padicValRat 2 (2 : ℚ) = 1 :=
    padicValRat.self (p := 2) (by norm_num)
  have h4 : padicValRat 2 (4 : ℚ) = 2 := by
    rw [show (4 : ℚ) = 2 * 2 by norm_num,
      padicValRat.mul (by norm_num) (by norm_num), h2]
    norm_num
  have hodd : Odd (2 * (k : ℤ) + 1) := ⟨k, by ring⟩
  have hvodd : padicValRat 2 ((2 * k + 1 : ℕ) : ℚ) = 0 := by
    rw [show ((2 * k + 1 : ℕ) : ℚ) = ((2 * (k : ℤ) + 1 : ℤ) : ℚ) by push_cast; ring,
      padicValRat_two_of_odd_int hodd]
  have hvodd' : padicValRat 2 (2 * (k : ℚ) + 1) = 0 := by
    rw [show 2 * (k : ℚ) + 1 = ((2 * k + 1 : ℕ) : ℚ) by push_cast; ring,
      hvodd]
  rw [h2, h4, hvodd', s2_two_mul_add_one]
  push_cast
  ring

theorem norm_nestF2Term_le (k : ℕ) :
    ‖((nestF2Term k : ℚ) : ℚ_[2])‖ ≤ (1 / 2 : ℝ) ^ (k + 1) := by
  rw [norm_ratCast_padic2 (nestF2Term_ne_zero k), nestF2Term_v2]
  have hs : (s2 k : ℤ) ≤ (k : ℤ) := by exact_mod_cast s2_le k
  rw [show (1 / 2 : ℝ) ^ (k + 1) = 2 ^ (-((k : ℤ) + 1)) by
    rw [div_pow, one_pow, ← zpow_natCast, zpow_neg]
    norm_num]
  exact zpow_le_zpow_right₀ (by norm_num) (by omega)

lemma summable_nestF2Term :
    Summable (fun k : ℕ => ((nestF2Term k : ℚ) : ℚ_[2])) := by
  have hhalf : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1)) := by
    have h := summable_geometric_of_lt_one (show (0 : ℝ) ≤ 1 / 2 by norm_num)
      (show (1 : ℝ) / 2 < 1 by norm_num)
    simpa [pow_succ] using h.mul_right (1 / 2 : ℝ)
  exact Summable.of_norm_bounded hhalf norm_nestF2Term_le

/-- The convergent `2`-adic continuation of `f₂(1)`. -/
noncomputable def nestF2Padic : ℚ_[2] :=
  ∑' k : ℕ, ((nestF2Term k : ℚ) : ℚ_[2])

end Catalan
