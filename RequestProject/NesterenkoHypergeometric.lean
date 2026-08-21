import RequestProject.NesterenkoCoefficients
import RequestProject.XiSeries

/-!
# The intrinsic Nesterenko hypergeometric factor over `ℚ₂`

The key estimate is that the `k`th term has `2`-adic norm at most `2⁻ᵏ`.
This makes the nonconstant tail divisible by `2`, so the sum is a unit.
-/

namespace Catalan

open Filter Topology
open scoped BigOperators

/-- A finite rational rising factorial `(x)_k`. -/
noncomputable def nestPochhammer (x : ℚ) (k : ℕ) : ℚ :=
  ∏ r ∈ Finset.range k, (x + r)

lemma nestPochhammer_succ (x : ℚ) (k : ℕ) :
    nestPochhammer x (k + 1) = nestPochhammer x k * (x + k) := by
  rw [nestPochhammer, Finset.prod_range_succ]
  rfl

lemma nestPochhammer_ne_zero {x : ℚ} (hx : HalfOdd x) (k : ℕ) :
    nestPochhammer x k ≠ 0 := by
  unfold nestPochhammer
  exact Finset.prod_ne_zero_iff.mpr fun r _ => (hx.add_natCast r).ne_zero

/-- Every factor of a half-odd rising factorial has `2`-adic norm `2`. -/
lemma norm_nestPochhammer_halfOdd {x : ℚ} (hx : HalfOdd x) (k : ℕ) :
    ‖((nestPochhammer x k : ℚ) : ℚ_[2])‖ = (2 : ℝ) ^ k := by
  have hcast : ((nestPochhammer x k : ℚ) : ℚ_[2]) =
      ∏ r ∈ Finset.range k, ((x : ℚ_[2]) + (r : ℚ_[2])) := by
    unfold nestPochhammer
    push_cast
    ring
  rw [hcast, norm_prod]
  calc
    (∏ r ∈ Finset.range k, ‖(x : ℚ_[2]) + (r : ℚ_[2])‖) =
        ∏ _r ∈ Finset.range k, (2 : ℝ) := by
      apply Finset.prod_congr rfl
      intro r _
      have hr := (hx.add_natCast r).norm_cast
      have hc : (((x + (r : ℚ) : ℚ)) : ℚ_[2]) =
          (x : ℚ_[2]) + (r : ℚ_[2]) := by
        push_cast
        ring
      rwa [hc] at hr
    _ = (2 : ℝ) ^ k := by simp

/-- The natural rising product `(4n+1)_k`. -/
def nestIntPochhammer (n k : ℕ) : ℕ :=
  ∏ r ∈ Finset.range k, (4 * n + 1 + r)

lemma nestIntPochhammer_succ (n k : ℕ) :
    nestIntPochhammer n (k + 1) =
      nestIntPochhammer n k * (4 * n + 1 + k) := by
  simp [nestIntPochhammer, Finset.prod_range_succ]

lemma nestIntPochhammer_mul_factorial (n k : ℕ) :
    nestIntPochhammer n k * Nat.factorial (4 * n) = Nat.factorial (4 * n + k) := by
  induction k with
  | zero => simp [nestIntPochhammer]
  | succ k ih =>
      rw [nestIntPochhammer_succ]
      rw [show 4 * n + (k + 1) = (4 * n + k) + 1 by omega, Nat.factorial_succ]
      calc
        nestIntPochhammer n k * (4 * n + 1 + k) * Nat.factorial (4 * n) =
            (nestIntPochhammer n k * Nat.factorial (4 * n)) * (4 * n + k + 1) := by ring
        _ = Nat.factorial (4 * n + k) * (4 * n + k + 1) := by rw [ih]
        _ = (4 * n + k + 1) * Nat.factorial (4 * n + k) := by ring

/-- `(4n+1)_k = k! * choose(4n+k,k)`. -/
lemma nestIntPochhammer_eq_choose (n k : ℕ) :
    nestIntPochhammer n k = Nat.factorial k * Nat.choose (4 * n + k) k := by
  apply Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos (4 * n))
  rw [nestIntPochhammer_mul_factorial]
  have h := Nat.add_choose_mul_factorial_mul_factorial (4 * n) k
  rw [← h]
  ring

lemma nestPochhammer_four_mul_add_one (n k : ℕ) :
    nestPochhammer ((4 * n + 1 : ℕ) : ℚ) k = (nestIntPochhammer n k : ℚ) := by
  unfold nestPochhammer nestIntPochhammer
  push_cast
  apply Finset.prod_congr rfl
  intro r _
  push_cast
  ring

/-- The `k`th term of the intrinsic `₃F₂(1)` factor. -/
noncomputable def nestHyperTerm (n k : ℕ) : ℚ :=
  nestPochhammer ((4 * n : ℕ) + (1 : ℚ) / 2) k *
      nestPochhammer ((4 * n + 1 : ℕ) : ℚ) k ^ 2 /
    (nestPochhammer ((7 * n : ℕ) + (3 : ℚ) / 2) k ^ 2 *
      (Nat.factorial k : ℚ))

lemma halfOdd_four_mul_add_half (n : ℕ) :
    HalfOdd ((4 * n : ℕ) + (1 : ℚ) / 2) := by
  refine ⟨8 * (n : ℤ) + 1, ⟨4 * (n : ℤ), by omega⟩, ?_⟩
  push_cast
  ring

lemma halfOdd_seven_mul_add_three_halves (n : ℕ) :
    HalfOdd ((7 * n : ℕ) + (3 : ℚ) / 2) := by
  refine ⟨14 * (n : ℤ) + 3, ⟨7 * (n : ℤ) + 1, by omega⟩, ?_⟩
  push_cast
  ring

lemma nestHyperTerm_zero (n : ℕ) : nestHyperTerm n 0 = 1 := by
  norm_num [nestHyperTerm, nestPochhammer]

/-- The elementary estimate behind the unit argument: the half-integral
factors contribute exactly `2⁻ᵏ`, while the remaining quotient is an integer. -/
theorem norm_nestHyperTerm_le (n k : ℕ) :
    ‖((nestHyperTerm n k : ℚ) : ℚ_[2])‖ ≤ (1 / 2 : ℝ) ^ k := by
  let u : ℚ := nestPochhammer ((4 * n : ℕ) + (1 : ℚ) / 2) k
  let d : ℚ := nestPochhammer ((7 * n : ℕ) + (3 : ℚ) / 2) k
  let i : ℕ := nestIntPochhammer n k
  have hu0 : u ≠ 0 := nestPochhammer_ne_zero (halfOdd_four_mul_add_half n) k
  have hd0 : d ≠ 0 := nestPochhammer_ne_zero (halfOdd_seven_mul_add_three_halves n) k
  have hkfac : (Nat.factorial k : ℚ) ≠ 0 := by positivity
  have hsplit : nestHyperTerm n k =
      (u / d ^ 2) * ((i : ℚ) ^ 2 / (Nat.factorial k : ℚ)) := by
    rw [nestHyperTerm, nestPochhammer_four_mul_add_one]
    dsimp [u, d, i]
    field_simp
  have hintQ : (i : ℚ) ^ 2 / (Nat.factorial k : ℚ) =
      ((Nat.factorial k * (Nat.choose (4 * n + k) k) ^ 2 : ℕ) : ℚ) := by
    rw [show i = Nat.factorial k * Nat.choose (4 * n + k) k by
      exact nestIntPochhammer_eq_choose n k]
    push_cast
    field_simp
  have hint :
      ‖((((i : ℚ) ^ 2 / (Nat.factorial k : ℚ) : ℚ)) : ℚ_[2])‖ ≤ 1 := by
    rw [hintQ]
    have hc :
        (((Nat.factorial k * (Nat.choose (4 * n + k) k) ^ 2 : ℕ) : ℚ) : ℚ_[2]) =
          ((Nat.factorial k * (Nat.choose (4 * n + k) k) ^ 2 : ℕ) : ℚ_[2]) := by
      push_cast
      ring
    rw [hc]
    exact Padic.norm_int_le_one _
  have hunorm : ‖((u : ℚ) : ℚ_[2])‖ = (2 : ℝ) ^ k :=
    norm_nestPochhammer_halfOdd (halfOdd_four_mul_add_half n) k
  have hdnorm : ‖((d : ℚ) : ℚ_[2])‖ = (2 : ℝ) ^ k :=
    norm_nestPochhammer_halfOdd (halfOdd_seven_mul_add_three_halves n) k
  have hratio : ‖(((u / d ^ 2 : ℚ)) : ℚ_[2])‖ = (1 / 2 : ℝ) ^ k := by
    push_cast
    rw [norm_div, norm_pow, hunorm, hdnorm]
    rw [div_pow]
    field_simp
    simp
  have hratio' : ‖(u : ℚ_[2]) / (d : ℚ_[2]) ^ 2‖ = (1 / 2 : ℝ) ^ k := by
    simpa using hratio
  rw [hsplit]
  push_cast
  rw [norm_mul, hratio']
  exact mul_le_of_le_one_right (by positivity) (by simpa using hint)

lemma summable_nestHyperTerm (n : ℕ) :
    Summable (fun k : ℕ => ((nestHyperTerm n k : ℚ) : ℚ_[2])) := by
  have hgeom : Summable (fun k : ℕ => (1 / 2 : ℝ) ^ k) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  exact Summable.of_norm_bounded hgeom (norm_nestHyperTerm_le n)

/-- The intrinsic `₃F₂(1)` factor over `ℚ₂`. -/
noncomputable def nestHyperFactor (n : ℕ) : ℚ_[2] :=
  ∑' k : ℕ, ((nestHyperTerm n k : ℚ) : ℚ_[2])

lemma norm_nestHyperTail_le (n : ℕ) :
    ‖∑' k : ℕ, ((nestHyperTerm n (k + 1) : ℚ) : ℚ_[2])‖ ≤ (1 / 2 : ℝ) := by
  refine le_trans (IsUltrametricDist.norm_tsum_le _) (ciSup_le ?_)
  intro k
  refine le_trans (norm_nestHyperTerm_le n (k + 1)) ?_
  have hk : (1 / 2 : ℝ) ^ k ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  rw [pow_succ]
  nlinarith

lemma nestHyperFactor_eq_one_add_tail (n : ℕ) :
    nestHyperFactor n = 1 +
      ∑' k : ℕ, ((nestHyperTerm n (k + 1) : ℚ) : ℚ_[2]) := by
  rw [nestHyperFactor, (summable_nestHyperTerm n).tsum_eq_zero_add,
    nestHyperTerm_zero]
  norm_num

/-- The hypergeometric factor is a `2`-adic unit. -/
theorem norm_nestHyperFactor (n : ℕ) : ‖nestHyperFactor n‖ = 1 := by
  rw [nestHyperFactor_eq_one_add_tail]
  let t : ℚ_[2] := ∑' k : ℕ, ((nestHyperTerm n (k + 1) : ℚ) : ℚ_[2])
  have ht : ‖t‖ < ‖(1 : ℚ_[2])‖ := by
    have hle := norm_nestHyperTail_le n
    change ‖t‖ ≤ (1 / 2 : ℝ) at hle
    norm_num
    linarith
  change ‖(1 : ℚ_[2]) + t‖ = 1
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (ne_of_gt ht)]
  rw [max_eq_left (by simpa using ht.le)]
  norm_num

theorem nestHyperFactor_ne_zero (n : ℕ) : nestHyperFactor n ≠ 0 := by
  apply padic2_ne_zero_of_norm_pos
  rw [norm_nestHyperFactor]
  norm_num

/-- Exact unit valuation, equation (16) of the audit. -/
theorem nestHyperFactor_v2 (n : ℕ) : Padic.valuation (nestHyperFactor n) = 0 := by
  apply padic2_valuation_eq_of_norm (nestHyperFactor_ne_zero n)
  rw [norm_nestHyperFactor]
  norm_num

/-- The intrinsic `2`-adic continuation of the Nesterenko double integral. -/
noncomputable def nestJ2 (n : ℕ) : ℚ_[2] :=
  ((nestPrefactor n : ℚ) : ℚ_[2]) * nestHyperFactor n

theorem nestJ2_ne_zero (n : ℕ) : nestJ2 n ≠ 0 := by
  unfold nestJ2
  apply mul_ne_zero
  · exact_mod_cast (ne_of_gt (by unfold nestPrefactor; positivity : 0 < nestPrefactor n))
  · exact nestHyperFactor_ne_zero n

/-- Exact valuation of the intrinsic linear form, before identifying it with
the partial-fraction expression `4 Bₙ G₂ - Cₙ`. -/
theorem nestJ2_v2 (n : ℕ) :
    Padic.valuation (nestJ2 n) =
      14 * (n : ℤ) + 2 - (s2 n : ℤ) - (s2 (3 * n) : ℤ) := by
  have hp : ((nestPrefactor n : ℚ) : ℚ_[2]) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by unfold nestPrefactor; positivity : 0 < nestPrefactor n))
  rw [nestJ2, Padic.valuation_mul hp (nestHyperFactor_ne_zero n),
    Padic.valuation_ratCast, nestPrefactor_v2, nestHyperFactor_v2]
  ring

/-- Once the finite partial-fraction identity is established, nonvanishing of
the concrete linear form is immediate from the intrinsic product. -/
theorem nestJform_ne_zero_of_eq (n : ℕ)
    (hbridge : nestJ2 n =
      ((4 * nestB n : ℚ) : ℚ_[2]) * GZ2 - ((nestCConcrete n : ℚ) : ℚ_[2])) :
    ((4 * nestB n : ℚ) : ℚ_[2]) * GZ2 - ((nestCConcrete n : ℚ) : ℚ_[2]) ≠ 0 := by
  rw [← hbridge]
  exact nestJ2_ne_zero n

/-- The exact form valuation follows from the same bridge; it is no longer an
independent arithmetic input. -/
theorem nestJform_v2_of_eq (n : ℕ)
    (hbridge : nestJ2 n =
      ((4 * nestB n : ℚ) : ℚ_[2]) * GZ2 - ((nestCConcrete n : ℚ) : ℚ_[2])) :
    Padic.valuation
        (((4 * nestB n : ℚ) : ℚ_[2]) * GZ2 - ((nestCConcrete n : ℚ) : ℚ_[2])) =
      14 * (n : ℤ) + 2 - (s2 n : ℤ) - (s2 (3 * n) : ℤ) := by
  rw [← hbridge]
  exact nestJ2_v2 n

end Catalan
