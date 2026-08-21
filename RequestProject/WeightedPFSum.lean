import RequestProject.NesterenkoPartialFraction

/-!
# A cancellation-safe weighted partial-fraction summation lemma

The simple-pole tails in the Nesterenko expansion need not be summable over
the reals.  This file therefore works with finite partial sums, cancels their
common prefix using `sum A₁ = 0`, and only then passes to the limit.  The same
statement applies to `ℝ` and to `ℚ_[2]`.
-/

namespace Catalan

open Filter Topology
open scoped BigOperators

section

variable {K : Type*} [NormedField K]

/-- A shifted finite sum differs from the unshifted one by a fixed missing
prefix and a finite tail at the moving endpoint. -/
lemma sum_range_shift_sub (a : ℕ → K) (N j : ℕ) :
    (∑ t ∈ Finset.range N, a (t + j)) - (∑ t ∈ Finset.range N, a t) =
      (∑ r ∈ Finset.range j, a (N + r)) - ∑ r ∈ Finset.range j, a r := by
  have hleft := Finset.sum_range_add a j N
  have hright := Finset.sum_range_add a N j
  simp_rw [Nat.add_comm j] at hleft
  rw [hleft] at hright
  linear_combination hright

/-- If the terms tend to zero, a fixed shift of partial sums has the expected
finite-prefix defect. -/
lemma tendsto_sum_range_shift_sub (a : ℕ → K)
    (ha : Tendsto a atTop (𝓝 0)) (j : ℕ) :
    Tendsto
      (fun N => (∑ t ∈ Finset.range N, a (t + j)) -
        ∑ t ∈ Finset.range N, a t)
      atTop (𝓝 (-∑ r ∈ Finset.range j, a r)) := by
  have htail : Tendsto (fun N => ∑ r ∈ Finset.range j, a (N + r))
      atTop (𝓝 0) := by
    have h := tendsto_finsetSum (Finset.range j) (fun r _ =>
      ha.comp (tendsto_add_atTop_nat r))
    simpa only [Function.comp_apply, Finset.sum_const_zero] using h
  convert htail.sub tendsto_const_nhds using 1
  · funext N
    rw [sum_range_shift_sub]
  · simp

/-- The universal weighted finite-partial-fraction lemma.  It deliberately
concludes convergence of the combined partial sums, rather than attempting to
sum the generally divergent simple-pole pieces separately. -/
theorem pf_weighted_partial_sums
    (d : ℕ) (a b term A1 A2 : ℕ → K) (bsum : K)
    (ha : Tendsto a atTop (𝓝 0))
    (hb : HasSum b bsum)
    (hA1 : ∑ j ∈ Finset.range d, A1 j = 0)
    (hterm : ∀ t,
      term t = ∑ j ∈ Finset.range d,
        (A1 j * a (t + j) + A2 j * b (t + j))) :
    Tendsto (fun N => ∑ t ∈ Finset.range N, term t) atTop
      (𝓝 ((∑ j ∈ Finset.range d, A2 j) * bsum -
        ∑ j ∈ Finset.range d,
          ((∑ m ∈ Finset.range j, a m) * A1 j +
            (∑ m ∈ Finset.range j, b m) * A2 j))) := by
  have haShift (j : ℕ) : Tendsto
      (fun N => A1 j *
        ((∑ t ∈ Finset.range N, a (t + j)) -
          ∑ t ∈ Finset.range N, a t)) atTop
      (𝓝 (A1 j * (-∑ m ∈ Finset.range j, a m))) :=
    (tendsto_const_nhds.mul (tendsto_sum_range_shift_sub a ha j))
  have hbShift (j : ℕ) : Tendsto
      (fun N => A2 j * ∑ t ∈ Finset.range N, b (t + j)) atTop
      (𝓝 (A2 j * (bsum - ∑ m ∈ Finset.range j, b m))) := by
    have hj : HasSum (fun t => b (t + j))
        (bsum - ∑ m ∈ Finset.range j, b m) :=
      (hasSum_nat_add_iff' j).2 hb
    exact tendsto_const_nhds.mul hj.tendsto_sum_nat
  have hlim :=
    (tendsto_finsetSum (Finset.range d) (fun j _ => haShift j)).add
      (tendsto_finsetSum (Finset.range d) (fun j _ => hbShift j))
  convert hlim using 1
  · funext N
    have hfinite :
        (∑ t ∈ Finset.range N, term t) =
          (∑ j ∈ Finset.range d,
            A1 j * ∑ t ∈ Finset.range N, a (t + j)) +
          ∑ j ∈ Finset.range d,
            A2 j * ∑ t ∈ Finset.range N, b (t + j) := by
      calc
        (∑ t ∈ Finset.range N, term t) =
            ∑ t ∈ Finset.range N, ∑ j ∈ Finset.range d,
              (A1 j * a (t + j) + A2 j * b (t + j)) := by
                apply Finset.sum_congr rfl
                intro t _
                exact hterm t
        _ = ∑ j ∈ Finset.range d, ∑ t ∈ Finset.range N,
              (A1 j * a (t + j) + A2 j * b (t + j)) := Finset.sum_comm
        _ = _ := by
          simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hfinite]
    have hcancel :
        (∑ j ∈ Finset.range d,
          A1 j * ∑ t ∈ Finset.range N, a (t + j)) =
          ∑ j ∈ Finset.range d,
            A1 j * ((∑ t ∈ Finset.range N, a (t + j)) -
              ∑ t ∈ Finset.range N, a t) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
      rw [hA1, zero_mul, sub_zero]
    rw [hcancel]
  · apply congrArg nhds
    rw [Finset.sum_add_distrib]
    simp_rw [mul_neg, mul_sub]
    rw [Finset.sum_mul]
    simp_rw [mul_comm (A1 _) _, mul_comm (A2 _) _]
    rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    ring

end

end Catalan
