import RequestProject.CatalanIntegral

/-!
# The accelerated series and the limit of the weights `c_k`

Combining the evaluation `∑_j wR j = 2G` (`CatalanIntegral.lean`) with the definition of the
weights `c_k = (1/4) ∑_{j<k} wR j` gives `c_k → G/2`, together with the bounds
`0 ≤ c_k ≤ G/2`.
-/

namespace Catalan

open Filter Topology Finset


lemma cRe_eq_partial (k : ℕ) : ((cCoef k : ℚ) : ℝ) = (1 / 4) * ∑ j ∈ range k, wR j := by
  rw [cCoef]
  push_cast
  refine congrArg (fun t => (1 / 4 : ℝ) * t) ?_
  refine Finset.sum_congr rfl (fun j _ => ?_)
  unfold wR
  ring

/-- The weights of the closed form of `B_n` converge to `G/2`. -/
theorem tendsto_cCoef :
    Tendsto (fun k => ((cCoef k : ℚ) : ℝ)) atTop (𝓝 (catalanReal / 2)) := by
  have h := summable_wR.hasSum.tendsto_sum_nat
  have h2 := h.const_mul (1 / 4 : ℝ)
  rw [tsum_wR] at h2
  have : (1 / 4 : ℝ) * (2 * catalanReal) = catalanReal / 2 := by ring
  rw [this] at h2
  exact h2.congr (fun k => (cRe_eq_partial k).symm)

lemma cCoef_nonneg (k : ℕ) : (0 : ℝ) ≤ ((cCoef k : ℚ) : ℝ) := by
  rw [cRe_eq_partial]
  have : 0 ≤ ∑ j ∈ range k, wR j := Finset.sum_nonneg (fun j _ => wR_nonneg j)
  linarith

lemma cCoef_le (k : ℕ) : ((cCoef k : ℚ) : ℝ) ≤ catalanReal / 2 := by
  rw [cRe_eq_partial]
  have h1 : ∑ j ∈ range k, wR j ≤ ∑' j, wR j :=
    summable_wR.sum_le_tsum _ (fun j _ => wR_nonneg j)
  rw [tsum_wR] at h1
  linarith

end Catalan
