import PrimeNumberTheoremAnd.Consequences
import PrimeNumberTheoremAnd.IEANTN.Lcm
import RequestProject.LcmRow
import RequestProject.RateTools

/-!
# Prime-number-theorem input

This adapts PNT+'s weak prime number theorem to the normalization used by
`LogRate`. PNT+ identifies the logarithm of its least-common-multiple
sequence `L` with Chebyshev's function `ψ`; its `WeakPNT''` says `ψ(x) ~ x`.
-/

namespace Catalan

open Filter Topology Asymptotics

lemma Dlcm_eq_pnt_L (N : ℕ) : Dlcm N = Lcm.L N := rfl

theorem rate_Dlcm : LogRate (fun N => ((Dlcm N : ℕ) : ℝ)) 1 := by
  unfold LogRate
  have hψR : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) := by
    have h := WeakPNT''
    rw [Asymptotics.isEquivalent_iff_tendsto_one
      (by filter_upwards [eventually_gt_atTop 0] with x hx; exact hx.ne')] at h
    convert h using 1 <;> ext x <;> rfl
  have hψ : Tendsto (fun N : ℕ => Chebyshev.psi N / N) atTop (𝓝 1) :=
    hψR.comp tendsto_natCast_atTop_atTop
  refine Filter.Tendsto.congr' ?_ hψ
  filter_upwards with N
  rw [abs_of_nonneg (Nat.cast_nonneg _), Dlcm_eq_pnt_L, Lcm.log_L_eq_psi]

end Catalan
