import RequestProject.RivoalP
import RequestProject.XiSeries
import RequestProject.PadeEstimate

/-!
# The `2`-adic Padé function, and the Zudilin `2`-adic limit

Sections 2--5 of the unconditional note.

Nothing here is assumed: the four results of the literature that this section uses are all
proved elsewhere in the development.  The functional equation `Ξ(x+1) + Ξ(x) = 2/x²` of Lemma 2.1
is `XiPade_funeq` (`XiSeries.lean`), for the Padé function `Ξ` defined there by Beukers'
series (2.2); Beukers' uniform `2`-adic Padé estimate of Lemma 3.1 is `beukers_pade_estimate`
(`PadeEstimate.lean`); and Rivoal's two identifications (4.7) and (4.9) of the Zudilin
denominator and numerator are `bq_xpt_eq_Qz` (`RivoalQ.lean`) and `rivoal_numerator`
(`RivoalP.lean`).

* `XiPade_orbit` is Lemma 5.1, `GZ2_eq_xi_div_eight` is Theorem 5.2.
-/

namespace Catalan

open Filter Topology

/-- The moving half-integer point `x_m = 1/2 - m` is half-odd. -/
lemma halfOdd_xpt (m : ℕ) : HalfOdd (xpt m) :=
  ⟨1 - 2 * (m : ℤ), ⟨-(m : ℤ), by ring⟩, xpt_eq_odd_div_two m⟩

/-- Lemma 5.1: `Ξ(x_m) = (-1)^m (ξ - 8 σ_m)`. -/
theorem XiPade_orbit (m : ℕ) :
    XiPade (xpt m) = (-1 : ℚ_[2]) ^ m * (xiCat - 8 * ((sigmaCat m : ℚ) : ℚ_[2])) := by
  induction m with
  | zero => simp [xiCat, xpt, sigmaCat]
  | succ k ih =>
      have hfun : XiPade (xpt k) + XiPade (xpt (k + 1))
          = ((2 / (xpt (k + 1)) ^ 2 : ℚ) : ℚ_[2]) := by
        have hf := XiPade_funeq (halfOdd_xpt (k + 1))
        rwa [xpt_succ_add_one] at hf
      have hx : ((2 / (xpt (k + 1)) ^ 2 : ℚ) : ℚ_[2])
          = ((8 / (2 * (k : ℚ) + 1) ^ 2 : ℚ) : ℚ_[2]) := by
        congr 1
        have hk0 : (0 : ℚ) ≤ (k : ℚ) := Nat.cast_nonneg k
        have hne : (2 * (k : ℚ) + 1) ≠ 0 := by positivity
        have hlt : xpt (k + 1) < 0 := by
          unfold xpt; push_cast; linarith
        have hxne : xpt (k + 1) ≠ 0 := ne_of_lt hlt
        have hxval : xpt (k + 1) = -(2 * (k : ℚ) + 1) / 2 := by
          unfold xpt; push_cast; ring
        rw [hxval]
        field_simp
        ring
      rw [hx] at hfun
      have hsig : ((sigmaCat (k + 1) : ℚ) : ℚ_[2])
          = ((sigmaCat k : ℚ) : ℚ_[2]) + ((-1 : ℚ) ^ k / (2 * (k : ℚ) + 1) ^ 2 : ℚ) := by
        rw [sigmaCat_succ]
        push_cast
        ring
      have hXik : XiPade (xpt (k + 1))
          = ((8 / (2 * (k : ℚ) + 1) ^ 2 : ℚ) : ℚ_[2]) - XiPade (xpt k) := by
        linear_combination hfun
      rw [hXik, ih, hsig]
      have hne : ((2 * (k : ℚ) + 1) ^ 2 : ℚ) ≠ 0 := by positivity
      have hcast : (((-1 : ℚ) ^ k / (2 * (k : ℚ) + 1) ^ 2 : ℚ) : ℚ_[2])
          = (-1 : ℚ_[2]) ^ k / ((2 * (k : ℚ_[2]) + 1) ^ 2) := by
        push_cast
        ring
      have hden : ((2 * (k : ℚ_[2]) + 1) ^ 2) ≠ 0 := by
        have h1 : (2 * (k : ℚ_[2]) + 1) ≠ 0 := by
          have : ((2 * (k : ℚ) + 1 : ℚ) : ℚ_[2]) ≠ 0 := by
            simpa using (Rat.cast_injective (α := ℚ_[2])).ne_iff.mpr
              (by positivity : (2 * (k : ℚ) + 1) ≠ 0)
          push_cast at this
          exact this
        exact pow_ne_zero _ h1
      have hcast8 : (((8 : ℚ) / (2 * (k : ℚ) + 1) ^ 2 : ℚ) : ℚ_[2])
          = (8 : ℚ_[2]) / ((2 * (k : ℚ_[2]) + 1) ^ 2) := by
        push_cast
        ring
      have hsq : ((-1 : ℚ_[2]) ^ k) * ((-1 : ℚ_[2]) ^ k) = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]
        norm_num
      rw [hcast, hcast8, pow_succ]
      linear_combination (-8 / ((2 * (k : ℚ_[2]) + 1) ^ 2)) * hsq



/-! ### Theorem 5.2 -/

lemma ratZ_sub_xi (m : ℕ) :
    ((RatZ m : ℚ) : ℚ_[2]) - xiCat / 8
      = ((-1 : ℚ_[2]) ^ m / 8) *
        (((bp (xpt m) m : ℚ) : ℚ_[2]) / ((Qz m : ℚ) : ℚ_[2]) - XiPade (xpt m)) := by
  have hQ : ((Qz m : ℚ) : ℚ_[2]) ≠ 0 := by
    simpa using (Rat.cast_injective (α := ℚ_[2])).ne_iff.mpr (Qz_ne_zero m)
  have hR : ((RatZ m : ℚ) : ℚ_[2]) = ((Pz m : ℚ) : ℚ_[2]) / ((Qz m : ℚ) : ℚ_[2]) := by
    unfold RatZ
    push_cast
    ring
  have hP : ((Pz m : ℚ) : ℚ_[2])
      = ((Qz m : ℚ) : ℚ_[2]) * ((sigmaCat m : ℚ) : ℚ_[2])
        + (-1 : ℚ_[2]) ^ m / 8 * ((bp (xpt m) m : ℚ) : ℚ_[2]) := by
    have := rivoal_numerator m
    have hcast := congrArg (fun z : ℚ => ((z : ℚ) : ℚ_[2])) this
    push_cast at hcast
    exact hcast
  have hsq : ((-1 : ℚ_[2]) ^ m) * ((-1 : ℚ_[2]) ^ m) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    simp
  have hXi := XiPade_orbit m
  rw [hR, hP, hXi]
  field_simp
  linear_combination (((Qz m : ℚ) : ℚ_[2]) * xiCat - 8 * ((Qz m : ℚ) : ℚ_[2]) *
    ((sigmaCat m : ℚ) : ℚ_[2])) * hsq

/-- Theorem 5.2: the Zudilin `2`-adic limit is `ξ/8`. -/
theorem GZ2_eq_xi_div_eight : GZ2 = xiCat / 8 := by
  have key : Tendsto (fun m => ((RatZ m : ℚ) : ℚ_[2])) atTop (𝓝 (xiCat / 8)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hbound : ∀ m : ℕ, 1 ≤ m →
        ‖((RatZ m : ℚ) : ℚ_[2]) - xiCat / 8‖ ≤ 32 * (m : ℝ) ^ 2 * (1 / 64 : ℝ) ^ m := by
      intro m hm
      have hQ : ((Qz m : ℚ) : ℚ_[2]) ≠ 0 := by
        simpa using (Rat.cast_injective (α := ℚ_[2])).ne_iff.mpr (Qz_ne_zero m)
      -- the error term
      set err : ℚ_[2] :=
        ((bp (xpt m) m : ℚ) : ℚ_[2]) - XiPade (xpt m) * ((Qz m : ℚ) : ℚ_[2]) with herr
      have hfac : ((RatZ m : ℚ) : ℚ_[2]) - xiCat / 8
          = ((-1 : ℚ_[2]) ^ m / 8) * (err / ((Qz m : ℚ) : ℚ_[2])) := by
        rw [ratZ_sub_xi m, herr]
        field_simp
      -- Beukers' estimate at `a = 1 - 2m`
      have hodd : Odd (1 - 2 * (m : ℤ)) := ⟨-(m : ℤ), by ring⟩
      have hxa : ((1 - 2 * (m : ℤ) : ℤ) : ℚ) / 2 = xpt m := (xpt_eq_odd_div_two m).symm
      have hest := beukers_pade_estimate (1 - 2 * (m : ℤ)) hodd m hm
      rw [hxa, bq_xpt_eq_Qz m] at hest
      have herrb : ‖err‖ ≤ 4 * (m : ℝ) ^ 2 * (2 : ℝ) ^ (-(4 * (m : ℤ))) := by
        rw [herr]
        exact hest
      -- the size of `Q_m`
      have hnq : ‖((Qz m : ℚ) : ℚ_[2])‖ = (2 : ℝ) ^ (-(-4 * (m : ℤ) + 2 * (s2 m : ℤ))) := by
        rw [norm_ratCast_padic2 (Qz_ne_zero m), val_Qz m]
      have hqge : (2 : ℝ) ^ (2 * (m : ℤ)) ≤ ‖((Qz m : ℚ) : ℚ_[2])‖ := by
        rw [hnq]
        have hs : (s2 m : ℤ) ≤ (m : ℤ) := by exact_mod_cast s2_le m
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hqpos : (0 : ℝ) < ‖((Qz m : ℚ) : ℚ_[2])‖ := by
        have : ((Qz m : ℚ) : ℚ_[2]) ≠ 0 := hQ
        positivity
      have hnorm8 : ‖((-1 : ℚ_[2]) ^ m / 8)‖ = 8 := by
        have h1 : ‖((-1 : ℚ_[2]) ^ m)‖ = 1 := by
          rw [norm_pow, norm_neg, norm_one, one_pow]
        rw [norm_div, h1]
        have h8 : ((8 : ℚ_[2])) = (((8 : ℚ) : ℚ_[2])) := by norm_num
        rw [h8, norm_ratCast_padic2 (by norm_num : (8:ℚ) ≠ 0)]
        have hv8 : padicValRat 2 (8 : ℚ) = 3 := by
          rw [show ((8 : ℚ)) = ((2 : ℚ) ^ 3) by norm_num, padicValRat_two_two_pow 3]
          norm_num
        rw [hv8]
        norm_num
      calc ‖((RatZ m : ℚ) : ℚ_[2]) - xiCat / 8‖
          = 8 * (‖err‖ / ‖((Qz m : ℚ) : ℚ_[2])‖) := by
            rw [hfac, norm_mul, hnorm8, norm_div]
        _ ≤ 8 * ((4 * (m : ℝ) ^ 2 * (2 : ℝ) ^ (-(4 * (m : ℤ)))) / (2 : ℝ) ^ (2 * (m : ℤ))) := by
            have hmono : ‖err‖ / ‖((Qz m : ℚ) : ℚ_[2])‖
                ≤ (4 * (m : ℝ) ^ 2 * (2 : ℝ) ^ (-(4 * (m : ℤ)))) / (2 : ℝ) ^ (2 * (m : ℤ)) :=
              div_le_div₀ (by positivity) herrb (by positivity) hqge
            linarith
        _ = 32 * (m : ℝ) ^ 2 * (1 / 64 : ℝ) ^ m := by
            have hz : (2 : ℝ) ^ (-(4 * (m : ℤ))) / (2 : ℝ) ^ (2 * (m : ℤ)) = (1 / 64 : ℝ) ^ m := by
              rw [← zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0),
                show (-(4 * (m : ℤ)) - 2 * (m : ℤ)) = (-6 : ℤ) * (m : ℤ) by ring,
                zpow_mul, zpow_natCast]
              norm_num
            rw [mul_div_assoc, hz]
            ring
    refine squeeze_zero' (Eventually.of_forall (fun m => norm_nonneg _))
      (Filter.eventually_atTop.2 ⟨1, hbound⟩) ?_
    have hlim := tendsto_pow_const_mul_const_pow_of_lt_one 2 (r := (1/64:ℝ))
      (by norm_num) (by norm_num)
    have := hlim.const_mul (32:ℝ)
    simpa [mul_assoc] using this
  exact tendsto_nhds_unique tendsto_GZ2 key


end Catalan
