import RequestProject.EPullback
import RequestProject.Plucker

/-!
# The cross-realization identity `𝒢_{Z,2} = 𝒢_{E,2} = ξ/8`

Section 7 of the unconditional note.  Starting from the two generating function identities
(6.11) and (6.12) proved in `EPullback.lean`, we subtract `ξ` times the first from the second
and read off the coefficients:

* `norm_eps_le`      : `‖ε_k‖ ≤ 4k² 16^{-k}` for `k ≥ 1` (Lemma 3.1 at `x = 1/2`),
* `key_identity`     : `16 B(z) - ξ A(z) = (1-8z) D(t(z))`, equation (7.3),
* `norm_sixteenB_sub`: `‖16 B_n - ξ A_n‖ ≤ 8n² 16^{-n}` for `n ≥ 2` (Lemma 7.1),
* `GE2_eq_xi_div_eight` : Theorem 7.2,
* `cross_identity`   : Theorem 7.3, `𝒢_{Z,2} = 𝒢_{E,2}`,
* `val_plucker_uncond`: Theorem 8.1, the unconditional exact Plücker valuation.
-/

namespace Catalan

open PowerSeries Filter Topology



/-! ### The Padé error sequence -/

/-- `ε_k = p_k(1/2) - ξ q_k(1/2)`, equation (7.1). -/
noncomputable def eps (k : ℕ) : ℚ_[2] := phalf k - xiCat * qhalf k

lemma two_zpow_neg_four_mul (k : ℕ) : (2 : ℝ) ^ (-(4 * (k : ℤ))) = (1 / 16 : ℝ) ^ k := by
  rw [show (-(4 * (k : ℤ))) = (-4 : ℤ) * (k : ℤ) by ring, zpow_mul, zpow_natCast]
  norm_num

/-- Equation (7.2): the fixed-`x = 1/2` instance of Beukers' estimate. -/
lemma norm_eps_le (k : ℕ) (hk : 1 ≤ k) :
    ‖eps k‖ ≤ 4 * (k : ℝ) ^ 2 * (1 / 16 : ℝ) ^ k := by
  have hodd : Odd (1 : ℤ) := ⟨0, by ring⟩
  have hest := beukers_pade_estimate 1 hodd k hk
  rw [show (((1 : ℤ) : ℚ) / 2) = 1 / 2 by norm_num, two_zpow_neg_four_mul] at hest
  simpa [eps, phalf, qhalf, xiCat] using hest

lemma mk_eps : PowerSeries.mk eps = PowerSeries.mk phalf - C xiCat * PowerSeries.mk qhalf := by
  ext n
  simp [eps, coeff_C_mul]

/-! ### Equation (7.3) -/

/-- Equation (7.3): `16 B(z) - ξ A(z) = (1 - 8z) D(t(z))`. -/
theorem key_identity :
    PowerSeries.mk (fun n => 16 * Bcast n - xiCat * Acast n) = Gser * substT (PowerSeries.mk eps) := by
  have hsplit : PowerSeries.mk (fun n => 16 * Bcast n - xiCat * Acast n)
      = PowerSeries.mk (fun n => 16 * Bcast n) - C xiCat * PowerSeries.mk Acast := by
    ext n
    simp [coeff_C_mul]
  rw [hsplit, B_eq_pullback, A_eq_pullback, mk_eps, substT_sub, substT_mul, substT_C]
  ring

/-! ### Coefficient bounds -/

lemma norm_coeff_substT_eps (n : ℕ) (hn : 1 ≤ n) :
    ‖coeff n (substT (PowerSeries.mk eps))‖ ≤ 4 * (n : ℝ) ^ 2 * (1 / 16 : ℝ) ^ n := by
  rw [coeff_substT_eq_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity) ?_
  intro k hk
  have hkn : k ≤ n := by
    have := Finset.mem_range.mp hk
    omega
  rw [coeff_mk, norm_mul]
  by_cases h2 : 2 * k < n
  · rw [coeff_Tpow_eq_zero k n h2, norm_zero, mul_zero]
    positivity
  · have hk1 : 1 ≤ k := by omega
    have hb1 : ‖eps k‖ ≤ 4 * (k : ℝ) ^ 2 * (1 / 16 : ℝ) ^ k := norm_eps_le k hk1
    have hb2 : ‖coeff n ((Tsub : ℚ_[2]⟦X⟧) ^ k)‖ ≤ (1 / 16 : ℝ) ^ k := norm_coeff_Tpow k n
    have hstep : ‖eps k‖ * ‖coeff n ((Tsub : ℚ_[2]⟦X⟧) ^ k)‖
        ≤ (4 * (k : ℝ) ^ 2 * (1 / 16 : ℝ) ^ k) * (1 / 16 : ℝ) ^ k :=
      mul_le_mul hb1 hb2 (norm_nonneg _) (by positivity)
    refine hstep.trans ?_
    have hpow : (1 / 16 : ℝ) ^ k * (1 / 16 : ℝ) ^ k ≤ (1 / 16 : ℝ) ^ n := by
      rw [← pow_add]
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have hkn' : (k : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      have : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    calc (4 * (k : ℝ) ^ 2 * (1 / 16 : ℝ) ^ k) * (1 / 16 : ℝ) ^ k
        = 4 * (k : ℝ) ^ 2 * ((1 / 16 : ℝ) ^ k * (1 / 16 : ℝ) ^ k) := by ring
      _ ≤ 4 * (n : ℝ) ^ 2 * (1 / 16 : ℝ) ^ n := by
          apply mul_le_mul _ hpow (by positivity) (by positivity)
          nlinarith

lemma coeff_Gser_mul (F : ℚ_[2]⟦X⟧) (j : ℕ) :
    coeff (j + 1) (Gser * F) = coeff (j + 1) F - 8 * coeff j F := by
  have hG : (Gser : ℚ_[2]⟦X⟧) * F = F - 8 * (X * F) := by
    rw [Gser]; ring
  rw [hG, map_sub]
  congr 1
  rw [show ((8 : ℚ_[2]⟦X⟧) * (X * F)) = C (8 : ℚ_[2]) * (X * F) by
      rw [show (8 : ℚ_[2]⟦X⟧) = C (8 : ℚ_[2]) from PowerSeries.ext (congrFun rfl)],
    coeff_C_mul, coeff_succ_X_mul]

lemma norm_eight_padic : ‖(8 : ℚ_[2])‖ = (1 / 8 : ℝ) := by
  have h8 : ((8 : ℚ_[2])) = (((8 : ℚ) : ℚ_[2])) := by norm_num
  rw [h8, norm_ratCast_padic2 (by norm_num : (8 : ℚ) ≠ 0)]
  have hv8 : padicValRat 2 (8 : ℚ) = 3 := by
    rw [show ((8 : ℚ)) = ((2 : ℚ) ^ 3) by norm_num, padicValRat_two_two_pow 3]
    norm_num
  rw [hv8]
  norm_num

/-- Lemma 7.1: `‖16 B_n - ξ A_n‖ ≤ 8 n² 16^{-n}` for `n ≥ 2`. -/
lemma norm_sixteenB_sub (n : ℕ) (hn : 2 ≤ n) :
    ‖16 * Bcast n - xiCat * Acast n‖ ≤ 8 * (n : ℝ) ^ 2 * (1 / 16 : ℝ) ^ n := by
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  have hj : 1 ≤ j := by omega
  have hco : (16 * Bcast (j + 1) - xiCat * Acast (j + 1))
      = coeff (j + 1) (Gser * substT (PowerSeries.mk eps)) := by
    rw [← key_identity, coeff_mk]
  rw [hco, coeff_Gser_mul]
  have hA : ‖coeff (j + 1) (substT (PowerSeries.mk eps))‖ ≤ 4 * ((j : ℝ) + 1) ^ 2 * (1 / 16 : ℝ) ^ (j + 1) := by
    have := norm_coeff_substT_eps (j + 1) (by omega)
    simpa using this
  have hB : ‖(8 : ℚ_[2]) * coeff j (substT (PowerSeries.mk eps))‖
      ≤ 8 * ((j : ℝ) + 1) ^ 2 * (1 / 16 : ℝ) ^ (j + 1) := by
    rw [norm_mul, norm_eight_padic]
    have hb := norm_coeff_substT_eps j hj
    have hjle : (j : ℝ) ≤ (j : ℝ) + 1 := by linarith
    have hpos : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    calc (1 / 8 : ℝ) * ‖coeff j (substT (PowerSeries.mk eps))‖
        ≤ (1 / 8 : ℝ) * (4 * (j : ℝ) ^ 2 * (1 / 16 : ℝ) ^ j) := by linarith
      _ = 8 * (j : ℝ) ^ 2 * (1 / 16 : ℝ) ^ (j + 1) := by rw [pow_succ]; ring
      _ ≤ 8 * ((j : ℝ) + 1) ^ 2 * (1 / 16 : ℝ) ^ (j + 1) := by
          have : (j : ℝ) ^ 2 ≤ ((j : ℝ) + 1) ^ 2 := by nlinarith
          have hp : (0 : ℝ) < (1 / 16 : ℝ) ^ (j + 1) := by positivity
          nlinarith
  have hmax : ‖coeff (j + 1) (substT (PowerSeries.mk eps)) - 8 * coeff j (substT (PowerSeries.mk eps))‖
      ≤ 8 * ((j : ℝ) + 1) ^ 2 * (1 / 16 : ℝ) ^ (j + 1) := by
    have hsub : ‖coeff (j + 1) (substT (PowerSeries.mk eps))
          - 8 * coeff j (substT (PowerSeries.mk eps))‖
        ≤ max ‖coeff (j + 1) (substT (PowerSeries.mk eps))‖
            ‖(8 : ℚ_[2]) * coeff j (substT (PowerSeries.mk eps))‖ := by
      rw [sub_eq_add_neg]
      simpa using IsUltrametricDist.norm_add_le_max
        (coeff (j + 1) (substT (PowerSeries.mk eps)))
        (-(8 * coeff j (substT (PowerSeries.mk eps))))
    refine hsub.trans ?_
    refine max_le ?_ hB
    refine hA.trans ?_
    have hp : (0 : ℝ) < (1 / 16 : ℝ) ^ (j + 1) := by positivity
    nlinarith [sq_nonneg ((j : ℝ) + 1)]
  simpa using hmax

/-! ### The `2`-adic size of `A_n` -/

lemma norm_Acast_ge (n : ℕ) : (1 / 4 : ℝ) ^ n ≤ ‖Acast n‖ := by
  have hne : Ae n ≠ 0 := Ae_ne_zero n
  have hnorm : ‖Acast n‖ = (2 : ℝ) ^ (-(2 * (s2 n : ℤ))) := by
    rw [Acast, norm_ratCast_padic2 hne, val_Ae n]
  rw [hnorm]
  have hs : (s2 n : ℤ) ≤ (n : ℤ) := by exact_mod_cast s2_le n
  have h1 : (1 / 4 : ℝ) ^ n = (2 : ℝ) ^ (-(2 * (n : ℤ))) := by
    rw [show (-(2 * (n : ℤ))) = (-2 : ℤ) * (n : ℤ) by ring, zpow_mul, zpow_natCast]
    norm_num
  rw [h1]
  exact zpow_le_zpow_right₀ (by norm_num) (by omega)

lemma norm_Acast_pos (n : ℕ) : (0 : ℝ) < ‖Acast n‖ :=
  lt_of_lt_of_le (by positivity) (norm_Acast_ge n)

/-! ### Theorem 7.2 -/

lemma ratE_sub_xi (n : ℕ) :
    ((RatE n : ℚ) : ℚ_[2]) - xiCat / 8 = (16 * Bcast n - xiCat * Acast n) / (8 * Acast n) := by
  have hAne : Acast n ≠ 0 := by
    have := norm_Acast_pos n
    intro hc
    rw [hc] at this
    simp at this
  have hcast : ((RatE n : ℚ) : ℚ_[2]) = 2 * Bcast n / Acast n := by
    unfold RatE Acast Bcast
    push_cast
    ring
  rw [hcast]
  field_simp
  ring

lemma norm_RatE_sub (n : ℕ) (hn : 2 ≤ n) :
    ‖((RatE n : ℚ) : ℚ_[2]) - xiCat / 8‖ ≤ 64 * (n : ℝ) ^ 2 * (1 / 4 : ℝ) ^ n := by
  rw [ratE_sub_xi n, norm_div, norm_mul, norm_eight_padic]
  have hnum := norm_sixteenB_sub n hn
  have hden := norm_Acast_ge n
  have hpos : (0 : ℝ) < (1 / 4 : ℝ) ^ n := by positivity
  have hdiv : ‖16 * Bcast n - xiCat * Acast n‖ / (1 / 8 * ‖Acast n‖)
      ≤ (8 * (n : ℝ) ^ 2 * (1 / 16 : ℝ) ^ n) / (1 / 8 * (1 / 4 : ℝ) ^ n) := by
    refine div_le_div₀ (by positivity) hnum (by positivity) ?_
    linarith
  refine hdiv.trans ?_
  have hkey : (8 * (n : ℝ) ^ 2 * (1 / 16 : ℝ) ^ n) / (1 / 8 * (1 / 4 : ℝ) ^ n)
      = 64 * (n : ℝ) ^ 2 * ((1 / 16 : ℝ) ^ n / (1 / 4 : ℝ) ^ n) := by
    field_simp
    ring
  rw [hkey]
  have hq : (1 / 16 : ℝ) ^ n / (1 / 4 : ℝ) ^ n = (1 / 4 : ℝ) ^ n := by
    rw [← div_pow]
    norm_num
  rw [hq]

/-- Theorem 7.2: the modular `E`-limit is `ξ/8`. -/
theorem GE2_eq_xi_div_eight : GE2 = xiCat / 8 := by
  have key : Tendsto (fun n => ((RatE n : ℚ) : ℚ_[2])) atTop (𝓝 (xiCat / 8)) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall (fun n => norm_nonneg _))
      (Filter.eventually_atTop.2 ⟨2, norm_RatE_sub⟩) ?_
    have hlim := tendsto_pow_const_mul_const_pow_of_lt_one 2 (r := (1 / 4 : ℝ))
      (by norm_num) (by norm_num)
    have := hlim.const_mul (64 : ℝ)
    simpa [mul_assoc] using this
  exact tendsto_nhds_unique tendsto_GE2 key

/-- Theorem 7.3, the cross-realization identity: `𝒢_{Z,2} = 𝒢_{E,2} = ξ/8`. -/
theorem cross_identity : GZ2 = GE2 := by
  rw [GZ2_eq_xi_div_eight, GE2_eq_xi_div_eight]

/-- Theorem 8.1: the exact Plücker valuation, now unconditional. -/
theorem val_plucker_uncond (m : ℕ) (hm : 1 ≤ m) :
    padicValRat 2 (Pz m * Ae (2 * m) - 2 * Be (2 * m) * Qz m) = 4 * (m : ℤ) - 1 :=
  val_plucker cross_identity m hm


end Catalan
