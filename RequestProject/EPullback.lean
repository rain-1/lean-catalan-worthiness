import RequestProject.Pullback
import RequestProject.Beukers

/-!
# The modular `E`-row as a quadratic pullback, and its `2`-adic limit

Sections 6 and 7 of the unconditional note.  Over `ℚ_[2]` we prove the two generating function
identities (6.11) and (6.12),

`A(z) = (1-8z) Y₀(16z(1-4z))`,  `16 B(z) = (1-8z) Y₁(16z(1-4z))`,

and deduce (Lemma 7.1 and Theorem 7.2) that `2 B_n / A_n → ξ/8`, i.e. `𝒢_{E,2} = ξ/8`.
-/

namespace Catalan

open PowerSeries Filter Topology

/-! ### The four sequences, viewed over `ℚ_[2]` -/

/-- `q_k(1/2)` in `ℚ_[2]`. -/
noncomputable def qhalf (k : ℕ) : ℚ_[2] := ((bq (1 / 2) k : ℚ) : ℚ_[2])

/-- `p_k(1/2)` in `ℚ_[2]`. -/
noncomputable def phalf (k : ℕ) : ℚ_[2] := ((bp (1 / 2) k : ℚ) : ℚ_[2])

/-- `A_n` in `ℚ_[2]`. -/
noncomputable def Acast (n : ℕ) : ℚ_[2] := ((Ae n : ℚ) : ℚ_[2])

/-- `B_n` in `ℚ_[2]`. -/
noncomputable def Bcast (n : ℕ) : ℚ_[2] := ((Be n : ℚ) : ℚ_[2])

lemma qhalf_rec (m : ℕ) :
    4 * ((m : ℚ_[2]) + 2) ^ 2 * qhalf (m + 2)
      = (8 * ((m : ℚ_[2]) + 1) ^ 2 + 8 * ((m : ℚ_[2]) + 1) + 3) * qhalf (m + 1)
        - 4 * ((m : ℚ_[2]) + 1) ^ 2 * qhalf m := by
  have h := bq_rec (1 / 2 : ℚ) m
  simp only [bL, bC, bR] at h
  have hc := congrArg (fun z : ℚ => ((z : ℚ) : ℚ_[2])) h
  simp only [qhalf]
  push_cast at hc ⊢
  linear_combination 4 * hc

lemma phalf_rec (m : ℕ) :
    4 * ((m : ℚ_[2]) + 2) ^ 2 * phalf (m + 2)
      = (8 * ((m : ℚ_[2]) + 1) ^ 2 + 8 * ((m : ℚ_[2]) + 1) + 3) * phalf (m + 1)
        - 4 * ((m : ℚ_[2]) + 1) ^ 2 * phalf m := by
  have h := bp_rec (1 / 2 : ℚ) m
  simp only [bL, bC, bR] at h
  have hc := congrArg (fun z : ℚ => ((z : ℚ) : ℚ_[2])) h
  simp only [phalf]
  push_cast at hc ⊢
  linear_combination 4 * hc

lemma Acast_rec (m : ℕ) :
    ((m : ℚ_[2]) + 2) ^ 2 * Acast (m + 2)
      = (12 * ((m : ℚ_[2]) + 1) * ((m : ℚ_[2]) + 2) + 4) * Acast (m + 1)
        - 32 * ((m : ℚ_[2]) + 1) ^ 2 * Acast m := by
  have h := Ae_rec m
  simp only [LE, CE, RE] at h
  have hc := congrArg (fun z : ℚ => ((z : ℚ) : ℚ_[2])) h
  simp only [Acast]
  push_cast at hc ⊢
  linear_combination hc

lemma Bcast_rec (m : ℕ) :
    ((m : ℚ_[2]) + 2) ^ 2 * (16 * Bcast (m + 2))
      = (12 * ((m : ℚ_[2]) + 1) * ((m : ℚ_[2]) + 2) + 4) * (16 * Bcast (m + 1))
        - 32 * ((m : ℚ_[2]) + 1) ^ 2 * (16 * Bcast m) := by
  have h := Be_rec m
  simp only [LE, CE, RE] at h
  have hc := congrArg (fun z : ℚ => ((z : ℚ) : ℚ_[2])) h
  simp only [Bcast]
  push_cast at hc ⊢
  linear_combination 16 * hc

@[simp] lemma qhalf_zero : qhalf 0 = 1 := by simp [qhalf]
@[simp] lemma qhalf_one : qhalf 1 = 3 / 4 := by
  simp [qhalf, bq_one]
  norm_num
@[simp] lemma phalf_zero : phalf 0 = 0 := by simp [phalf]
@[simp] lemma phalf_one : phalf 1 = 1 := by simp [phalf]
@[simp] lemma Acast_zero : Acast 0 = 1 := by simp [Acast]
@[simp] lemma Acast_one : Acast 1 = 4 := by simp [Acast]
@[simp] lemma Bcast_zero : Bcast 0 = 0 := by simp [Bcast]
@[simp] lemma Bcast_one : Bcast 1 = 1 := by simp [Bcast]

/-! ### The two generating function identities -/

lemma LBop_mk_qhalf : LBop (mk qhalf) = 0 := by
  rw [LBop_mk qhalf qhalf_rec]
  norm_num

lemma LBop_mk_phalf : LBop (mk phalf) = C 4 := by
  rw [LBop_mk phalf phalf_rec]
  norm_num

lemma LEop_mk_Acast : LEop (mk Acast) = 0 := by
  rw [LEop_mk Acast Acast_rec]
  norm_num

lemma LEop_mk_Bcast : LEop (mk (fun n => 16 * Bcast n)) = C 16 * X := by
  rw [LEop_mk (fun n => 16 * Bcast n) Bcast_rec]
  norm_num

lemma coeff_substT_eq_sum (F : ℚ_[2]⟦X⟧) (n : ℕ) :
    coeff n (substT F) = ∑ k ∈ Finset.range (n + 1), coeff k F * coeff n ((Tsub : ℚ_[2]⟦X⟧) ^ k) := by
  have hTpow : ∀ k : ℕ, (Tsub : ℚ_[2]⟦X⟧) ^ k = X ^ k * (16 - 64 * X) ^ k := by
    intro k
    rw [← mul_pow]
    congr 1
    rw [Tsub]
    ring
  have hvanish : ∀ k : ℕ, n < k → coeff n ((Tsub : ℚ_[2]⟦X⟧) ^ k) = 0 := by
    intro k hk
    rw [hTpow k, coeff_Xpow_mul]
    exact if_neg (by omega)
  rw [substT_eq, coeff_subst' hasSubst_T]
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.range (n + 1)) ?_]
  · simp [smul_eq_mul]
  · intro k hk
    simp only [Function.mem_support] at hk
    simp only [Finset.coe_range, Set.mem_Iio]
    by_contra hcon
    exact hk (by rw [hvanish k (by omega)]; simp)

lemma coeff_zero_substT (F : ℚ_[2]⟦X⟧) : coeff 0 (substT F) = coeff 0 F := by
  rw [coeff_substT_eq_sum]
  simp

/-- Equation (6.11): `A(z) = (1-8z) Y₀(16z(1-4z))`. -/
theorem A_eq_pullback : mk Acast = Gser * substT (mk qhalf) := by
  refine LEop_injective ?_ ?_
  · rw [LEop_mk_Acast, LEop_pullback, LBop_mk_qhalf]
    simp
  · rw [coeff_mk]
    have h1 : coeff 0 (Gser * substT (mk qhalf)) = coeff 0 (substT (mk qhalf)) := by
      rw [Gser]
      simp [mul_comm]
    rw [h1, coeff_zero_substT]
    simp

/-- Equation (6.12): `16 B(z) = (1-8z) Y₁(16z(1-4z))`. -/
theorem B_eq_pullback : mk (fun n => 16 * Bcast n) = Gser * substT (mk phalf) := by
  refine LEop_injective ?_ ?_
  · rw [LEop_mk_Bcast, LEop_pullback, LBop_mk_phalf, substT_C,
      show (C (16 : ℚ_[2]) : ℚ_[2]⟦X⟧) = 16 from PowerSeries.ext (congrFun rfl),
      show (C (4 : ℚ_[2]) : ℚ_[2]⟦X⟧) = 4 from PowerSeries.ext (congrFun rfl)]
    ring
  · rw [coeff_mk]
    have h1 : coeff 0 (Gser * substT (mk phalf)) = coeff 0 (substT (mk phalf)) := by
      rw [Gser]
      simp [mul_comm]
    rw [h1, coeff_zero_substT]
    simp

/-! ### Integrality and vanishing of the coefficients of `t^k` -/

@[simp] lemma coeff_succ_four (i : ℕ) : coeff (i + 1) (4 : ℚ_[2]⟦X⟧) = 0 := by
  rw [show (4 : ℚ_[2]⟦X⟧) = C (4 : ℚ_[2]) from PowerSeries.ext (congrFun rfl)]
  simp

lemma norm_coeff_mul_le_one {f g : ℚ_[2]⟦X⟧} (hf : ∀ j, ‖coeff j f‖ ≤ 1)
    (hg : ∀ j, ‖coeff j g‖ ≤ 1) (n : ℕ) : ‖coeff n (f * g)‖ ≤ 1 := by
  rw [PowerSeries.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num) ?_
  intro p _
  rw [norm_mul]
  exact mul_le_one₀ (hf _) (norm_nonneg _) (hg _)

lemma norm_coeff_one_sub_four_X (j : ℕ) : ‖coeff j (1 - 4 * X : ℚ_[2]⟦X⟧)‖ ≤ 1 := by
  match j with
  | 0 => simp
  | 1 =>
      have : coeff 1 (1 - 4 * X : ℚ_[2]⟦X⟧) = -4 := by
        simp [PowerSeries.coeff_one]
      rw [this]
      have h4 : ((-4 : ℚ_[2])) = (((-4 : ℚ)) : ℚ_[2]) := by norm_num
      rw [h4, norm_ratCast_padic2 (by norm_num : (-4 : ℚ) ≠ 0)]
      have hv : padicValRat 2 (-4 : ℚ) = 2 := by
        rw [show ((-4 : ℚ)) = ((-1 : ℤ) : ℚ) * ((2 : ℚ) ^ 2) by norm_num,
          padicValRat.mul (by norm_num) (by norm_num),
          padicValRat_two_of_odd_int ⟨-1, by ring⟩, padicValRat_two_two_pow 2]
        norm_num
      rw [hv]
      norm_num
  | (k + 2) =>
      have : coeff (k + 2) (1 - 4 * X : ℚ_[2]⟦X⟧) = 0 := by
        simp [PowerSeries.coeff_one]
      rw [this]
      norm_num

lemma norm_coeff_one_sub_four_X_pow (k j : ℕ) :
    ‖coeff j ((1 - 4 * X : ℚ_[2]⟦X⟧) ^ k)‖ ≤ 1 := by
  induction k generalizing j with
  | zero =>
      match j with
      | 0 => simp
      | (i + 1) => simp
  | succ k ih =>
      rw [pow_succ]
      exact norm_coeff_mul_le_one ih norm_coeff_one_sub_four_X j

lemma coeff_one_sub_four_X_pow_eq_zero (k j : ℕ) (h : k < j) :
    coeff j ((1 - 4 * X : ℚ_[2]⟦X⟧) ^ k) = 0 := by
  induction k generalizing j with
  | zero =>
      simp only [pow_zero, PowerSeries.coeff_one]
      exact if_neg (by omega)
  | succ k ih =>
      rw [pow_succ, PowerSeries.coeff_mul]
      refine Finset.sum_eq_zero ?_
      intro p hp
      have hp' : p.1 + p.2 = j := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
      by_cases h2 : p.2 ≤ 1
      · rw [ih p.1 (by omega)]
        ring
      · have : coeff p.2 (1 - 4 * X : ℚ_[2]⟦X⟧) = 0 := by
          match hp2 : p.2 with
          | 0 => omega
          | 1 => omega
          | (i + 2) => simp [PowerSeries.coeff_one]
        rw [this]
        ring

lemma norm_sixteen_pow (k : ℕ) : ‖((16 : ℚ_[2]) ^ k)‖ = (1 / 16 : ℝ) ^ k := by
  have h16 : ‖((16 : ℚ_[2]))‖ = (1 / 16 : ℝ) := by
    have hc : ((16 : ℚ_[2])) = (((16 : ℚ)) : ℚ_[2]) := by norm_num
    rw [hc, norm_ratCast_padic2 (by norm_num : (16 : ℚ) ≠ 0)]
    have hv : padicValRat 2 (16 : ℚ) = 4 := by
      rw [show ((16 : ℚ)) = ((2 : ℚ) ^ 4) by norm_num, padicValRat_two_two_pow 4]
      norm_num
    rw [hv]
    norm_num
  rw [norm_pow, h16]

lemma Tpow_eq (k : ℕ) :
    (Tsub : ℚ_[2]⟦X⟧) ^ k = X ^ k * ((16 : ℚ_[2]⟦X⟧) ^ k * (1 - 4 * X) ^ k) := by
  rw [← mul_pow, ← mul_pow]
  congr 1
  rw [Tsub]
  ring

lemma norm_coeff_Tpow (k n : ℕ) :
    ‖coeff n ((Tsub : ℚ_[2]⟦X⟧) ^ k)‖ ≤ (1 / 16 : ℝ) ^ k := by
  rw [Tpow_eq, coeff_Xpow_mul]
  by_cases hk : k ≤ n
  · rw [if_pos hk]
    have h16 : ((16 : ℚ_[2]⟦X⟧) ^ k) = C ((16 : ℚ_[2]) ^ k) := by
      rw [map_pow]
      congr 1
    rw [h16, coeff_C_mul, norm_mul, norm_sixteen_pow]
    have := norm_coeff_one_sub_four_X_pow k (n - k)
    nlinarith [norm_nonneg (coeff (n - k) ((1 - 4 * X : ℚ_[2]⟦X⟧) ^ k)),
      pow_pos (by norm_num : (0:ℝ) < 1/16) k]
  · rw [if_neg hk]
    simp

lemma coeff_Tpow_eq_zero (k n : ℕ) (h : 2 * k < n) :
    coeff n ((Tsub : ℚ_[2]⟦X⟧) ^ k) = 0 := by
  rw [Tpow_eq, coeff_Xpow_mul]
  by_cases hk : k ≤ n
  · rw [if_pos hk]
    have h16 : ((16 : ℚ_[2]⟦X⟧) ^ k) = C ((16 : ℚ_[2]) ^ k) := by
      rw [map_pow]
      congr 1
    rw [h16, coeff_C_mul, coeff_one_sub_four_X_pow_eq_zero k (n - k) (by omega)]
    ring
  · exact if_neg hk

end Catalan
