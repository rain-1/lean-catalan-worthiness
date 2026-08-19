import Mathlib

/-!
# The `2`-adic clearing exponent of the Zudilin row

Equation (5.1) of the base note defines

`e_m = min { 6m, 4m + 3 + ⌊log₂(2m-1)⌋ }`,

the exponent for which `2^{e_m} Q_m` and `2^{e_m} D_{2m-1}² P_m` are integers.  Only two
properties of `e` are used downstream, and both are proved here from the definition:

* `eZud_three_mul_lb` : `e_{3n} ≥ 12n + 1`, which is equation (9.2);
* `tendsto_eZud_three_mul` : `e_{3n}/n → 12`, i.e. `e_{3n} = 12n + o(n)`, which is what makes
  the Zudilin row have archimedean rate `A_Z`.
-/

namespace Catalan

open Filter Topology

/-- Equation (5.1): the `2`-adic clearing exponent `e_m` of the Zudilin row. -/
def eZud (m : ℕ) : ℕ := min (6 * m) (4 * m + 3 + Nat.log 2 (2 * m - 1))

/-- Equation (9.2): `e_{3n} ≥ 12n + 1` for `n ≥ 1`. -/
theorem eZud_three_mul_lb (n : ℕ) (hn : 1 ≤ n) : 12 * n + 1 ≤ eZud (3 * n) := by
  have h := Nat.zero_le (Nat.log 2 (2 * (3 * n) - 1))
  simp only [eZud, le_min_iff]
  omega

lemma natLog_le_log_div_log_two {k : ℕ} (hk : k ≠ 0) :
    (Nat.log 2 k : ℝ) ≤ Real.log k / Real.log 2 := by
  have hle : (2 : ℕ) ^ Nat.log 2 k ≤ k := Nat.pow_log_le_self 2 hk
  have hleR : ((2 : ℝ)) ^ Nat.log 2 k ≤ (k : ℝ) := by exact_mod_cast hle
  have hpos : (0 : ℝ) < (2 : ℝ) ^ Nat.log 2 k := by positivity
  have hlog : Real.log ((2 : ℝ) ^ Nat.log 2 k) ≤ Real.log k := Real.log_le_log hpos hleR
  rw [Real.log_pow] at hlog
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ h2]
  linarith

/-- The `⌊log₂⌋` correction term is `o(n)`. -/
lemma tendsto_natLog_div (c : ℕ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => (Nat.log 2 (c * n - 1) : ℝ) / n) atTop (𝓝 0) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hlog : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hcast : Tendsto (fun n : ℕ => (c : ℝ) * n) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hcR tendsto_natCast_atTop_atTop
  have hcomp : Tendsto (fun n : ℕ => Real.log ((c : ℝ) * n) / ((c : ℝ) * n)) atTop (𝓝 0) :=
    hlog.comp hcast
  have hmaj : Tendsto
      (fun n : ℕ => (Real.log ((c : ℝ) * n) / ((c : ℝ) * n)) * ((c : ℝ) / Real.log 2))
      atTop (𝓝 0) := by
    simpa using hcomp.mul_const ((c : ℝ) / Real.log 2)
  refine squeeze_zero' (Eventually.of_forall fun n => by positivity) ?_ hmaj
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hcn : (1 : ℝ) ≤ (c : ℝ) * n := by
    have : (1 : ℕ) ≤ c * n := Nat.one_le_iff_ne_zero.mpr (by positivity)
    exact_mod_cast this
  have hlognn : 0 ≤ Real.log ((c : ℝ) * n) := Real.log_nonneg hcn
  have hbound : (Nat.log 2 (c * n - 1) : ℝ) ≤ Real.log ((c : ℝ) * n) / Real.log 2 := by
    rcases Nat.eq_zero_or_pos (c * n - 1) with hk | hk
    · rw [hk]
      simp only [Nat.log_zero_right, Nat.cast_zero]
      positivity
    · refine (natLog_le_log_div_log_two (by omega)).trans ?_
      have hmono : Real.log ((c * n - 1 : ℕ) : ℝ) ≤ Real.log ((c : ℝ) * n) := by
        refine Real.log_le_log (by exact_mod_cast hk) ?_
        have : ((c * n - 1 : ℕ) : ℝ) ≤ ((c * n : ℕ) : ℝ) := by
          exact_mod_cast Nat.sub_le (c * n) 1
        simpa using this
      gcongr
  calc (Nat.log 2 (c * n - 1) : ℝ) / n
      ≤ (Real.log ((c : ℝ) * n) / Real.log 2) / n := by gcongr
    _ = (Real.log ((c : ℝ) * n) / ((c : ℝ) * n)) * ((c : ℝ) / Real.log 2) := by
        field_simp

/-- `e_{3n} = 12n + o(n)`. -/
theorem tendsto_eZud_three_mul :
    Tendsto (fun n : ℕ => (eZud (3 * n) : ℝ) / n) atTop (𝓝 12) := by
  have hlow : Tendsto (fun n : ℕ => 12 + 3 / (n : ℝ)) atTop (𝓝 12) := by
    simpa using (tendsto_const_nhds (x := (12 : ℝ)) (f := atTop (α := ℕ))).add
      (tendsto_const_div_atTop_nhds_zero_nat (3 : ℝ))
  have hupp : Tendsto
      (fun n : ℕ => 12 + 3 / (n : ℝ) + (Nat.log 2 (6 * n - 1) : ℝ) / n) atTop (𝓝 12) := by
    simpa using hlow.add (tendsto_natLog_div 6 (by norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hupp ?_ ?_
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hle : 12 * n + 3 ≤ eZud (3 * n) := by
      have h := Nat.zero_le (Nat.log 2 (2 * (3 * n) - 1))
      simp only [eZud, le_min_iff]
      omega
    have hleR : (12 : ℝ) * n + 3 ≤ (eZud (3 * n) : ℝ) := by exact_mod_cast hle
    rw [le_div_iff₀ hnR]
    have hexp : (12 + 3 / (n : ℝ)) * n = 12 * n + 3 := by field_simp
    rw [hexp]
    exact hleR
  · filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hle : eZud (3 * n) ≤ 12 * n + 3 + Nat.log 2 (6 * n - 1) := by
      have : eZud (3 * n) ≤ 4 * (3 * n) + 3 + Nat.log 2 (2 * (3 * n) - 1) := min_le_right _ _
      have h6 : 2 * (3 * n) = 6 * n := by ring
      rw [h6] at this
      omega
    have hleR : (eZud (3 * n) : ℝ) ≤ 12 * n + 3 + (Nat.log 2 (6 * n - 1) : ℝ) := by
      exact_mod_cast hle
    rw [div_le_iff₀ hnR]
    have hexp : (12 + 3 / (n : ℝ) + (Nat.log 2 (6 * n - 1) : ℝ) / n) * n
        = 12 * n + 3 + (Nat.log 2 (6 * n - 1) : ℝ) := by
      field_simp
    rw [hexp]
    exact hleR

end Catalan
