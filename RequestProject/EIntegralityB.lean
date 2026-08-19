import RequestProject.EClosedForm
import RequestProject.EDenominator

/-!
# Integrality of the modular `E`-family numerators: `D_N² B_N ∈ ℤ`

This is the integrality half of Imported Theorem E for the *numerator* row.  Combining

* the closed form `B_N = ∑_{k ≤ N} C(2k,k)² c_k (-4)^{N-k} C(k, N-k)` (`Be_closed_form`), with
  `c_k = (1/4) ∑_{j<k} 4^j / (C(2j,j)(2j+1)²)`, and
* the arithmetic estimate `4 C(2j,j)(2j+1)² ∣ D_k² C(2k,k)² 4^j` for `j < k`
  (`central_denom_dvd`),

every single term of the double sum `D_N² B_N` is an integer.
-/

namespace Catalan

open Finset

lemma Dlcm_dvd_Dlcm {k N : ℕ} (h : k ≤ N) : Dlcm k ∣ Dlcm N := by
  refine Finset.lcm_dvd (fun b hb => ?_)
  obtain ⟨hb1, hb2⟩ := Finset.mem_Icc.1 hb
  exact dvd_Dlcm hb1 (le_trans hb2 h)

/-- The subring of `ℚ` consisting of the integers. -/
noncomputable def ZSub : Subring ℚ := (Int.castRingHom ℚ).range

lemma mem_ZSub_iff (x : ℚ) : x ∈ ZSub ↔ ∃ z : ℤ, (z : ℚ) = x := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, hz⟩

/-- A single term of the double sum is an integer. -/
lemma denom_term_isInt {N j k : ℕ} (hjk : j < k) (hkN : k ≤ N) :
    ((Dlcm N : ℚ) ^ 2 * (Nat.centralBinom k : ℚ) ^ 2 * (1 / 4))
      * ((4 : ℚ) ^ j / ((Nat.centralBinom j : ℚ) * (2 * j + 1) ^ 2)) ∈ ZSub := by
  have hdvd : 4 * Nat.centralBinom j * (2 * j + 1) ^ 2 ∣
      (Dlcm N) ^ 2 * (Nat.centralBinom k) ^ 2 * 4 ^ j := by
    have h1 := central_denom_dvd hjk
    have h2 : (Dlcm k) ^ 2 ∣ (Dlcm N) ^ 2 := pow_dvd_pow_of_dvd (Dlcm_dvd_Dlcm hkN) 2
    exact h1.trans (mul_dvd_mul_right (mul_dvd_mul_right h2 _) _)
  obtain ⟨c, hc⟩ := hdvd
  rw [mem_ZSub_iff]
  refine ⟨(c : ℤ), ?_⟩
  have hcQ : ((Dlcm N : ℚ)) ^ 2 * (Nat.centralBinom k : ℚ) ^ 2 * (4 : ℚ) ^ j
      = (4 * (Nat.centralBinom j : ℚ) * (2 * (j : ℚ) + 1) ^ 2) * (c : ℚ) := by
    have := congrArg (fun m : ℕ => (m : ℚ)) hc
    push_cast at this
    linarith [this]
  have hbj : (Nat.centralBinom j : ℚ) ≠ 0 := centralBinom_ne_zero j
  have h2j : (2 * (j : ℚ) + 1) ≠ 0 := by positivity
  field_simp
  push_cast
  linear_combination (-1 : ℚ) * hcQ

/-- **Imported Theorem E, integrality half**: `D_N² B_N` is an integer. -/
theorem Dlcm_sq_mul_Be_isInt (N : ℕ) : ∃ z : ℤ, (z : ℚ) = (Dlcm N : ℚ) ^ 2 * Be N := by
  rw [← mem_ZSub_iff]
  rw [Be_closed_form, Finset.mul_sum]
  refine Subring.sum_mem _ (fun k hk => ?_)
  simp only [Finset.mem_range] at hk
  have hkN : k ≤ N := by omega
  have hterm : (Dlcm N : ℚ) ^ 2 *
      ((Nat.centralBinom k : ℚ) ^ 2 * cCoef k * ((-4 : ℚ) ^ (N - k) * (k.choose (N - k))))
      = ((Dlcm N : ℚ) ^ 2 * (Nat.centralBinom k : ℚ) ^ 2 * cCoef k)
        * ((-4 : ℚ) ^ (N - k) * (k.choose (N - k))) := by ring
  rw [hterm]
  refine Subring.mul_mem _ ?_ ?_
  · have hsum : (Dlcm N : ℚ) ^ 2 * (Nat.centralBinom k : ℚ) ^ 2 * cCoef k
        = ∑ j ∈ range k, ((Dlcm N : ℚ) ^ 2 * (Nat.centralBinom k : ℚ) ^ 2 * (1 / 4))
            * ((4 : ℚ) ^ j / ((Nat.centralBinom j : ℚ) * (2 * j + 1) ^ 2)) := by
      unfold cCoef
      rw [show (Dlcm N : ℚ) ^ 2 * (Nat.centralBinom k : ℚ) ^ 2 *
          ((1 / 4) * ∑ j ∈ range k, (4 : ℚ) ^ j / ((Nat.centralBinom j : ℚ) * (2 * j + 1) ^ 2))
          = ((Dlcm N : ℚ) ^ 2 * (Nat.centralBinom k : ℚ) ^ 2 * (1 / 4)) *
            ∑ j ∈ range k, (4 : ℚ) ^ j / ((Nat.centralBinom j : ℚ) * (2 * j + 1) ^ 2) by ring,
        Finset.mul_sum]
    rw [hsum]
    refine Subring.sum_mem _ (fun j hj => ?_)
    simp only [Finset.mem_range] at hj
    exact denom_term_isInt hj hkN
  · rw [mem_ZSub_iff]
    exact ⟨(-4 : ℤ) ^ (N - k) * (k.choose (N - k) : ℤ), by push_cast; ring⟩

/-- The first-row numerator `Y₁ n = 2 S n B_{6n}` is an integer. -/
theorem Y1row_isInt (n : ℕ) : ∃ z : ℤ, (z : ℚ) = 2 * (Sfac n : ℚ) * Be (6 * n) := by
  obtain ⟨z, hz⟩ := Dlcm_sq_mul_Be_isInt (6 * n)
  refine ⟨2 * z, ?_⟩
  have hS : ((Sfac n : ℕ) : ℚ) = (Dlcm (6 * n) : ℚ) ^ 2 := by
    unfold Sfac
    push_cast
    ring
  rw [hS]
  push_cast
  linarith [hz]

end Catalan
