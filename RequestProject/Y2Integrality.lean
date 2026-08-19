import RequestProject.PadeIntegrality
import RequestProject.RivoalP
import RequestProject.Rows
import RequestProject.ZudilinExponent

/-!
# Integrality of the Zudilin second row

The second row of the two-row construction is

`Y₂ n = 2^{e_{3n}} · S n · P_{3n}`,   `S n = D_{6n}²`,

and this file proves that it is an *integer* (`Y2row_isInt`), which is the last piece of
imported arithmetic of the base note still carried as a hypothesis.

The proof combines three ingredients:

* Rivoal's identity `P_m = Q_m σ_m + (-1)^m p_m(x_m)/8` (`rivoal_numerator`);
* `2^{4m} Q_m ∈ ℤ` (`two_pow_mul_Qz_isInt`) together with the elementary
  `D_N² σ_m ∈ ℤ` for `2m - 1 ≤ N` (`Dlcm_sq_mul_sigmaCat_isInt`);
* `2^{4m} D_m² p_m(x_m) ∈ ℤ` (`two_pow_mul_Dlcm_sq_mul_bp_isInt`).

The clearing exponent is large enough: `e_{3n} ≥ 12n + 3 = 4·(3n) + 3` for `n ≥ 1`.
-/

namespace Catalan

open Finset

/-- `D_N² σ_m ∈ ℤ` as soon as `2m - 1 ≤ N`: each denominator `(2k+1)²` with `k < m` divides
`D_N²`. -/
lemma Dlcm_sq_mul_sigmaCat_isInt (m N : ℕ) (h : 2 * m ≤ N + 1) :
    ∃ z : ℤ, (z : ℚ) = (Dlcm N : ℚ) ^ 2 * sigmaCat m := by
  classical
  refine (mem_ZSub_iff _).1 ?_
  rw [sigmaCat, Finset.mul_sum]
  refine Subring.sum_mem _ (fun k hk => ?_)
  simp only [Finset.mem_range] at hk
  obtain ⟨c, hc⟩ : (2 * k + 1) ∣ Dlcm N := dvd_Dlcm (by omega) (by omega)
  refine (mem_ZSub_iff _).2 ⟨(-1) ^ k * (c : ℤ) ^ 2, ?_⟩
  have hcQ : (Dlcm N : ℚ) = (2 * (k : ℚ) + 1) * (c : ℚ) := by
    have := congrArg (fun t : ℕ => (t : ℚ)) hc
    push_cast at this
    linarith [this]
  have hne : (2 * (k : ℚ) + 1) ≠ 0 := by positivity
  rw [hcQ]
  push_cast
  field_simp

/-- The clearing exponent is at least `4·(3n) + 3` for `n ≥ 1`. -/
lemma eZud_three_mul_ge (n : ℕ) (hn : 1 ≤ n) : 12 * n + 3 ≤ eZud (3 * n) := by
  have h := Nat.zero_le (Nat.log 2 (2 * (3 * n) - 1))
  simp only [eZud, le_min_iff]
  omega

/-- **The Zudilin second row is an integer.** -/
theorem Y2row_isInt (n : ℕ) : ∃ z : ℤ, (z : ℚ) = Y2row eZud n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨0, ?_⟩
    have hP : Pz 0 = 0 := by
      simp
    simp [Y2row, hP]
  · set m := 3 * n with hm
    set e := eZud (3 * n) with he
    have hem : 4 * m + 3 ≤ e := by
      have := eZud_three_mul_ge n hn
      omega
    have hDdvd : Dlcm m ∣ Dlcm (6 * n) := Dlcm_dvd_Dlcm (by omega)
    obtain ⟨t, ht⟩ := hDdvd
    have h1 : (2 : ℚ) ^ e * (Dlcm (6 * n) : ℚ) ^ 2 * (Qz m * sigmaCat m) ∈ ZSub := by
      obtain ⟨z1, hz1⟩ := two_pow_mul_Qz_isInt m e (by omega)
      obtain ⟨z2, hz2⟩ := Dlcm_sq_mul_sigmaCat_isInt m (6 * n) (by omega)
      refine (mem_ZSub_iff _).2 ⟨z1 * z2, ?_⟩
      push_cast
      rw [hz1, hz2]
      ring
    have h2 : (2 : ℚ) ^ e * (Dlcm (6 * n) : ℚ) ^ 2 * ((-1 : ℚ) ^ m / 8 * bp (xpt m) m) ∈ ZSub := by
      obtain ⟨z, hz⟩ := two_pow_mul_Dlcm_sq_mul_bp_isInt m
      refine (mem_ZSub_iff _).2 ⟨(-1) ^ m * 2 ^ (e - 3 - 4 * m) * (t : ℤ) ^ 2 * z, ?_⟩
      have hsplit : (2 : ℚ) ^ e = 2 ^ (e - 3 - 4 * m) * 2 ^ (4 * m) * 8 := by
        rw [show (8 : ℚ) = 2 ^ 3 by norm_num, ← pow_add, ← pow_add]
        congr 1
        omega
      have hD : (Dlcm (6 * n) : ℚ) = (Dlcm m : ℚ) * (t : ℚ) := by
        exact_mod_cast congrArg (fun s : ℕ => (s : ℚ)) ht
      push_cast
      rw [hsplit, hD]
      linear_combination ((-1 : ℚ) ^ m * 2 ^ (e - 3 - 4 * m) * (t : ℚ) ^ 2) * hz
    obtain ⟨z, hz⟩ := (mem_ZSub_iff _).1 (add_mem h1 h2)
    refine ⟨z, ?_⟩
    rw [hz, Y2row, Sfac, rivoal_numerator m]
    push_cast
    ring

end Catalan
