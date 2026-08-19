import RequestProject.PadeNumerator
import RequestProject.ZIntegrality
import RequestProject.EDenominator
import RequestProject.EIntegralityB
import RequestProject.Beukers

/-!
# Integrality of the diagonal Padé numerator: `2^{4m} D_m² p_m(x_m) ∈ ℤ`

This is the arithmetic input still missing for the Zudilin second row (`Y₂`).  Combining

* the closed form `p_n(x) = -∑_{k≤n} C(n,k) (β_k(y)/(k!)²) h_k(x)` of `PadeNumerator.lean`,
  where `h_k(x) = ∑_{j<k} [j/x][j/(1-x)]`, and
* the evaluation of `β_k` and of the bracket products at the moving point `x_m = 1/2 - m`,

each term of the resulting double sum is, up to sign,

`C(m,k) · (j!)² · U₁ · U₂ / (4^L (k!)²)`,   `L = k - j - 1`,

with `U₁ = (2m-2k+1)(2m-2k+3)⋯(2m-2j-3)` and `U₂ = (2m+2j+3)⋯(2m+2k-1)` two runs of `L`
consecutive odd numbers (the middle block of the run cancels against the bracket denominators).

The arithmetic statement `pade_term_dvd` is then proved prime by prime.

*Odd `p`.*  Legendre's bound along an arithmetic progression (`APValuation.lean`) gives
`v_p(L!) ≤ v_p(U₁)` and `v_p(L!) ≤ v_p(U₂)`, so it suffices that

`v_p(k!) ≤ v_p(j!) + v_p(L!) + v_p(D_m)`,

and since `k = j + L + 1` one has `k! = j! · L! · (k · C(j+L, j))`, so this is exactly the
Nair-type bound `v_p(k · C(k-1,j)) ≤ log_p k`, proved here from Kummer's carry description of
`v_p` of a binomial coefficient: if `p^i ∣ k = j + L + 1`, then `j mod p^i + L mod p^i = p^i - 1`,
so no carry occurs at any level `i ≤ v_p(k)`.

*`p = 2`.*  Both runs are odd, and `2 v₂(k!) + 2L ≤ 4(k-1) ≤ 4m`.
-/

namespace Catalan

open Finset

/-! ### A Nair-type bound -/

/-- Splitting a run of odd numbers. -/
lemma oddRun_add (c a b : ℕ) : oddRun c (a + b) = oddRun c a * oddRun (c + 2 * a) b := by
  unfold oddRun
  rw [Finset.prod_range_add]
  refine congrArg _ (Finset.prod_congr rfl (fun j _ => by ring))

/-- `k! = j! · L! · (k · C(j+L, j))` for `k = j + L + 1`. -/
lemma factorial_succ_add_eq (j L : ℕ) :
    (j + L + 1).factorial = j.factorial * L.factorial * ((j + L + 1) * (j + L).choose j) := by
  have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_right j L)
  simp only [Nat.add_sub_cancel_left] at h
  rw [Nat.factorial_succ]
  rw [← h]
  ring

/-- The Nair-type bound: `v_p(k · C(k-1, j)) ≤ log_p k` for `k = j + L + 1`. -/
lemma factorization_mul_choose_le_log {p : ℕ} (hp : p.Prime) (j L : ℕ) :
    ((j + L + 1) * (j + L).choose j).factorization p ≤ Nat.log p (j + L + 1) := by
  classical
  set v := (j + L + 1).factorization p with hv
  set b := Nat.log p (j + L + 1) + 1 with hb
  have hchne : (j + L).choose j ≠ 0 := (Nat.choose_pos (Nat.le_add_right j L)).ne'
  have hfac : ((j + L + 1) * (j + L).choose j).factorization p
      = v + ((j + L).choose j).factorization p := by
    rw [Nat.factorization_mul (by omega) hchne]
    simp [hv]
  have hlog : Nat.log p (j + L) < b := by
    have := Nat.log_mono_right (b := p) (show j + L ≤ j + L + 1 by omega)
    omega
  have hch := Nat.factorization_choose hp (Nat.le_add_right j L) hlog
  rw [Nat.add_sub_cancel_left] at hch
  have hvle : v ≤ Nat.log p (j + L + 1) :=
    Nat.le_log_of_pow_le hp.one_lt (Nat.le_of_dvd (by omega) (Nat.ordProj_dvd _ p))
  have hsub : {i ∈ Finset.Ico 1 b | p ^ i ≤ j % p ^ i + L % p ^ i} ⊆ Finset.Ico (v + 1) b := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_Ico] at hi ⊢
    obtain ⟨⟨hi1, hi2⟩, hcond⟩ := hi
    refine ⟨?_, hi2⟩
    by_contra hcon
    push_neg at hcon
    have hile : i ≤ v := by omega
    have hdvd : p ^ i ∣ (j + L + 1) := dvd_trans (pow_dvd_pow p hile) (Nat.ordProj_dvd _ p)
    set q := p ^ i with hq
    have hq1 : 1 < q := by
      calc 1 < p ^ 1 := by simpa using hp.one_lt
        _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos hi1
    have hjq : j % q < q := Nat.mod_lt _ (by omega)
    have hLq : L % q < q := Nat.mod_lt _ (by omega)
    have hmod0 : (j + L + 1) % q = 0 := Nat.mod_eq_zero_of_dvd hdvd
    have h1 : (j + L + 1) % q = ((j + L) % q + 1) % q := by
      conv_lhs => rw [Nat.add_mod (j + L) 1 q, Nat.mod_eq_of_lt hq1]
    have hr : (j + L) % q < q := Nat.mod_lt _ (by omega)
    have hjl : (j + L) % q = q - 1 := by
      rcases Nat.lt_or_ge ((j + L) % q + 1) q with h | h
      · rw [Nat.mod_eq_of_lt h] at h1; omega
      · omega
    have hsum : (j % q + L % q) % q = (j + L) % q := (Nat.add_mod j L q).symm
    have hcase : (j % q + L % q) % q = j % q + L % q - q := by
      rw [Nat.mod_eq_sub_mod hcond, Nat.mod_eq_of_lt (by omega)]
    omega
  calc ((j + L + 1) * (j + L).choose j).factorization p
      = v + ({i ∈ Finset.Ico 1 b | p ^ i ≤ j % p ^ i + L % p ^ i}).card := by rw [hfac, hch]
    _ ≤ v + (Finset.Ico (v + 1) b).card := Nat.add_le_add_left (Finset.card_le_card hsub) v
    _ ≤ Nat.log p (j + L + 1) := by rw [Nat.card_Ico]; omega

/-- The consequence used below: `v_p(k!) ≤ v_p(j!) + v_p(L!) + log_p k`, `k = j + L + 1`. -/
lemma factorization_factorial_split_le {p : ℕ} (hp : p.Prime) (j L : ℕ) :
    ((j + L + 1).factorial).factorization p
      ≤ (j.factorial).factorization p + (L.factorial).factorization p
        + Nat.log p (j + L + 1) := by
  have hne1 : j.factorial * L.factorial ≠ 0 := by positivity
  have hne2 : (j + L + 1) * (j + L).choose j ≠ 0 := by
    have := (Nat.choose_pos (Nat.le_add_right j L)).ne'
    positivity
  rw [factorial_succ_add_eq j L, Nat.factorization_mul hne1 hne2,
    Nat.factorization_mul (Nat.factorial_ne_zero j) (Nat.factorial_ne_zero L)]
  simp only [Finsupp.coe_add, Pi.add_apply]
  exact Nat.add_le_add_left (factorization_mul_choose_le_log hp j L) _

/-! ### The arithmetic estimate -/

/-- The arithmetic estimate behind the integrality of the diagonal Padé numerator:
with `k = j + L + 1` and `m = k + d`,

`(k!)² 4^L ∣ 2^{4m} D_m² (j!)² · U₁ · U₂`,

where `U₁, U₂` are the two runs of `L` odd numbers occurring in the closed form. -/
theorem pade_term_dvd (j L d : ℕ) :
    ((j + L + 1).factorial) ^ 2 * 4 ^ L ∣
      2 ^ (4 * (j + L + 1 + d)) * (Dlcm (j + L + 1 + d)) ^ 2 * (j.factorial) ^ 2
        * oddRun (2 * d + 1) L * oddRun (2 * (j + L + 1 + d) + 2 * j + 3) L := by
  set m := j + L + 1 + d with hm
  set k := j + L + 1 with hk
  set A := oddRun (2 * d + 1) L with hA
  set B := oddRun (2 * m + 2 * j + 3) L with hB
  have hApos : 0 < A := oddRun_pos _ _ (by omega)
  have hBpos : 0 < B := oddRun_pos _ _ (by omega)
  have hDpos : 0 < Dlcm m := Nat.pos_of_ne_zero (Dlcm_ne_zero m)
  have hfour : (4 : ℕ) ^ L = 2 ^ (2 * L) := by
    rw [pow_mul]; norm_num
  have hLne : (k.factorial) ^ 2 * 4 ^ L ≠ 0 := by positivity
  have hRne : 2 ^ (4 * m) * (Dlcm m) ^ 2 * (j.factorial) ^ 2 * A * B ≠ 0 := by positivity
  rw [← Nat.factorization_le_iff_dvd hLne hRne, Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · have hLHS : ((k.factorial) ^ 2 * 4 ^ L).factorization p
        = 2 * (k.factorial).factorization p + 2 * L * (Nat.factorization 2 p) := by
      rw [hfour, Nat.factorization_mul (by positivity) (by positivity),
        Nat.factorization_pow, Nat.factorization_pow]
      simp [mul_comm]
    have hRHS : (2 ^ (4 * m) * (Dlcm m) ^ 2 * (j.factorial) ^ 2 * A * B).factorization p
        = 4 * m * (Nat.factorization 2 p) + 2 * (Dlcm m).factorization p
          + 2 * (j.factorial).factorization p + A.factorization p + B.factorization p := by
      rw [Nat.factorization_mul (by positivity) hBpos.ne',
        Nat.factorization_mul (by positivity) hApos.ne',
        Nat.factorization_mul (by positivity) (by positivity),
        Nat.factorization_mul (by positivity) (by positivity),
        Nat.factorization_pow, Nat.factorization_pow, Nat.factorization_pow]
      simp [mul_comm]
    rw [hLHS, hRHS]
    rcases eq_or_ne p 2 with rfl | hp2
    · have h2 : (Nat.factorization 2) 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
      have hv2 : (k.factorial).factorization 2 ≤ k := by
        have : padicValNat 2 (Nat.factorial k) ≤ k :=
          @padicValNat_factorial_le 2 ⟨Nat.prime_two⟩ k
        rwa [Nat.factorization_def _ Nat.prime_two]
      rw [h2]
      omega
    · have hzero : (Nat.factorization 2) p = 0 := by
        rw [Nat.Prime.factorization Nat.prime_two]
        simp [Ne.symm hp2]
      have hAle : (L.factorial).factorization p ≤ A.factorization p :=
        factorization_factorial_le_prod_ap hp hp2 (2 * d + 1) L (by omega)
      have hBle : (L.factorial).factorization p ≤ B.factorization p :=
        factorization_factorial_le_prod_ap hp hp2 (2 * m + 2 * j + 3) L (by omega)
      have hsplit := factorization_factorial_split_le hp j L
      rw [← hk] at hsplit
      have hlogD : Nat.log p k ≤ (Dlcm m).factorization p := by
        refine le_factorization_Dlcm hp ?_
        calc p ^ Nat.log p k ≤ k := Nat.pow_log_le_self p (by omega)
          _ ≤ m := by omega
      rw [hzero]
      omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-! ### Evaluation of the closed form at the moving point -/

lemma betaCoef_xpt (m k : ℕ) (hk : k ≤ m) :
    betaCoef ((xpt m) ^ 2 - xpt m) k = (oddRun (2 * m - 2 * k + 1) (2 * k) : ℚ) / 4 ^ k := by
  have hprod : betaCoef ((xpt m) ^ 2 - xpt m) k
      = pdProd ((m : ℚ) - 1 / 2) k * puProd ((m : ℚ) + 1 / 2) k := by
    unfold betaCoef pdProd puProd xpt
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl (fun i _ => by ring)
  have h := four_pow_mul_halves m k hk
  have h4 : (4 : ℚ) ^ k ≠ 0 := by positivity
  rw [hprod, eq_div_iff h4]
  linarith [h]

/-- The bracket denominator at the moving point, cleared of its powers of two. -/
lemma two_pow_mul_brkDen_xpt (m j : ℕ) (hj : j < m) :
    (2 : ℚ) ^ (j + 1) * brkDen (xpt m) j
      = (-1 : ℚ) ^ (j + 1) * (oddRun (2 * m - 2 * j - 1) (j + 1) : ℚ) := by
  have h2 : (2 : ℚ) ^ (j + 1) = ∏ _i ∈ range (j + 1), (2 : ℚ) := by simp
  have hs : (-1 : ℚ) ^ (j + 1) = ∏ _i ∈ range (j + 1), (-1 : ℚ) := by simp
  rw [brkDen, h2, ← Finset.prod_mul_distrib, hs, oddRun, Nat.cast_prod,
    ← Finset.prod_mul_distrib,
    ← Finset.prod_range_reflect (fun i => ((-1 : ℚ) * ((2 * m - 2 * j - 1 + 2 * i : ℕ) : ℚ)))
      (j + 1)]
  refine Finset.prod_congr rfl (fun i hi => ?_)
  simp only [Finset.mem_range] at hi
  have hnat : 2 * m - 2 * j - 1 + 2 * (j + 1 - 1 - i) = 2 * m - (1 + 2 * i) := by omega
  have hle : 1 + 2 * i ≤ 2 * m := by omega
  rw [hnat, Nat.cast_sub hle]
  unfold xpt
  push_cast
  ring

/-- The reflected bracket denominator at the moving point. -/
lemma two_pow_mul_brkDen_one_sub_xpt (m j : ℕ) :
    (2 : ℚ) ^ (j + 1) * brkDen (1 - xpt m) j = (oddRun (2 * m + 1) (j + 1) : ℚ) := by
  have h2 : (2 : ℚ) ^ (j + 1) = ∏ _i ∈ range (j + 1), (2 : ℚ) := by simp
  rw [brkDen, h2, ← Finset.prod_mul_distrib, oddRun, Nat.cast_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  unfold xpt
  push_cast
  ring

lemma xiTerm_xpt (m j : ℕ) (hj : j < m) :
    xiTerm (xpt m) j =
      (-1 : ℚ) ^ (j + 1) * 4 ^ (j + 1) * (j.factorial : ℚ) ^ 2
        / (oddRun (2 * m - 2 * j - 1) (2 * j + 2) : ℚ) := by
  have hsplit : oddRun (2 * m - 2 * j - 1) (2 * j + 2)
      = oddRun (2 * m - 2 * j - 1) (j + 1) * oddRun (2 * m + 1) (j + 1) := by
    have h := oddRun_add (2 * m - 2 * j - 1) (j + 1) (j + 1)
    have hc : 2 * m - 2 * j - 1 + 2 * (j + 1) = 2 * m + 1 := by omega
    rw [hc] at h
    rw [show 2 * j + 2 = (j + 1) + (j + 1) by ring]
    exact h
  have h1 := two_pow_mul_brkDen_xpt m j hj
  have h2 := two_pow_mul_brkDen_one_sub_xpt m j
  have hd1 : brkDen (xpt m) j ≠ 0 := brkDen_ne_zero (halfOdd_xpt m) j
  have hd2 : brkDen (1 - xpt m) j ≠ 0 := brkDen_ne_zero (halfOdd_xpt m).one_sub j
  have hpos1 : (0 : ℚ) < (oddRun (2 * m - 2 * j - 1) (j + 1) : ℚ) := by
    exact_mod_cast oddRun_pos _ _ (by omega)
  have hpos2 : (0 : ℚ) < (oddRun (2 * m + 1) (j + 1) : ℚ) := by
    exact_mod_cast oddRun_pos _ _ (by omega)
  have hsign : ((-1 : ℚ) ^ (j + 1)) * ((-1 : ℚ) ^ (j + 1)) = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨j + 1, by ring⟩
  unfold xiTerm brk
  rw [hsplit, div_mul_div_comm]
  push_cast
  rw [div_eq_div_iff (by positivity) (by positivity)]
  have hden : (brkDen (xpt m) j * brkDen (1 - xpt m) j) * (4 : ℚ) ^ (j + 1)
      = (-1 : ℚ) ^ (j + 1) * ((oddRun (2 * m - 2 * j - 1) (j + 1) : ℚ)
        * (oddRun (2 * m + 1) (j + 1) : ℚ)) := by
    have h4 : (4 : ℚ) ^ (j + 1) = 2 ^ (j + 1) * 2 ^ (j + 1) := by
      rw [← mul_pow]; norm_num
    calc (brkDen (xpt m) j * brkDen (1 - xpt m) j) * (4 : ℚ) ^ (j + 1)
        = ((2 : ℚ) ^ (j + 1) * brkDen (xpt m) j) * ((2 : ℚ) ^ (j + 1) * brkDen (1 - xpt m) j) := by
          rw [h4]; ring
      _ = (-1 : ℚ) ^ (j + 1) * ((oddRun (2 * m - 2 * j - 1) (j + 1) : ℚ)
            * (oddRun (2 * m + 1) (j + 1) : ℚ)) := by rw [h1, h2]; ring
  linear_combination (-(-1 : ℚ) ^ (j + 1) * (j.factorial : ℚ) ^ 2) * hden
    + (-(j.factorial : ℚ) ^ 2 * ((oddRun (2 * m - 2 * j - 1) (j + 1) : ℚ)
        * (oddRun (2 * m + 1) (j + 1) : ℚ))) * hsign

/-- A single term of the double sum, cleared by `2^{4m} D_m²`, is an integer. -/
theorem pade_term_isInt (m k j : ℕ) (hj : j < k) (hk : k ≤ m) :
    ∃ z : ℤ, (z : ℚ) = 2 ^ (4 * m) * (Dlcm m : ℚ) ^ 2 *
      ((m.choose k : ℚ) * (gCoef ((xpt m) ^ 2 - xpt m) k * xiTerm (xpt m) j)) := by
  obtain ⟨L, rfl⟩ : ∃ L, k = j + L + 1 := ⟨k - j - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, m = j + L + 1 + d := ⟨m - (j + L + 1), by omega⟩
  set m := j + L + 1 + d with hm
  set k := j + L + 1 with hk
  set A := oddRun (2 * d + 1) L with hA
  set B := oddRun (2 * m + 2 * j + 3) L with hB
  set M := oddRun (2 * m - 2 * j - 1) (2 * j + 2) with hM
  have hsplit : oddRun (2 * m - 2 * k + 1) (2 * k) = A * M * B := by
    have e0 : 2 * m - 2 * k + 1 = 2 * d + 1 := by omega
    have e1 : 2 * d + 1 + 2 * L = 2 * m - 2 * j - 1 := by omega
    have e2 : 2 * m - 2 * j - 1 + 2 * (2 * j + 2) = 2 * m + 2 * j + 3 := by omega
    have e3 : 2 * k = L + ((2 * j + 2) + L) := by omega
    rw [e0, e3, oddRun_add, e1, oddRun_add, e2, hA, hB, hM, mul_assoc]
  have hMpos : (0 : ℚ) < (M : ℚ) := by
    rw [hM]; exact_mod_cast oddRun_pos _ _ (by omega)
  have hfpos : (0 : ℚ) < (k.factorial : ℚ) := by exact_mod_cast Nat.factorial_pos k
  obtain ⟨c, hc⟩ := pade_term_dvd j L d
  have hcQ : (2 : ℚ) ^ (4 * m) * (Dlcm m : ℚ) ^ 2 * (j.factorial : ℚ) ^ 2 * (A : ℚ) * (B : ℚ)
      = ((k.factorial : ℚ) ^ 2 * 4 ^ L) * (c : ℚ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℚ)) hc
  have h4 : (4 : ℚ) ^ k = 4 ^ L * 4 ^ (j + 1) := by
    rw [← pow_add]
    congr 1
    omega
  have hkm : k ≤ m := by omega
  have hjm : j < m := by omega
  clear_value m k A B M
  have key : gCoef ((xpt m) ^ 2 - xpt m) k * xiTerm (xpt m) j
      = (-1 : ℚ) ^ (j + 1) * ((A : ℚ) * (B : ℚ) * (j.factorial : ℚ) ^ 2)
        / (4 ^ L * (k.factorial : ℚ) ^ 2) := by
    rw [gCoef, betaCoef_xpt m k hkm, xiTerm_xpt m j hjm, hsplit, ← hM]
    push_cast
    rw [h4]
    field_simp
  refine ⟨(-1) ^ (j + 1) * (m.choose k : ℤ) * (c : ℤ), ?_⟩
  rw [key]
  have hne : ((4 : ℚ) ^ L * (k.factorial : ℚ) ^ 2) ≠ 0 := by positivity
  push_cast
  field_simp
  linear_combination (-(m.choose k : ℚ)) * hcQ

/-! ### Integrality of the diagonal Padé numerator -/

/-- **`2^{4m} D_m² p_m(x_m) ∈ ℤ`.** -/
theorem two_pow_mul_Dlcm_sq_mul_bp_isInt (m : ℕ) :
    ∃ z : ℤ, (z : ℚ) = 2 ^ (4 * m) * (Dlcm m : ℚ) ^ 2 * bp (xpt m) m := by
  classical
  have hbp : bp (xpt m) m = -∑ k ∈ range (m + 1), ∑ j ∈ range k,
      (m.choose k : ℚ) * (gCoef ((xpt m) ^ 2 - xpt m) k * xiTerm (xpt m) j) := by
    rw [bp_eq_pSum (halfOdd_xpt m) m, pSum, pPart]
    refine congrArg Neg.neg (Finset.sum_congr rfl (fun k _ => ?_))
    rw [pWeight, xiPart, Finset.mul_sum, Finset.mul_sum]
  have hmem : ∑ k ∈ range (m + 1), ∑ j ∈ range k,
      2 ^ (4 * m) * (Dlcm m : ℚ) ^ 2 *
        ((m.choose k : ℚ) * (gCoef ((xpt m) ^ 2 - xpt m) k * xiTerm (xpt m) j)) ∈ ZSub := by
    refine Subring.sum_mem _ (fun k hk => Subring.sum_mem _ (fun j hj => ?_))
    simp only [Finset.mem_range] at hk hj
    obtain ⟨z, hz⟩ := pade_term_isInt m k j hj (by omega)
    exact (mem_ZSub_iff _).2 ⟨z, hz⟩
  have hval : 2 ^ (4 * m) * (Dlcm m : ℚ) ^ 2 * bp (xpt m) m
      = -∑ k ∈ range (m + 1), ∑ j ∈ range k,
        2 ^ (4 * m) * (Dlcm m : ℚ) ^ 2 *
          ((m.choose k : ℚ) * (gCoef ((xpt m) ^ 2 - xpt m) k * xiTerm (xpt m) j)) := by
    rw [hbp, mul_neg, Finset.mul_sum]
    refine congrArg Neg.neg (Finset.sum_congr rfl (fun k _ => ?_))
    rw [Finset.mul_sum]
  rw [hval]
  obtain ⟨z, hz⟩ := (mem_ZSub_iff _).1 (neg_mem hmem)
  exact ⟨z, hz⟩

end Catalan
