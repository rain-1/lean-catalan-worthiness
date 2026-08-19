import RequestProject.ClosedForm
import RequestProject.Zudilin

/-!
# Rivoal's identification of the Zudilin denominators

Equation (4.7) of the note states `q_m(x_m) = Q_m`, where `q_n` is Beukers' Padé denominator,
`x_m = 1/2 - m` is the moving half-integer point, and `Q_m` is Zudilin's denominator sequence.
In the note this is quoted from Rivoal's Theorem 2; here it is *proved*, directly from the two
recurrences.

The argument has three steps.

* `ClosedForm.lean` gives the closed form `q_n(x) = ∑_{k≤n} C(n,k) β_k(y)/(k!)²`, `y = x² - x`.
* At `x = x_m` one has `y = m² - 1/4`, and the closed form becomes the *diagonal* sum
  `D_m = ∑_{k≤m} T(m,k)`, `T(m,k) = ∏_{j<k}(m-j)(m-1/2-j)(m+1/2+j)/(k!)³`.
* `dZsum_rec`: `D` satisfies Zudilin's three-term recurrence.  This is a creative-telescoping
  (Zeilberger) computation: the certificate is the explicit polynomial `vPoly`, and the whole
  verification reduces to one polynomial identity in `(m,k)`, closed by `ring`.

Since `D_0 = Q_0 = 1` and `D_1 = Q_1 = 7/4`, uniqueness of solutions of the recurrence gives
`D_m = Q_m`, i.e. `bq_xpt_eq_Qz : bq (xpt m) m = Qz m`.
-/

namespace Catalan

open Finset

/-! ### Falling and rising products -/

/-- `∏_{j<k} (a - j)`. -/
def pdProd (a : ℚ) (k : ℕ) : ℚ := ∏ j ∈ range k, (a - (j : ℚ))

/-- `∏_{j<k} (a + j)`. -/
def puProd (a : ℚ) (k : ℕ) : ℚ := ∏ j ∈ range k, (a + (j : ℚ))

@[simp] lemma pdProd_zero (a : ℚ) : pdProd a 0 = 1 := by simp [pdProd]

@[simp] lemma puProd_zero (a : ℚ) : puProd a 0 = 1 := by simp [puProd]

lemma pdProd_succ (a : ℚ) (k : ℕ) : pdProd a (k + 1) = pdProd a k * (a - (k : ℚ)) :=
  prod_range_succ _ _

lemma puProd_succ (a : ℚ) (k : ℕ) : puProd a (k + 1) = puProd a k * (a + (k : ℚ)) :=
  prod_range_succ _ _

/-- Peeling the *first* factor of a falling product. -/
lemma pdProd_succ_left (a : ℚ) (k : ℕ) : pdProd (a + 1) (k + 1) = (a + 1) * pdProd a k := by
  unfold pdProd
  rw [prod_range_succ' (fun j => (a + 1 - (j : ℚ))) k]
  have : ∀ j ∈ range k, (a + 1 - ((j + 1 : ℕ) : ℚ)) = a - (j : ℚ) := by
    intro j _; push_cast; ring
  rw [prod_congr rfl this]
  push_cast
  ring

/-- Shifting a rising product. -/
lemma puProd_shift (a : ℚ) (k : ℕ) : a * puProd (a + 1) k = (a + (k : ℚ)) * puProd a k := by
  induction k with
  | zero => simp
  | succ i ih =>
      rw [puProd_succ, puProd_succ]
      push_cast
      calc a * (puProd (a + 1) i * (a + 1 + (i : ℚ)))
          = (a * puProd (a + 1) i) * (a + 1 + (i : ℚ)) := by ring
        _ = ((a + (i : ℚ)) * puProd a i) * (a + 1 + (i : ℚ)) := by rw [ih]
        _ = (a + ((i : ℚ) + 1)) * (puProd a i * (a + (i : ℚ))) := by ring

/-- Shifting a falling product. -/
lemma pdProd_shift (a : ℚ) (k : ℕ) : a * pdProd (a - 1) k = pdProd a k * (a - (k : ℚ)) := by
  have h2 : pdProd a (k + 1) = a * pdProd (a - 1) k := by
    have := pdProd_succ_left (a - 1) k
    simpa using this
  rw [← h2, pdProd_succ]

/-! ### The diagonal summand -/

/-- `T(m,k) = ∏_{j<k}(m-j)(m-1/2-j)(m+1/2+j)/(k!)³`. -/
def tZ (m : ℚ) (k : ℕ) : ℚ :=
  pdProd m k * pdProd (m - 1 / 2) k * puProd (m + 1 / 2) k / (k.factorial : ℚ) ^ 3

@[simp] lemma tZ_zero (m : ℚ) : tZ m 0 = 1 := by simp [tZ]

lemma tZ_mul (m : ℚ) (k : ℕ) :
    ((k.factorial : ℚ)) ^ 3 * tZ m k
      = pdProd m k * pdProd (m - 1 / 2) k * puProd (m + 1 / 2) k := by
  have hk := factorial_ne_zero_rat k
  unfold tZ
  field_simp

lemma factorial_succ_cube (k : ℕ) :
    (((k + 1).factorial : ℚ)) ^ 3 = ((k : ℚ) + 1) ^ 3 * ((k.factorial : ℚ)) ^ 3 := by
  rw [Nat.factorial_succ]
  push_cast
  ring

lemma tZ_succ (m : ℚ) (k : ℕ) :
    ((k : ℚ) + 1) ^ 3 * tZ m (k + 1)
      = (m - (k : ℚ)) * (m - 1 / 2 - (k : ℚ)) * (m + 1 / 2 + (k : ℚ)) * tZ m k := by
  have hk := factorial_ne_zero_rat k
  unfold tZ
  rw [pdProd_succ, pdProd_succ, puProd_succ, Nat.factorial_succ]
  push_cast
  field_simp

lemma tZ_up (m : ℚ) (hm : m + 1 / 2 ≠ 0) (k : ℕ) :
    ((k : ℚ) + 1) ^ 3 * tZ (m + 1) (k + 1)
      = (m + 1) * (m + (k : ℚ) + 1 / 2) * (m + (k : ℚ) + 3 / 2) * tZ m k := by
  have hk := factorial_ne_zero_rat k
  have hf : ((k.factorial : ℚ)) ^ 3 ≠ 0 := pow_ne_zero _ hk
  have e1 : m + 1 - 1 / 2 = m + 1 / 2 := by ring
  have e2 : m + 1 + 1 / 2 = m + 3 / 2 := by ring
  have h1 : pdProd (m + 1) (k + 1) = (m + 1) * pdProd m k := pdProd_succ_left m k
  have h2 : pdProd (m + 1 / 2) (k + 1) = (m + 1 / 2) * pdProd (m - 1 / 2) k := by
    have h := pdProd_succ_left (m - 1 / 2) k
    rw [show m - 1 / 2 + 1 = m + 1 / 2 from by ring] at h
    exact h
  have h3 : (m + 1 / 2) * puProd (m + 3 / 2) (k + 1)
      = (m + (k : ℚ) + 3 / 2) * (puProd (m + 1 / 2) k * (m + 1 / 2 + (k : ℚ))) := by
    have h := puProd_shift (m + 1 / 2) (k + 1)
    rw [show m + 1 / 2 + 1 = m + 3 / 2 from by ring] at h
    rw [h, puProd_succ]
    push_cast
    ring
  have hnum : pdProd (m + 1) (k + 1) * pdProd (m + 1 / 2) (k + 1) * puProd (m + 3 / 2) (k + 1)
      = (m + 1) * (m + (k : ℚ) + 1 / 2) * (m + (k : ℚ) + 3 / 2)
        * (pdProd m k * pdProd (m - 1 / 2) k * puProd (m + 1 / 2) k) := by
    refine mul_left_cancel₀ hm ?_
    rw [h1, h2]
    linear_combination ((m + 1) * pdProd m k * ((m + 1 / 2) * pdProd (m - 1 / 2) k)) * h3
  have hL := tZ_mul (m + 1) (k + 1)
  rw [e1, e2] at hL
  have hR := tZ_mul m k
  have hfac := factorial_succ_cube k
  refine mul_left_cancel₀ hf ?_
  linear_combination hL + hnum - (tZ (m + 1) (k + 1)) * hfac
    - ((m + 1) * (m + (k : ℚ) + 1 / 2) * (m + (k : ℚ) + 3 / 2)) * hR

lemma tZ_down (m : ℚ) (hm : m - 1 / 2 ≠ 0) (k : ℕ) :
    m * (m + (k : ℚ) - 1 / 2) * tZ (m - 1) k
      = (m - (k : ℚ)) * (m - (k : ℚ) - 1 / 2) * tZ m k := by
  have hk := factorial_ne_zero_rat k
  have hf : ((k.factorial : ℚ)) ^ 3 ≠ 0 := pow_ne_zero _ hk
  have g1 : m * pdProd (m - 1) k = pdProd m k * (m - (k : ℚ)) := pdProd_shift m k
  have g2 : (m - 1 / 2) * pdProd (m - 3 / 2) k
      = pdProd (m - 1 / 2) k * (m - 1 / 2 - (k : ℚ)) := by
    have h := pdProd_shift (m - 1 / 2) k
    rw [show m - 1 / 2 - 1 = m - 3 / 2 from by ring] at h
    exact h
  have g3 : (m - 1 / 2) * puProd (m + 1 / 2) k
      = (m - 1 / 2 + (k : ℚ)) * puProd (m - 1 / 2) k := by
    have h := puProd_shift (m - 1 / 2) k
    rw [show m - 1 / 2 + 1 = m + 1 / 2 from by ring] at h
    exact h
  have hnum : m * (m + (k : ℚ) - 1 / 2)
        * (pdProd (m - 1) k * pdProd (m - 3 / 2) k * puProd (m - 1 / 2) k)
      = (m - (k : ℚ)) * (m - (k : ℚ) - 1 / 2)
        * (pdProd m k * pdProd (m - 1 / 2) k * puProd (m + 1 / 2) k) := by
    refine mul_left_cancel₀ hm ?_
    linear_combination
      ((m + (k : ℚ) - 1 / 2) * ((m - 1 / 2) * pdProd (m - 3 / 2) k) * puProd (m - 1 / 2) k) * g1
      + ((m + (k : ℚ) - 1 / 2) * (pdProd m k * (m - (k : ℚ))) * puProd (m - 1 / 2) k) * g2
      - ((m - (k : ℚ)) * (m - (k : ℚ) - 1 / 2) * (pdProd m k * pdProd (m - 1 / 2) k)) * g3
  have hL := tZ_mul (m - 1) k
  rw [show m - 1 - 1 / 2 = m - 3 / 2 from by ring,
    show m - 1 + 1 / 2 = m - 1 / 2 from by ring] at hL
  have hR := tZ_mul m k
  refine mul_left_cancel₀ hf ?_
  linear_combination (m * (m + (k : ℚ) - 1 / 2)) * hL
    - ((m - (k : ℚ)) * (m - (k : ℚ) - 1 / 2)) * hR + hnum

/-! ### The Zeilberger certificate -/

/-- The leading coefficient of Zudilin's recurrence, as a polynomial over `ℚ`. -/
def lzQ (m : ℚ) : ℚ := (2 * m + 1) ^ 2 * (2 * m + 2) ^ 2 * (20 * m ^ 2 - 8 * m + 1)

/-- The middle coefficient of Zudilin's recurrence, as a polynomial over `ℚ`. -/
def czQ (m : ℚ) : ℚ :=
  3520 * m ^ 6 + 5632 * m ^ 5 + 2064 * m ^ 4 - 384 * m ^ 3 - 156 * m ^ 2 + 16 * m + 7

/-- The trailing coefficient of Zudilin's recurrence, as a polynomial over `ℚ`. -/
def rzQ (m : ℚ) : ℚ :=
  (2 * m - 1) ^ 2 * (2 * m) ^ 2 * (20 * (m + 1) ^ 2 - 8 * (m + 1) + 1)

lemma lzQ_cast (m : ℕ) : ((LZ m : ℤ) : ℚ) = lzQ (m : ℚ) := by
  unfold LZ phiZ lzQ; push_cast; ring

lemma czQ_cast (m : ℕ) : ((CZ m : ℤ) : ℚ) = czQ (m : ℚ) := by
  unfold CZ czQ; push_cast; ring

lemma rzQ_cast (m : ℕ) : ((RZ m : ℤ) : ℚ) = rzQ (m : ℚ) := by
  unfold RZ phiZ rzQ; push_cast; ring

/-- The Zeilberger certificate polynomial. -/
def vPoly (m k : ℚ) : ℚ :=
  (116 - 336 * k + 208 * k ^ 2) + m * (-320 + 544 * k - 320 * k ^ 2)
    + m ^ 2 * (1072 - 896 * k ^ 2) + m ^ 3 * (1024 + 512 * k + 768 * k ^ 2)
    + m ^ 4 * (-14400 + 8448 * k + 1280 * k ^ 2) + m ^ 5 * (-27648 + 7680 * k)
    - 14080 * m ^ 6

/-- The telescoping function `G(m,k)`. -/
def gCert (m : ℚ) : ℕ → ℚ
  | 0 => 0
  | (k + 1) => vPoly m ((k : ℚ) + 1) * tZ m k / 4

/-- The core polynomial identity behind the creative telescoping. -/
lemma vPoly_key (m k : ℚ) :
    4 * m * ((m + 1) * (m + k - 1 / 2) * (m + k + 1 / 2) * lzQ m
        - czQ m * (m - k + 1) * (m - k + 1 / 2) * (m + k - 1 / 2))
      - 4 * rzQ m * (m - k) * (m - k - 1 / 2) * (m - k + 1) * (m - k + 1 / 2)
      = m * (vPoly m (k + 1) * (m - k + 1) * (m - k + 1 / 2) * (m + k - 1 / 2)
        - vPoly m k * k ^ 3) := by
  unfold vPoly lzQ czQ rzQ
  ring

/-- The `k = 0` case of the certificate identity. -/
lemma vPoly_zero (m : ℚ) : 4 * (lzQ m - czQ m - rzQ m) = vPoly m 1 := by
  unfold vPoly lzQ czQ rzQ
  ring

/-- The termwise creative-telescoping identity. -/
lemma zud_term (m : ℚ) (hm0 : m ≠ 0) (hmp : m + 1 / 2 ≠ 0) (hmm : m - 1 / 2 ≠ 0)
    (hs : ∀ k : ℕ, m + (k : ℚ) + 1 / 2 ≠ 0) (k : ℕ) :
    lzQ m * tZ (m + 1) k - czQ m * tZ m k - rzQ m * tZ (m - 1) k
      = gCert m (k + 1) - gCert m k := by
  match k with
  | 0 =>
      have h := vPoly_zero m
      simp only [gCert, tZ_zero, Nat.cast_zero, zero_add]
      linarith [h]
  | (i + 1) =>
      have hi : ((i : ℚ) + 1) ≠ 0 := by positivity
      have hik : m + (i : ℚ) + 1 / 2 ≠ 0 := hs i
      have hA := tZ_up m hmp i
      have hB := tZ_succ m i
      have hC := tZ_down m hmm (i + 1)
      have hkey := vPoly_key m ((i : ℚ) + 1)
      push_cast at hC
      simp only [gCert]
      push_cast
      have hD : (4 : ℚ) * ((i : ℚ) + 1) ^ 3 * m * (m + (i : ℚ) + 1 / 2) ≠ 0 := by
        refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ hi)) hm0) hik
      refine mul_left_cancel₀ hD ?_
      linear_combination
        (4 * m * (m + (i : ℚ) + 1 / 2) * lzQ m) * hA
        + (-(4 * m * (m + (i : ℚ) + 1 / 2) * czQ m) - m * (m + (i : ℚ) + 1 / 2)
            * vPoly m ((i : ℚ) + 1 + 1) - 4 * rzQ m * (m - ((i : ℚ) + 1))
            * (m - ((i : ℚ) + 1) - 1 / 2)) * hB
        + (-(4 * rzQ m * ((i : ℚ) + 1) ^ 3)) * hC
        + (tZ m i * (m + (i : ℚ) + 1 / 2)) * hkey

/-! ### The diagonal sum and Zudilin's recurrence -/

/-- The diagonal sum `D_m = ∑_{k≤m} T(m,k)`. -/
def dZsum (n : ℕ) : ℚ := ∑ k ∈ range (n + 1), tZ (n : ℚ) k

lemma tZ_natCast_eq_zero {n k : ℕ} (h : n < k) : tZ (n : ℚ) k = 0 := by
  have hp : pdProd (n : ℚ) k = 0 := by
    unfold pdProd
    refine Finset.prod_eq_zero (i := n) (by simpa using h) ?_
    ring
  unfold tZ
  rw [hp]
  simp

lemma dZsum_eq_sum (n N : ℕ) (h : n + 1 ≤ N) : dZsum n = ∑ k ∈ range N, tZ (n : ℚ) k := by
  unfold dZsum
  refine Finset.sum_subset (by simpa using h) ?_
  intro k _ hk
  exact tZ_natCast_eq_zero (by simpa using hk)

/-- Zudilin's three-term recurrence for the diagonal sum. -/
lemma dZsum_rec (i : ℕ) :
    lzQ ((i : ℚ) + 1) * dZsum (i + 2)
      = czQ ((i : ℚ) + 1) * dZsum (i + 1) + rzQ ((i : ℚ) + 1) * dZsum i := by
  set m : ℚ := (i : ℚ) + 1 with hm
  have hm0 : m ≠ 0 := by rw [hm]; positivity
  have hmp : m + 1 / 2 ≠ 0 := by rw [hm]; positivity
  have hmm : m - 1 / 2 ≠ 0 := by
    have hi : (0 : ℚ) ≤ (i : ℚ) := Nat.cast_nonneg i
    rw [hm]
    intro hc
    linarith
  have hs : ∀ k : ℕ, m + (k : ℚ) + 1 / 2 ≠ 0 := by
    intro k
    rw [hm]
    positivity
  have hsum : ∑ k ∈ range (i + 3),
      (lzQ m * tZ (m + 1) k - czQ m * tZ m k - rzQ m * tZ (m - 1) k)
      = gCert m (i + 3) - gCert m 0 := by
    rw [Finset.sum_congr rfl (fun k _ => zud_term m hm0 hmp hmm hs k)]
    exact Finset.sum_range_sub (gCert m) (i + 3)
  have hg : gCert m (i + 3) = 0 := by
    have : tZ m (i + 2) = 0 := by
      have h := tZ_natCast_eq_zero (n := i + 1) (k := i + 2) (by omega)
      rw [show ((i + 1 : ℕ) : ℚ) = m from by rw [hm]; push_cast; ring] at h
      exact h
    simp [gCert, this]
  rw [hg, show gCert m 0 = 0 from rfl] at hsum
  have e1 : ∑ k ∈ range (i + 3), tZ (m + 1) k = dZsum (i + 2) := by
    rw [dZsum_eq_sum (i + 2) (i + 3) (by omega)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show ((i + 2 : ℕ) : ℚ) = m + 1 from by rw [hm]; push_cast; ring]
  have e2 : ∑ k ∈ range (i + 3), tZ m k = dZsum (i + 1) := by
    rw [dZsum_eq_sum (i + 1) (i + 3) (by omega)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show ((i + 1 : ℕ) : ℚ) = m from by rw [hm]; push_cast; ring]
  have e3 : ∑ k ∈ range (i + 3), tZ (m - 1) k = dZsum i := by
    rw [dZsum_eq_sum i (i + 3) (by omega)]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show ((i : ℕ) : ℚ) = m - 1 from by rw [hm]; ring]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, e1, e2, e3] at hsum
  linarith [hsum]

@[simp] lemma dZsum_zero : dZsum 0 = 1 := by
  simp [dZsum]

@[simp] lemma dZsum_one : dZsum 1 = 7 / 4 := by
  simp [dZsum, Finset.sum_range_succ, tZ, pdProd, puProd]
  norm_num

/-- The diagonal sum is Zudilin's denominator sequence. -/
theorem dZsum_eq_Qz (n : ℕ) : dZsum n = Qz n := by
  refine rec2_unique _ _ _ _ _ dZsum dZsum_zero dZsum_one
    (fun m => by exact_mod_cast (Int.cast_ne_zero (α := ℚ)).mpr (LZ_ne_zero (m + 1))) ?_ n
  intro m
  have h := dZsum_rec m
  rw [lzQ_cast (m + 1), czQ_cast (m + 1), rzQ_cast (m + 1)]
  push_cast
  linarith [h]

/-! ### Rivoal's identification -/

lemma pdProd_natCast (n k : ℕ) :
    pdProd (n : ℚ) k = (n.choose k : ℚ) * (k.factorial : ℚ) := by
  induction k with
  | zero => simp
  | succ i ih =>
      rw [pdProd_succ, ih, Nat.factorial_succ]
      have h := cast_choose_succ n i
      push_cast
      linear_combination (-(i.factorial : ℚ)) * h

lemma betaCoef_diag (m : ℚ) (k : ℕ) :
    betaCoef (m ^ 2 - 1 / 4) k = pdProd (m - 1 / 2) k * puProd (m + 1 / 2) k := by
  unfold betaCoef pdProd puProd
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  ring

lemma qSum_diag (n : ℕ) : qSum ((n : ℚ) ^ 2 - 1 / 4) n = dZsum n := by
  unfold qSum qPart dZsum
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hk := factorial_ne_zero_rat k
  unfold gCoef tZ
  rw [betaCoef_diag, pdProd_natCast]
  field_simp

/-- **Rivoal's identification** (equation (4.7) of the note): the diagonal value of Beukers'
Padé denominator at the moving half-integer point `x_m = 1/2 - m` is Zudilin's `Q_m`.

In the note this is quoted from Rivoal's Theorem 2; here it is proved from the two recurrences. -/
theorem bq_xpt_eq_Qz (m : ℕ) : bq (xpt m) m = Qz m := by
  have hy : (xpt m) ^ 2 - xpt m = (m : ℚ) ^ 2 - 1 / 4 := by
    unfold xpt
    ring
  rw [bq_eq_qSum, hy, qSum_diag, dZsum_eq_Qz]

end Catalan
