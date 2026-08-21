import RequestProject.BinaryDigits
import RequestProject.EDenominator
import RequestProject.EIntegralityB

/-!
# The explicit audited Nesterenko `(4,7)` row

This file fixes the positive double-pole convention of the audited full-LCM
normalization.  It defines the denominator coefficients `A2`, their finite sum
`nestB`, and the original partial-fraction numerator `nestC` parameterized by
the simple-pole coefficients `A1`.

The remaining period bridge `J n = 4 * nestB n * G - nestC n` is intentionally
kept separate: it is the partial-fraction theorem to be formalized from the
integral representation.
-/

namespace Catalan

open scoped BigOperators

/-- Landau's floor inequality for the factorial quotient used in Nesterenko's
coefficient-clearing argument. -/
theorem factorial_ratio_floor_le (u v d : ℕ) (hv : v ≤ u) (hd : 0 < d) :
    u / d + (2 * v) / d + (u - v) / d ≤ (2 * u) / d + v / d := by
  let a := u % d
  let b := v % d
  let q := u / d
  let r := v / d
  have ha : a < d := Nat.mod_lt _ hd
  have hb : b < d := Nat.mod_lt _ hd
  have hu : u = a + d * q := by
    dsimp [a, q]
    exact (Nat.mod_add_div u d).symm
  have hv' : v = b + d * r := by
    dsimp [b, r]
    exact (Nat.mod_add_div v d).symm
  have h2u : (2 * u) / d = 2 * q + (2 * a) / d := by
    rw [hu, show 2 * (a + d * q) = 2 * a + d * (2 * q) by ring,
      Nat.add_mul_div_left _ _ hd]
    omega
  have h2v : (2 * v) / d = 2 * r + (2 * b) / d := by
    rw [hv', show 2 * (b + d * r) = 2 * b + d * (2 * r) by ring,
      Nat.add_mul_div_left _ _ hd]
    omega
  rcases (show b ≤ a ∨ a < b by omega) with hab | hab
  · have hrq : r ≤ q := by
      by_contra h
      have : q < r := by omega
      nlinarith
    have huv : u - v = (a - b) + d * (q - r) := by
      have heq : u = v + ((a - b) + d * (q - r)) := calc
        u = a + d * q := hu
        _ = ((a - b) + b) + d * ((q - r) + r) := by
          rw [Nat.sub_add_cancel hab, Nat.sub_add_cancel hrq]
        _ = (b + d * r) + ((a - b) + d * (q - r)) := by ring
        _ = v + ((a - b) + d * (q - r)) := by rw [← hv']
      omega
    have hsub : (u - v) / d = q - r := by
      apply Nat.div_eq_of_lt_le
      · rw [huv]
        nlinarith
      · rw [huv]
        have habd : a - b < d := by omega
        simp only [add_mul]
        rw [mul_comm (q - r) d]
        omega
    rw [h2u, h2v, hsub]
    have hda : (2 * a) / d ≤ 1 := by
      have : (2 * a) / d < 2 := (Nat.div_lt_iff_lt_mul hd).2 (by omega)
      omega
    have hdb : (2 * b) / d ≤ (2 * a) / d := Nat.div_le_div_right (by omega)
    clear hu hv' huv ha hb hda h2u h2v
    omega
  · have hrq : r < q := by
      by_contra h
      have : q ≤ r := by omega
      nlinarith
    have huv : u - v = (a + d - b) + d * (q - r - 1) := by
      have hr1q : r + 1 ≤ q := by omega
      have hbad : b ≤ a + d := by omega
      have hq : q = (q - r - 1) + (r + 1) := by omega
      have had : a + d = (a + d - b) + b := by omega
      have heq : u = v + ((a + d - b) + d * (q - r - 1)) := calc
        u = a + d * q := hu
        _ = a + d * ((q - r - 1) + (r + 1)) := by rw [← hq]
        _ = (b + d * r) + ((a + d - b) + d * (q - r - 1)) := by
          calc
            a + d * ((q - r - 1) + (r + 1)) =
                (a + d) + d * r + d * (q - r - 1) := by ring
            _ = ((a + d - b) + b) + d * r + d * (q - r - 1) := by
              exact congrArg (fun x => x + d * r + d * (q - r - 1)) had
            _ = (b + d * r) + ((a + d - b) + d * (q - r - 1)) := by ac_rfl
        _ = v + ((a + d - b) + d * (q - r - 1)) := by rw [← hv']
      omega
    have hsub : (u - v) / d = q - r - 1 := by
      apply Nat.div_eq_of_lt_le
      · rw [huv, mul_comm (q - r - 1) d]
        exact Nat.le_add_left _ _
      · rw [huv]
        have habd : a + d - b < d := by omega
        simp only [add_mul]
        rw [mul_comm (q - r - 1) d]
        omega
    rw [h2u, h2v, hsub]
    have hda : (2 * a) / d ≤ 1 := by
      have : (2 * a) / d < 2 := (Nat.div_lt_iff_lt_mul hd).2 (by omega)
      omega
    have hdb : (2 * b) / d ≤ 1 := by
      have : (2 * b) / d < 2 := (Nat.div_lt_iff_lt_mul hd).2 (by omega)
      omega
    have hda0 : 0 ≤ (2 * a) / d := Nat.zero_le _
    have hdb0 : 0 ≤ (2 * b) / d := Nat.zero_le _
    generalize hs : q - r - 1 = s
    have hq : q = s + (r + 1) := by omega
    clear hu hv' huv ha hb h2u h2v
    rw [hq]
    omega

/-- The specialized factorial quotient in Nesterenko's Lemma 1 is an integer. -/
theorem factorial_ratio_dvd (u v : ℕ) (hv : v ≤ u) :
    Nat.factorial u * Nat.factorial (2 * v) * Nat.factorial (u - v) ∣
      Nat.factorial (2 * u) * Nat.factorial v := by
  rw [← Nat.factorization_le_iff_dvd (by positivity) (by positivity)]
  intro p
  by_cases hp : p.Prime
  · have hbound (x : ℕ) (hx : x ≤ 2 * u) : Nat.log p x < 2 * u + 1 := by
      exact lt_of_le_of_lt (Nat.log_le_self p x) (by omega)
    rw [Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity),
      Nat.factorization_mul (by positivity) (by positivity)]
    change u.factorial.factorization p + (2 * v).factorial.factorization p +
      (u - v).factorial.factorization p ≤
      (2 * u).factorial.factorization p + v.factorial.factorization p
    rw [Nat.factorization_factorial hp (hbound u (by omega)),
      Nat.factorization_factorial hp (hbound (2 * v) (by omega)),
      Nat.factorization_factorial hp (hbound (u - v) (by omega)),
      Nat.factorization_factorial hp (hbound (2 * u) (by omega)),
      Nat.factorization_factorial hp (hbound v (by omega)),
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun i _ =>
      factorial_ratio_floor_le u v (p ^ i) hv (pow_pos hp.pos i)
  · simp only [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact le_rfl

/-- The factorial quotient `F(u,v)` occurring in the audited coefficient formula. -/
noncomputable def nestFactorialRatio (u v : ℕ) : ℚ :=
  (Nat.factorial (2 * u) : ℚ) * Nat.factorial v /
    ((Nat.factorial u : ℚ) * Nat.factorial (2 * v) * Nat.factorial (u - v))

/-- Natural-number realization of `nestFactorialRatio` in its integral range. -/
def nestFactorialRatioNat (u v : ℕ) : ℕ :=
  (Nat.factorial (2 * u) * Nat.factorial v) /
    (Nat.factorial u * Nat.factorial (2 * v) * Nat.factorial (u - v))

theorem nestFactorialRatioNat_den_mul (u v : ℕ) (hv : v ≤ u) :
    (Nat.factorial u * Nat.factorial (2 * v) * Nat.factorial (u - v)) *
        nestFactorialRatioNat u v =
      Nat.factorial (2 * u) * Nat.factorial v := by
  exact Nat.mul_div_cancel' (factorial_ratio_dvd u v hv)

lemma nestFactorialRatioNat_ne_zero (u v : ℕ) (hv : v ≤ u) :
    nestFactorialRatioNat u v ≠ 0 := by
  intro h
  have heq := nestFactorialRatioNat_den_mul u v hv
  rw [h, mul_zero] at heq
  exact (Nat.mul_ne_zero (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)) heq.symm

theorem nestFactorialRatioNat_cast (u v : ℕ) (hv : v ≤ u) :
    (nestFactorialRatioNat u v : ℚ) = nestFactorialRatio u v := by
  have h := congrArg (fun x : ℕ => (x : ℚ))
    (nestFactorialRatioNat_den_mul u v hv)
  push_cast at h
  unfold nestFactorialRatio
  field_simp
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

theorem nestFactorialRatio_isInt (u v : ℕ) (hv : v ≤ u) :
    ∃ z : ℤ, (z : ℚ) = nestFactorialRatio u v := by
  obtain ⟨c, hc⟩ := factorial_ratio_dvd u v hv
  refine ⟨c, ?_⟩
  unfold nestFactorialRatio
  have hcQ := congrArg (fun x : ℕ => (x : ℚ)) hc
  push_cast at hcQ
  rw [hcQ]
  field_simp
  norm_num

/-- The audited, positive double-pole coefficient `A_{2,n,j}`. -/
noncomputable def nestA2 (n j : ℕ) : ℚ :=
  (2 : ℚ) ^ (-14 * (n : ℤ) + 2 * (j : ℤ) + 1) *
    (Nat.factorial (8 * n + 2 * j) : ℚ) * (Nat.factorial j : ℚ) *
      (Nat.factorial (6 * n) : ℚ) /
    ((Nat.factorial (4 * n) : ℚ) * (Nat.factorial (4 * n + j) : ℚ) *
      (Nat.factorial (3 * n - j) : ℚ) ^ 2 * (Nat.factorial (2 * j) : ℚ) ^ 2)

private lemma nestA2_scale_power (n j : ℕ) (hj : j ≤ 7 * n) :
    (4 : ℚ) ^ (7 * n - j) *
        (2 : ℚ) ^ (-14 * (n : ℤ) + 2 * (j : ℤ) + 1) = 2 := by
  rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul, ← zpow_natCast,
    ← zpow_add₀ (by norm_num : (2 : ℚ) ≠ 0)]
  have hsub : ((7 * n - j : ℕ) : ℤ) = 7 * (n : ℤ) - (j : ℤ) := by omega
  push_cast
  rw [hsub]
  norm_num
  ring_nf
  norm_num

/-- Formula (3.10) of the source, specialized to the audited `(4,7)` row.
It factors the scaled double-pole coefficient into three integers. -/
theorem nestA2_scaled_factorization (n j : ℕ) (hj : j ≤ 3 * n) :
    (4 : ℚ) ^ (7 * n - j) * nestA2 n j =
      2 * Nat.choose (3 * n) j * nestFactorialRatio (4 * n + j) j *
        nestFactorialRatio (3 * n) j := by
  have hj7 : j ≤ 7 * n := by omega
  have hp := nestA2_scale_power n j hj7
  calc
    (4 : ℚ) ^ (7 * n - j) * nestA2 n j =
        ((4 : ℚ) ^ (7 * n - j) *
          (2 : ℚ) ^ (-14 * (n : ℤ) + 2 * (j : ℤ) + 1)) *
          ((Nat.factorial (8 * n + 2 * j) : ℚ) * Nat.factorial j *
            Nat.factorial (6 * n)) /
          ((Nat.factorial (4 * n) : ℚ) * Nat.factorial (4 * n + j) *
            (Nat.factorial (3 * n - j)) ^ 2 * (Nat.factorial (2 * j)) ^ 2) := by
              rw [nestA2]
              ring
    _ = 2 * Nat.choose (3 * n) j * nestFactorialRatio (4 * n + j) j *
          nestFactorialRatio (3 * n) j := by
      rw [hp, nestFactorialRatio, nestFactorialRatio,
        Nat.cast_choose ℚ hj]
      rw [show 4 * n + j - j = 4 * n by omega]
      push_cast
      field_simp
      ring

/-- The first half of Nesterenko's coefficient-clearing theorem, now proved
directly from the explicit factorial formula. -/
theorem nestA2_scaled_isInt (n j : ℕ) (hj : j ≤ 3 * n) :
    ∃ z : ℤ, (z : ℚ) = (4 : ℚ) ^ (7 * n - j) * nestA2 n j := by
  obtain ⟨x, hx⟩ := nestFactorialRatio_isInt (4 * n + j) j (by omega)
  obtain ⟨y, hy⟩ := nestFactorialRatio_isInt (3 * n) j hj
  refine ⟨2 * (Nat.choose (3 * n) j : ℤ) * x * y, ?_⟩
  rw [nestA2_scaled_factorization n j hj]
  push_cast
  rw [hx, hy]

/-- The audited double-pole coefficients use the positive convention. -/
lemma nestA2_pos (n j : ℕ) : 0 < nestA2 n j := by
  unfold nestA2
  have htwo : 0 < (2 : ℚ) ^ (-14 * (n : ℤ) + 2 * (j : ℤ) + 1) :=
    zpow_pos (by norm_num) _
  positivity

lemma nest_val_factorial (k : ℕ) :
    padicValRat 2 (Nat.factorial k : ℚ) = (k : ℤ) - (s2 k : ℤ) := by
  rw [padicValRat.of_nat, padicValNat_two_factorial]
  have hk := s2_le k
  omega

/-- Exact `2`-adic valuation of the audited double-pole coefficient. -/
theorem nestA2_v2 (n j : ℕ) (hj : j ≤ 3 * n) :
    padicValRat 2 (nestA2 n j) =
      -14 * (n : ℤ) + 2 * (j : ℤ) + 1 + (s2 n : ℤ) - (s2 (3 * n) : ℤ) +
        2 * (s2 (3 * n - j) : ℤ) + (s2 j : ℤ) := by
  unfold nestA2
  rw [padicValRat.div (by positivity) (by positivity)]
  rw [padicValRat.mul (by positivity) (by positivity)]
  rw [padicValRat.mul (by positivity) (by positivity)]
  rw [padicValRat.mul (by positivity) (by positivity)]
  rw [padicValRat.mul (by positivity) (by positivity)]
  rw [padicValRat.mul (by positivity) (by positivity)]
  rw [padicValRat.mul (by positivity) (by positivity)]
  rw [padicValRat.pow, padicValRat.pow, padicValRat.zpow,
    nest_val_factorial, nest_val_factorial, nest_val_factorial,
    nest_val_factorial, nest_val_factorial, nest_val_factorial, nest_val_factorial]
  rw [show 8 * n + 2 * j = 2 * (4 * n + j) by omega, s2_two_mul,
    show 6 * n = 2 * (3 * n) by omega, s2_two_mul,
    show 4 * n = 2 * (2 * n) by omega, s2_two_mul, s2_two_mul,
    show 2 * j = 2 * j by rfl, s2_two_mul]
  have hsub : ((3 * n - j : ℕ) : ℤ) = 3 * (n : ℤ) - (j : ℤ) := by
    omega
  rw [hsub]
  have htwo : padicValRat 2 (2 : ℚ) = 1 := by
    exact padicValRat.self (by norm_num)
  rw [htwo]
  push_cast
  ring

theorem nestA2_zero_v2 (n : ℕ) :
    padicValRat 2 (nestA2 n 0) =
      1 + (s2 n : ℤ) + (s2 (3 * n) : ℤ) - 14 * (n : ℤ) := by
  rw [nestA2_v2 n 0 (by omega)]
  simp
  ring

/-- The `j=0` term is the unique term of smallest `2`-adic valuation. -/
theorem nestA2_zero_unique_min (n j : ℕ) (hj0 : 1 ≤ j) (hj : j ≤ 3 * n) :
    padicValRat 2 (nestA2 n 0) < padicValRat 2 (nestA2 n j) := by
  rw [nestA2_zero_v2, nestA2_v2 n j hj]
  have hadd : s2 (3 * n) ≤ s2 (3 * n - j) + s2 j := by
    have h := s2_add_le (3 * n - j) j
    rw [Nat.sub_add_cancel hj] at h
    exact h
  have hjdigit := s2_le j
  have hj0Z : (1 : ℤ) ≤ (j : ℤ) := by exact_mod_cast hj0
  have haddZ : (s2 (3 * n) : ℤ) ≤ (s2 (3 * n - j) : ℤ) + (s2 j : ℤ) := by
    exact_mod_cast hadd
  have hjdigitZ : (s2 j : ℤ) ≤ (j : ℤ) := by exact_mod_cast hjdigit
  omega

/-- The one-level floor estimate used to clear the denominator of
`ν!/(3/2)_ν`. -/
lemma two_mul_add_one_div_le (ν d : ℕ) (hd : 0 < d) :
    (2 * ν + 1) / d ≤ 2 * (ν / d) + 1 := by
  let a := ν % d
  let q := ν / d
  have ha : a < d := Nat.mod_lt _ hd
  have hν : ν = a + d * q := by
    dsimp [a, q]
    exact (Nat.mod_add_div ν d).symm
  change (2 * ν + 1) / d ≤ 2 * q + 1
  rw [hν, show 2 * (a + d * q) + 1 = (2 * a + 1) + d * (2 * q) by ring,
    Nat.add_mul_div_left _ _ hd]
  have : (2 * a + 1) / d < 2 := (Nat.div_lt_iff_lt_mul hd).2 (by omega)
  omega

/-- Prime-by-prime denominator clearing for the half-integral Pochhammer
factorial quotient. -/
theorem pochhammer_factorial_dvd (n ν : ℕ) (hν : ν < 3 * n) :
    Nat.factorial (2 * ν + 1) ∣
      Dlcm (6 * n) * 4 ^ ν * (Nat.factorial ν) ^ 2 := by
  have hD : Dlcm (6 * n) ≠ 0 := Dlcm_ne_zero _
  have hR : Dlcm (6 * n) * 4 ^ ν * (Nat.factorial ν) ^ 2 ≠ 0 := by positivity
  rw [← Nat.factorization_le_iff_dvd (Nat.factorial_ne_zero _) hR, Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · rw [Nat.factorization_mul (Nat.mul_ne_zero hD (by positivity)) (by positivity),
      Nat.factorization_mul hD (by positivity), Nat.factorization_pow,
      Nat.factorization_pow]
    change (Nat.factorial (2 * ν + 1)).factorization p ≤
      (Dlcm (6 * n)).factorization p + ν * (Nat.factorization 4) p +
        2 * (Nat.factorial ν).factorization p
    rcases eq_or_ne p 2 with rfl | hp2
    · have hfac : (Nat.factorial (2 * ν + 1)).factorization 2 =
          (Nat.factorial (2 * ν)).factorization 2 := by
        rw [Nat.factorial_succ, Nat.factorization_mul (by omega) (by positivity)]
        change (Nat.factorization (2 * ν + 1)) 2 +
          (Nat.factorial (2 * ν)).factorization 2 = _
        rw [Nat.factorization_eq_zero_of_not_dvd (by omega)]
        simp
      have hle : (Nat.factorial (2 * ν)).factorization 2 ≤ 2 * ν := by
        rw [Nat.factorization_def _ Nat.prime_two]
        exact @padicValNat_factorial_le 2 ⟨Nat.prime_two⟩ (2 * ν)
      have hfour : (Nat.factorization 4) 2 = 2 := by
        rw [show 4 = 2 ^ 2 by norm_num, Nat.factorization_pow]
        change 2 * (Nat.factorization 2) 2 = 2
        rw [Nat.Prime.factorization_self Nat.prime_two]
      rw [hfac, hfour]
      omega
    · let e := Nat.log p (2 * ν + 1)
      have hpow : p ^ e ≤ 6 * n := by
        calc p ^ e ≤ 2 * ν + 1 := Nat.pow_log_le_self p (by omega)
          _ ≤ 6 * n := by omega
      have hD' : e ≤ (Dlcm (6 * n)).factorization p :=
        le_factorization_Dlcm hp hpow
      have hb : Nat.log p (2 * ν + 1) < e + 1 := by omega
      have hbν : Nat.log p ν < e + 1 := by
        have := Nat.log_mono_right (show ν ≤ 2 * ν + 1 by omega) (b := p)
        omega
      rw [Nat.factorization_factorial hp hb, Nat.factorization_factorial hp hbν]
      have hfour : (Nat.factorization 4) p = 0 := by
        rw [show 4 = 2 ^ 2 by norm_num, Nat.factorization_pow,
          Nat.Prime.factorization Nat.prime_two]
        simp [hp2]
      rw [hfour]
      simp only [mul_zero, add_zero]
      calc
        ∑ i ∈ Finset.Ico 1 (e + 1), (2 * ν + 1) / p ^ i
            ≤ ∑ i ∈ Finset.Ico 1 (e + 1), (2 * (ν / p ^ i) + 1) :=
              Finset.sum_le_sum fun i _ =>
                two_mul_add_one_div_le ν (p ^ i) (pow_pos hp.pos i)
        _ = 2 * (∑ i ∈ Finset.Ico 1 (e + 1), ν / p ^ i) + e := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
              simp
        _ ≤ (Dlcm (6 * n)).factorization p +
              2 * (∑ i ∈ Finset.Ico 1 (e + 1), ν / p ^ i) := by omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- The half-integral rising factorial `(3/2)_ν`. -/
noncomputable def nestPochhammerThreeHalves (ν : ℕ) : ℚ :=
  ∏ r ∈ Finset.range ν, ((3 : ℚ) / 2 + r)

/-- Closed factorial form of the half-integral rising factorial:
`(3/2)_ν = (2ν+1)! / (4^ν ν!)`. -/
theorem nestPochhammerThreeHalves_eq (ν : ℕ) :
    nestPochhammerThreeHalves ν =
      (Nat.factorial (2 * ν + 1) : ℚ) /
        ((4 : ℚ) ^ ν * (Nat.factorial ν : ℚ)) := by
  induction ν with
  | zero => norm_num [nestPochhammerThreeHalves]
  | succ ν ih =>
      rw [nestPochhammerThreeHalves, Finset.prod_range_succ]
      rw [show (∏ r ∈ Finset.range ν, ((3 : ℚ) / 2 + r)) =
          nestPochhammerThreeHalves ν by rfl, ih]
      have hfac : Nat.factorial (2 * (ν + 1) + 1) =
          (2 * ν + 3) * (2 * ν + 2) * Nat.factorial (2 * ν + 1) := by
        rw [show 2 * (ν + 1) + 1 = (2 * ν + 2) + 1 by omega,
          Nat.factorial_succ,
          show 2 * ν + 2 = (2 * ν + 1) + 1 by omega, Nat.factorial_succ]
        ring
      have hfacν : Nat.factorial (ν + 1) = (ν + 1) * Nat.factorial ν :=
        Nat.factorial_succ ν
      rw [hfac, hfacν]
      push_cast
      field_simp
      ring

/-- Consequently `ν!/(3/2)_ν = 4^ν(ν!)²/(2ν+1)!`. -/
theorem factorial_div_nestPochhammerThreeHalves (ν : ℕ) :
    (Nat.factorial ν : ℚ) / nestPochhammerThreeHalves ν =
      (4 : ℚ) ^ ν * (Nat.factorial ν : ℚ) ^ 2 /
        (Nat.factorial (2 * ν + 1) : ℚ) := by
  rw [nestPochhammerThreeHalves_eq]
  field_simp

/-- The elementary harmonic-denominator lemma used in the conservative
`D_{6n}²` normalization. -/
theorem Dlcm_mul_factorial_div_pochhammer_isInt (n ν : ℕ) (hν : ν < 3 * n) :
    ∃ z : ℤ, (z : ℚ) =
      (Dlcm (6 * n) : ℚ) *
        ((Nat.factorial ν : ℚ) / nestPochhammerThreeHalves ν) := by
  obtain ⟨c, hc⟩ := pochhammer_factorial_dvd n ν hν
  refine ⟨c, ?_⟩
  rw [factorial_div_nestPochhammerThreeHalves]
  have hcQ := congrArg (fun x : ℕ => (x : ℚ)) hc
  push_cast at hcQ
  field_simp
  simpa [mul_comm, mul_left_comm, mul_assoc] using hcQ.symm

/-- The audited Nesterenko denominator coefficient `B_n`. -/
noncomputable def nestB (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (3 * n + 1), nestA2 n j

/-- Exact denominator valuation of the audited Nesterenko row. -/
theorem nestB_v2 (n : ℕ) (hn : 1 ≤ n) :
    padicValRat 2 (nestB n) =
      1 + (s2 n : ℤ) + (s2 (3 * n) : ℤ) - 14 * (n : ℤ) := by
  let S : Finset ℕ := Finset.Icc 1 (3 * n)
  have hSne : S.Nonempty := ⟨1, by simp [S]; omega⟩
  have htailpos : 0 < ∑ j ∈ S, nestA2 n j :=
    Finset.sum_pos (fun j _ => nestA2_pos n j) hSne
  have htailval : padicValRat 2 (nestA2 n 0) <
      padicValRat 2 (∑ j ∈ S, nestA2 n j) := by
    apply padicValRat.lt_sum_of_lt hSne
    · intro j hj
      simp only [S, Finset.mem_Icc] at hj
      exact nestA2_zero_unique_min n j hj.1 hj.2
    · exact fun j => nestA2_pos n j
  have hrange : Finset.range (3 * n + 1) = insert 0 S := by
    ext j
    simp only [S, Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  rw [nestB, hrange, Finset.sum_insert (by simp [S])]
  rw [padicValRat.add_eq_of_lt (ne_of_gt (add_pos (nestA2_pos n 0) htailpos))
    (ne_of_gt (nestA2_pos n 0)) (ne_of_gt htailpos) htailval]
  exact nestA2_zero_v2 n

theorem nest_four_B_v2 (n : ℕ) (hn : 1 ≤ n) :
    padicValRat 2 (4 * nestB n) =
      3 + (s2 n : ℤ) + (s2 (3 * n) : ℤ) - 14 * (n : ℤ) := by
  rw [padicValRat.mul (by norm_num) (ne_of_gt (by
    rw [nestB]
    exact Finset.sum_pos (fun j _ => nestA2_pos n j) ⟨0, by simp⟩)), nestB_v2 n hn]
  have h4 : padicValRat 2 (4 : ℚ) = 2 := by
    have h2 : padicValRat 2 (2 : ℚ) = 1 :=
      padicValRat.self (p := 2) (by norm_num)
    rw [show (4 : ℚ) = 2 * 2 by norm_num,
      padicValRat.mul (by norm_num) (by norm_num), h2]
    norm_num
  rw [h4]
  ring

/-- The rational beta prefactor in the Nesterenko hypergeometric form. -/
noncomputable def nestPrefactor (n : ℕ) : ℚ :=
  (4 : ℚ) ^ (7 * n + 2) * (Nat.factorial (8 * n) : ℚ) *
      (Nat.factorial (6 * n) : ℚ) * (Nat.factorial (7 * n + 1) : ℚ) ^ 2 /
    (Nat.factorial (14 * n + 2) : ℚ) ^ 2

/-- Exact valuation of the beta prefactor. -/
theorem nestPrefactor_v2 (n : ℕ) :
    padicValRat 2 (nestPrefactor n) =
      14 * (n : ℤ) + 2 - (s2 n : ℤ) - (s2 (3 * n) : ℤ) := by
  unfold nestPrefactor
  rw [padicValRat.div (by positivity) (by positivity)]
  rw [padicValRat.mul (by positivity) (by positivity)]
  rw [padicValRat.mul (by positivity) (by positivity)]
  rw [padicValRat.mul (by positivity) (by positivity)]
  rw [padicValRat.pow, padicValRat.pow, padicValRat.pow,
    nest_val_factorial, nest_val_factorial, nest_val_factorial, nest_val_factorial]
  have h4 : padicValRat 2 (4 : ℚ) = 2 := by
    have h2 : padicValRat 2 (2 : ℚ) = 1 :=
      padicValRat.self (p := 2) (by norm_num)
    rw [show (4 : ℚ) = 2 * 2 by norm_num,
      padicValRat.mul (by norm_num) (by norm_num), h2]
    norm_num
  rw [h4, show 8 * n = 2 * (2 * (2 * n)) by omega,
    s2_two_mul, s2_two_mul, s2_two_mul,
    show 6 * n = 2 * (3 * n) by omega, s2_two_mul,
    show 14 * n + 2 = 2 * (7 * n + 1) by omega, s2_two_mul]
  push_cast
  ring

/-- The original partial-fraction numerator coefficient `C_n`.  The specialized
clearing theorem for `A₁` is the only literature input needed for the conservative
integer normalization of this row. -/
noncomputable def nestC (A1 : ℕ → ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (3 * n + 1),
    ∑ ν ∈ Finset.range j,
      (Nat.factorial ν : ℚ) / nestPochhammerThreeHalves ν *
        (A1 n j + nestA2 n j / ((ν : ℚ) + 1 / 2))

/-- The odd denominator occurring in the `A₂/(ν+1/2)` term is cleared by
`2 D_{6n}` in the required range. -/
lemma two_mul_Dlcm_div_odd_isInt (n ν : ℕ) (hν : ν < 3 * n) :
    ∃ z : ℤ, (z : ℚ) = 2 * (Dlcm (6 * n) : ℚ) / (2 * ν + 1 : ℚ) := by
  obtain ⟨c, hc⟩ : (2 * ν + 1) ∣ Dlcm (6 * n) :=
    dvd_Dlcm (by omega) (by omega)
  refine ⟨2 * (c : ℤ), ?_⟩
  have hcQ := congrArg (fun x : ℕ => (x : ℚ)) hc
  push_cast at hcQ
  rw [hcQ]
  norm_num
  field_simp

/-- Conservative numerator clearing, conditional only on the specialized
simple-pole coefficient clearing.  All other denominator estimates are proved
above. -/
theorem nestC_scaled_isInt_of_A1_clearing (A1 : ℕ → ℕ → ℚ) (n : ℕ)
    (hA1 : ∀ j, j ≤ 3 * n →
      ∃ z : ℤ, (z : ℚ) =
        (4 : ℚ) ^ (7 * n - j) * (Dlcm (6 * n) : ℚ) * A1 n j) :
    ∃ z : ℤ, (z : ℚ) =
      (4 : ℚ) ^ (7 * n) * (Dlcm (6 * n) : ℚ) ^ 2 * nestC A1 n := by
  rw [← mem_ZSub_iff, nestC, Finset.mul_sum]
  refine Subring.sum_mem _ fun j hj => ?_
  simp only [Finset.mem_range] at hj
  have hj3 : j ≤ 3 * n := by omega
  have hj7 : j ≤ 7 * n := by omega
  rw [Finset.mul_sum]
  refine Subring.sum_mem _ fun ν hν => ?_
  simp only [Finset.mem_range] at hν
  have hν3 : ν < 3 * n := lt_of_lt_of_le hν hj3
  obtain ⟨zr, hzr⟩ := Dlcm_mul_factorial_div_pochhammer_isInt n ν hν3
  obtain ⟨za, hza⟩ := hA1 j hj3
  obtain ⟨z₂, hz₂⟩ := nestA2_scaled_isInt n j hj3
  obtain ⟨zo, hzo⟩ := two_mul_Dlcm_div_odd_isInt n ν hν3
  have hr : (Dlcm (6 * n) : ℚ) *
      ((Nat.factorial ν : ℚ) / nestPochhammerThreeHalves ν) ∈ ZSub :=
    (mem_ZSub_iff _).mpr ⟨zr, hzr⟩
  have ha : (4 : ℚ) ^ (7 * n - j) * (Dlcm (6 * n) : ℚ) * A1 n j ∈ ZSub :=
    (mem_ZSub_iff _).mpr ⟨za, hza⟩
  have ha₂ : (4 : ℚ) ^ (7 * n - j) * nestA2 n j ∈ ZSub :=
    (mem_ZSub_iff _).mpr ⟨z₂, hz₂⟩
  have ho : 2 * (Dlcm (6 * n) : ℚ) / (2 * ν + 1 : ℚ) ∈ ZSub :=
    (mem_ZSub_iff _).mpr ⟨zo, hzo⟩
  have h4j : (4 : ℚ) ^ j ∈ ZSub :=
    (mem_ZSub_iff _).mpr ⟨(4 ^ j : ℤ), by norm_num⟩
  have hp : (4 : ℚ) ^ (7 * n) = 4 ^ j * 4 ^ (7 * n - j) := by
    rw [← pow_add, Nat.add_sub_of_le hj7]
  have heq :
      (4 : ℚ) ^ (7 * n) * (Dlcm (6 * n) : ℚ) ^ 2 *
          ((Nat.factorial ν : ℚ) / nestPochhammerThreeHalves ν *
            (A1 n j + nestA2 n j / ((ν : ℚ) + 1 / 2))) =
        ((Dlcm (6 * n) : ℚ) *
            ((Nat.factorial ν : ℚ) / nestPochhammerThreeHalves ν)) * 4 ^ j *
              ((4 : ℚ) ^ (7 * n - j) * (Dlcm (6 * n) : ℚ) * A1 n j) +
        ((Dlcm (6 * n) : ℚ) *
            ((Nat.factorial ν : ℚ) / nestPochhammerThreeHalves ν)) * 4 ^ j *
              ((4 : ℚ) ^ (7 * n - j) * nestA2 n j) *
                (2 * (Dlcm (6 * n) : ℚ) / (2 * ν + 1 : ℚ)) := by
    rw [hp]
    field_simp
  rw [heq]
  exact ZSub.add_mem
    (ZSub.mul_mem (ZSub.mul_mem hr h4j) ha)
    (ZSub.mul_mem (ZSub.mul_mem (ZSub.mul_mem hr h4j) ha₂) ho)

end Catalan
