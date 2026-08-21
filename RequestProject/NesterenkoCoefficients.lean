import RequestProject.NesterenkoRow

/-!
# The concrete simple-pole coefficients of the Nesterenko row

This file turns the audited backward triangular relation into a genuine
descending definition.  Thus both partial-fraction rows are concrete finite
rational objects; no existence hypothesis for `A₁` remains.
-/

namespace Catalan

open scoped BigOperators

/-- The central-binomial kernel `h_l = choose(2l,l)/4^l`. -/
noncomputable def nestH (l : ℕ) : ℚ :=
  (Nat.choose (2 * l) l : ℚ) / (4 : ℚ) ^ l

/-- The ordinary harmonic number `H_j`. -/
noncomputable def nestHarmonic (j : ℕ) : ℚ :=
  ∑ r ∈ Finset.range j, (1 : ℚ) / (r + 1)

/-- The explicit logarithmic-derivative term in the triangular equation. -/
noncomputable def nestM (n j : ℕ) : ℚ :=
  nestHarmonic j - 2 * nestHarmonic (3 * n - j) +
    2 * (∑ r ∈ Finset.range j, (1 : ℚ) / (2 * r + 1)) -
    2 * (∑ r ∈ Finset.range (4 * n), (1 : ℚ) / (2 * (j + r) + 1))

/-- The reverse index used to justify recursion from `3n` down to `0`. -/
private def nestReverseIndex (n j : ℕ) : ℕ := 3 * n - j

/-- The simple-pole coefficient `A_{1,n,j}`, defined by the audited backward
triangular relation.  Calls only occur at `j+l>j`, hence at a strictly smaller
reverse index. -/
noncomputable def nestA1 (n : ℕ) : ℕ → ℚ :=
  WellFounded.fix (measure (nestReverseIndex n)).wf fun j rec =>
    if hj : j ≤ 3 * n then
      nestA2 n j * nestM n j -
        ∑ l : (Finset.Icc 1 (3 * n - j)),
          nestH l.1 *
            (rec (j + l.1) (by
                show nestReverseIndex n (j + l.1) < nestReverseIndex n j
                unfold nestReverseIndex
                have hl := (Finset.mem_Icc.mp l.2).1
                have hlu := (Finset.mem_Icc.mp l.2).2
                omega) + nestA2 n (j + l.1) / l.1)
    else 0

/-- The defining triangular identity, now a theorem about the concrete
coefficients rather than an imported row condition. -/
theorem nestA1_triangular (n j : ℕ) (hj : j ≤ 3 * n) :
    nestA1 n j +
        ∑ l ∈ Finset.Icc 1 (3 * n - j),
          nestH l * (nestA1 n (j + l) + nestA2 n (j + l) / l) =
      nestA2 n j * nestM n j := by
  have hfix : nestA1 n j +
        ∑ l : (Finset.Icc 1 (3 * n - j)),
          nestH l.1 * (nestA1 n (j + l.1) + nestA2 n (j + l.1) / l.1) =
      nestA2 n j * nestM n j := by
    rw [nestA1, WellFounded.fix_eq]
    simp only [dif_pos hj]
    ring
  have hsum :
      (∑ l : (Finset.Icc 1 (3 * n - j)),
          nestH l.1 * (nestA1 n (j + l.1) + nestA2 n (j + l.1) / (l.1 : ℚ))) =
        ∑ l ∈ Finset.Icc 1 (3 * n - j),
          nestH l * (nestA1 n (j + l) + nestA2 n (j + l) / (l : ℚ)) := by
    simpa only using Finset.sum_coe_sort (Finset.Icc 1 (3 * n - j))
      (fun l => nestH l * (nestA1 n (j + l) + nestA2 n (j + l) / (l : ℚ)))
  rw [hsum] at hfix
  exact hfix

/-- At the top index the triangular sum is empty. -/
theorem nestA1_top (n : ℕ) :
    nestA1 n (3 * n) = nestA2 n (3 * n) * nestM n (3 * n) := by
  have h := nestA1_triangular n (3 * n) (by omega)
  simpa using h

/-- The concrete numerator coefficient obtained from the original audited
partial-fraction formula. -/
noncomputable def nestCConcrete (n : ℕ) : ℚ := nestC nestA1 n

theorem nestCConcrete_eq (n : ℕ) :
    nestCConcrete n =
      ∑ j ∈ Finset.range (3 * n + 1),
        ∑ ν ∈ Finset.range j,
          (Nat.factorial ν : ℚ) / nestPochhammerThreeHalves ν *
            (nestA1 n j + nestA2 n j / ((ν : ℚ) + 1 / 2)) := by
  rfl

/-! ### Descending coefficient clearing

The triangular relation reduces the full `A₁` theorem to the single
logarithmic-derivative divisibility statement for `A₂ M`. -/

/-- Once the diagonal derivative term is integral, the backward triangular
system propagates the required clearing to every simple-pole coefficient. -/
theorem nestA1_scaled_mem_ZSub_of_diagonal (n : ℕ)
    (hdiag : ∀ j, j ≤ 3 * n →
      ((4 : ℚ) ^ (7 * n - j) * (Dlcm (6 * n) : ℚ) *
        (nestA2 n j * nestM n j)) ∈ ZSub) :
    ∀ j, j ≤ 3 * n →
      ((4 : ℚ) ^ (7 * n - j) * (Dlcm (6 * n) : ℚ) * nestA1 n j) ∈ ZSub := by
  have aux : ∀ k j, k = 3 * n - j → j ≤ 3 * n →
      ((4 : ℚ) ^ (7 * n - j) * (Dlcm (6 * n) : ℚ) * nestA1 n j) ∈ ZSub := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro j hkj hj
      have htri := nestA1_triangular n j hj
      have hsolve : nestA1 n j = nestA2 n j * nestM n j -
          ∑ l ∈ Finset.Icc 1 (3 * n - j),
            nestH l * (nestA1 n (j + l) + nestA2 n (j + l) / l) := by
        linarith
      rw [hsolve, mul_sub]
      refine ZSub.sub_mem (hdiag j hj) ?_
      rw [Finset.mul_sum]
      refine Subring.sum_mem _ fun l hl => ?_
      simp only [Finset.mem_Icc] at hl
      obtain ⟨hl1, hlu⟩ := hl
      have hjl : j + l ≤ 3 * n := by omega
      have hrev : 3 * n - (j + l) < k := by omega
      have hA1 := ih (3 * n - (j + l)) hrev (j + l) rfl hjl
      have hA2 : (4 : ℚ) ^ (7 * n - (j + l)) * nestA2 n (j + l) ∈ ZSub := by
        obtain ⟨z, hz⟩ := nestA2_scaled_isInt n (j + l) hjl
        exact (mem_ZSub_iff _).mpr ⟨z, hz⟩
      obtain ⟨c, hc⟩ : l ∣ Dlcm (6 * n) := dvd_Dlcm (by omega) (by omega)
      have hDl : (Dlcm (6 * n) : ℚ) / (l : ℚ) ∈ ZSub := by
        refine (mem_ZSub_iff _).mpr ⟨c, ?_⟩
        have hcQ := congrArg (fun x : ℕ => (x : ℚ)) hc
        push_cast at hcQ
        rw [hcQ]
        field_simp
        norm_num
      have hchoose : (Nat.choose (2 * l) l : ℚ) ∈ ZSub :=
        (mem_ZSub_iff _).mpr ⟨Nat.choose (2 * l) l, by norm_num⟩
      have hp : (4 : ℚ) ^ (7 * n - j) =
          4 ^ l * 4 ^ (7 * n - (j + l)) := by
        rw [← pow_add]
        congr 1
        omega
      have heq :
          (4 : ℚ) ^ (7 * n - j) * (Dlcm (6 * n) : ℚ) *
              (nestH l * (nestA1 n (j + l) + nestA2 n (j + l) / l)) =
            (Nat.choose (2 * l) l : ℚ) *
                ((4 : ℚ) ^ (7 * n - (j + l)) * (Dlcm (6 * n) : ℚ) *
                  nestA1 n (j + l)) +
              (Nat.choose (2 * l) l : ℚ) *
                ((Dlcm (6 * n) : ℚ) / l) *
                ((4 : ℚ) ^ (7 * n - (j + l)) * nestA2 n (j + l)) := by
        rw [nestH, hp]
        field_simp
      rw [heq]
      exact ZSub.add_mem (ZSub.mul_mem hchoose hA1)
        (ZSub.mul_mem (ZSub.mul_mem hchoose hDl) hA2)
  intro j hj
  exact aux (3 * n - j) j rfl hj

/-- Existential-integer form of the specialized `A₁` clearing theorem. -/
theorem nestA1_scaled_isInt_of_diagonal (n : ℕ)
    (hdiag : ∀ j, j ≤ 3 * n →
      ((4 : ℚ) ^ (7 * n - j) * (Dlcm (6 * n) : ℚ) *
        (nestA2 n j * nestM n j)) ∈ ZSub)
    (j : ℕ) (hj : j ≤ 3 * n) :
    ∃ z : ℤ, (z : ℚ) =
      (4 : ℚ) ^ (7 * n - j) * (Dlcm (6 * n) : ℚ) * nestA1 n j :=
  (mem_ZSub_iff _).mp (nestA1_scaled_mem_ZSub_of_diagonal n hdiag j hj)

/-- Consequently the entire concrete conservative numerator is integral. -/
theorem nestCConcrete_scaled_isInt_of_diagonal (n : ℕ)
    (hdiag : ∀ j, j ≤ 3 * n →
      ((4 : ℚ) ^ (7 * n - j) * (Dlcm (6 * n) : ℚ) *
        (nestA2 n j * nestM n j)) ∈ ZSub) :
    ∃ z : ℤ, (z : ℚ) =
      (4 : ℚ) ^ (7 * n) * (Dlcm (6 * n) : ℚ) ^ 2 * nestCConcrete n := by
  exact nestC_scaled_isInt_of_A1_clearing nestA1 n
    (nestA1_scaled_isInt_of_diagonal n hdiag)

/-! The diagonal term itself reduces to the long odd denominators occurring
in the logarithmic derivative.  Denominators at most `6n` are supplied by the
LCM directly. -/

private lemma Dlcm_div_mem_ZSub {n d : ℕ} (hd1 : 1 ≤ d) (hd6 : d ≤ 6 * n) :
    (Dlcm (6 * n) : ℚ) / (d : ℚ) ∈ ZSub := by
  obtain ⟨c, hc⟩ := dvd_Dlcm hd1 hd6
  refine (mem_ZSub_iff _).mpr ⟨c, ?_⟩
  have hcQ := congrArg (fun x : ℕ => (x : ℚ)) hc
  push_cast at hcQ
  rw [hcQ]
  field_simp
  norm_num

/-- Reduction of the diagonal derivative divisibility to the only terms whose
odd denominators may exceed `D_{6n}`. -/
theorem nestA2_diagonal_mem_of_long_odd (n : ℕ)
    (hlong : ∀ j, j ≤ 3 * n → ∀ r, r < 4 * n →
      ((4 : ℚ) ^ (7 * n - j) * nestA2 n j) *
        (2 * (Dlcm (6 * n) : ℚ) / (2 * (j + r) + 1 : ℚ)) ∈ ZSub) :
    ∀ j, j ≤ 3 * n →
      ((4 : ℚ) ^ (7 * n - j) * (Dlcm (6 * n) : ℚ) *
        (nestA2 n j * nestM n j)) ∈ ZSub := by
  intro j hj
  let s : ℚ := (4 : ℚ) ^ (7 * n - j) * nestA2 n j
  have hs : s ∈ ZSub := by
    obtain ⟨z, hz⟩ := nestA2_scaled_isInt n j hj
    exact (mem_ZSub_iff _).mpr ⟨z, by simpa [s] using hz⟩
  have htwo : (2 : ℚ) ∈ ZSub := (mem_ZSub_iff _).mpr ⟨2, by norm_num⟩
  have hHj : s * (Dlcm (6 * n) : ℚ) * nestHarmonic j ∈ ZSub := by
    rw [nestHarmonic, Finset.mul_sum]
    refine Subring.sum_mem _ fun r hr => ?_
    simp only [Finset.mem_range] at hr
    have hr3 : r + 1 ≤ 3 * n := by omega
    have h36 : 3 * n ≤ 6 * n := Nat.mul_le_mul_right n (by norm_num)
    have hd' := Dlcm_div_mem_ZSub (n := n) (d := r + 1) (by omega) (hr3.trans h36)
    have hd : (Dlcm (6 * n) : ℚ) / (r + 1 : ℚ) ∈ ZSub := by
      simpa only [Nat.cast_add, Nat.cast_one] using hd'
    have heq : s * (Dlcm (6 * n) : ℚ) * ((1 : ℚ) / (r + 1)) =
        s * ((Dlcm (6 * n) : ℚ) / (r + 1)) := by ring
    rw [heq]
    exact ZSub.mul_mem hs hd
  have hHsub : s * (Dlcm (6 * n) : ℚ) * nestHarmonic (3 * n - j) ∈ ZSub := by
    rw [nestHarmonic, Finset.mul_sum]
    refine Subring.sum_mem _ fun r hr => ?_
    simp only [Finset.mem_range] at hr
    have hr3 : r + 1 ≤ 3 * n := by omega
    have h36 : 3 * n ≤ 6 * n := Nat.mul_le_mul_right n (by norm_num)
    have hd' := Dlcm_div_mem_ZSub (n := n) (d := r + 1) (by omega) (hr3.trans h36)
    have hd : (Dlcm (6 * n) : ℚ) / (r + 1 : ℚ) ∈ ZSub := by
      simpa only [Nat.cast_add, Nat.cast_one] using hd'
    have heq : s * (Dlcm (6 * n) : ℚ) * ((1 : ℚ) / (r + 1)) =
        s * ((Dlcm (6 * n) : ℚ) / (r + 1)) := by ring
    rw [heq]
    exact ZSub.mul_mem hs hd
  have hoddShort : s * (Dlcm (6 * n) : ℚ) *
      (2 * ∑ r ∈ Finset.range j, (1 : ℚ) / (2 * r + 1)) ∈ ZSub := by
    rw [show s * (Dlcm (6 * n) : ℚ) *
        (2 * ∑ r ∈ Finset.range j, (1 : ℚ) / (2 * r + 1)) =
      (s * (Dlcm (6 * n) : ℚ) * 2) *
        ∑ r ∈ Finset.range j, (1 : ℚ) / (2 * r + 1) by ring,
      Finset.mul_sum]
    refine Subring.sum_mem _ fun r hr => ?_
    simp only [Finset.mem_range] at hr
    obtain ⟨z, hz⟩ := two_mul_Dlcm_div_odd_isInt n r (by omega)
    have ho : 2 * (Dlcm (6 * n) : ℚ) / (2 * r + 1 : ℚ) ∈ ZSub :=
      (mem_ZSub_iff _).mpr ⟨z, hz⟩
    have heq : s * (Dlcm (6 * n) : ℚ) * 2 *
          ((1 : ℚ) / (2 * r + 1)) =
        s * (2 * (Dlcm (6 * n) : ℚ) / (2 * r + 1)) := by ring
    rw [heq]
    exact ZSub.mul_mem hs ho
  have hoddLong : s * (Dlcm (6 * n) : ℚ) *
      (2 * ∑ r ∈ Finset.range (4 * n), (1 : ℚ) / (2 * (j + r) + 1)) ∈ ZSub := by
    rw [show s * (Dlcm (6 * n) : ℚ) *
        (2 * ∑ r ∈ Finset.range (4 * n), (1 : ℚ) / (2 * (j + r) + 1)) =
      (s * (Dlcm (6 * n) : ℚ) * 2) *
        ∑ r ∈ Finset.range (4 * n), (1 : ℚ) / (2 * (j + r) + 1) by ring,
      Finset.mul_sum]
    refine Subring.sum_mem _ fun r hr => ?_
    simp only [Finset.mem_range] at hr
    have h := hlong j hj r hr
    have heq : s * (Dlcm (6 * n) : ℚ) * 2 *
          ((1 : ℚ) / (2 * (j + r) + 1)) =
        s * (2 * (Dlcm (6 * n) : ℚ) / (2 * (j + r) + 1)) := by ring
    rwa [heq]
  have heq :
      (4 : ℚ) ^ (7 * n - j) * (Dlcm (6 * n) : ℚ) *
          (nestA2 n j * nestM n j) =
        (s * (Dlcm (6 * n) : ℚ) * nestHarmonic j) -
          2 * (s * (Dlcm (6 * n) : ℚ) * nestHarmonic (3 * n - j)) +
          (s * (Dlcm (6 * n) : ℚ) *
            (2 * ∑ r ∈ Finset.range j, (1 : ℚ) / (2 * r + 1))) -
          (s * (Dlcm (6 * n) : ℚ) *
            (2 * ∑ r ∈ Finset.range (4 * n),
              (1 : ℚ) / (2 * (j + r) + 1))) := by
    rw [nestM]
    dsimp [s]
    ring
  rw [heq]
  exact ZSub.sub_mem
    (ZSub.add_mem (ZSub.sub_mem hHj (ZSub.mul_mem htwo hHsub)) hoddShort)
    hoddLong

/-- A prime larger than `6n` but occurring below the top factorial contributes
one factor to the first integral factorial quotient in the scaled `A₂`. -/
lemma one_le_factorization_nestFactorialRatioNat (n j p : ℕ)
    (hj : j ≤ 3 * n) (hp : p.Prime) (hp6 : 6 * n < p)
    (hptop : p ≤ 8 * n + 2 * j) :
    1 ≤ (nestFactorialRatioNat (4 * n + j) j).factorization p := by
  let u := 4 * n + j
  have hv : j ≤ u := by omega
  have hn : 1 ≤ n := by
    by_contra h
    have : n = 0 := by omega
    omega
  have hu : u ≤ 7 * n := by omega
  have h2u : 2 * u ≤ 14 * n := by omega
  have hsq : 2 * u < p ^ 2 := by
    have hp' : 6 * n + 1 ≤ p := by omega
    nlinarith [sq_nonneg (p - (6 * n + 1)), sq_nonneg (n - 1)]
  have hbound (x : ℕ) (hx : x ≤ 2 * u) : Nat.log p x < 2 :=
    Nat.log_lt_of_lt_pow' (by norm_num) (lt_of_le_of_lt hx hsq)
  rw [nestFactorialRatioNat, Nat.factorization_div (factorial_ratio_dvd u j hv)]
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  change 1 ≤
    ((Nat.factorial (2 * u)).factorization p + (Nat.factorial j).factorization p) -
      ((Nat.factorial u).factorization p + (Nat.factorial (2 * j)).factorization p +
        (Nat.factorial (u - j)).factorization p)
  rw [Nat.factorization_factorial hp (hbound (2 * u) le_rfl),
    Nat.factorization_factorial hp (hbound j (by omega)),
    Nat.factorization_factorial hp (hbound u (by omega)),
    Nat.factorization_factorial hp (hbound (2 * j) (by omega)),
    Nat.factorization_factorial hp (hbound (u - j) (by omega))]
  norm_num
  have hjp : j / p = 0 := Nat.div_eq_of_lt (by omega)
  have h2jp : (2 * j) / p = 0 := Nat.div_eq_of_lt (by omega)
  have hujp : (u - j) / p = 0 := Nat.div_eq_of_lt (by dsimp [u]; omega)
  rw [hjp, h2jp, hujp]
  rcases lt_or_ge u p with hup | hpu
  · have huq : u / p = 0 := Nat.div_eq_of_lt hup
    have h2uq : (2 * u) / p = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [huq, h2uq]
  · have hu2p : u < 2 * p := by omega
    have huq : u / p = 1 := Nat.div_eq_of_lt_le (by simpa using hpu) hu2p
    have h2u3p : 2 * u < 3 * p := by omega
    have h2uq : (2 * u) / p = 2 := Nat.div_eq_of_lt_le (by omega) h2u3p
    rw [huq, h2uq]

/-- Carry-level version of the preceding lemma.  It applies also when `p` is
small but a power `p^a` is the long odd denominator. -/
lemma one_le_factorization_nestFactorialRatioNat_of_pow (n j p a : ℕ)
    (hj : j ≤ 3 * n) (hp : p.Prime) (ha : 1 ≤ a)
    (h6 : 6 * n < p ^ a) (htop : p ^ a ≤ 8 * n + 2 * j) :
    1 ≤ (nestFactorialRatioNat (4 * n + j) j).factorization p := by
  let u := 4 * n + j
  have hv : j ≤ u := by omega
  let b := 2 * u + 1
  have hbound (x : ℕ) (hx : x ≤ 2 * u) : Nat.log p x < b := by
    exact lt_of_le_of_lt (Nat.log_le_self p x) (by dsimp [b]; omega)
  rw [nestFactorialRatioNat, Nat.factorization_div (factorial_ratio_dvd u j hv)]
  rw [Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity),
    Nat.factorization_mul (by positivity) (by positivity)]
  change 1 ≤
    ((Nat.factorial (2 * u)).factorization p + (Nat.factorial j).factorization p) -
      ((Nat.factorial u).factorization p + (Nat.factorial (2 * j)).factorization p +
        (Nat.factorial (u - j)).factorization p)
  rw [Nat.factorization_factorial hp (hbound (2 * u) le_rfl),
    Nat.factorization_factorial hp (hbound j (by omega)),
    Nat.factorization_factorial hp (hbound u (by omega)),
    Nat.factorization_factorial hp (hbound (2 * j) (by omega)),
    Nat.factorization_factorial hp (hbound (u - j) (by omega)),
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  let L := fun i : ℕ => u / p ^ i + (2 * j) / p ^ i + (u - j) / p ^ i
  let R := fun i : ℕ => (2 * u) / p ^ i + j / p ^ i
  change 1 ≤ (∑ i ∈ Finset.Ico 1 b, R i) - ∑ i ∈ Finset.Ico 1 b, L i
  have ha_lt : a < b := by
    have hpow2 : 2 ^ a ≤ p ^ a := Nat.pow_le_pow_left hp.two_le a
    have haa : a < 2 ^ a := Nat.lt_two_pow_self
    dsimp [b]
    exact lt_of_lt_of_le (lt_of_lt_of_le haa hpow2) (htop.trans (by dsimp [u]; omega))
  have hamem : a ∈ Finset.Ico 1 b := Finset.mem_Ico.mpr ⟨ha, ha_lt⟩
  have hle : ∀ i ∈ Finset.Ico 1 b, L i ≤ R i := by
    intro i _
    exact factorial_ratio_floor_le u j (p ^ i) hv (pow_pos hp.pos i)
  have hstrict : L a < R a := by
    have hjd : j / p ^ a = 0 := Nat.div_eq_of_lt (by omega)
    have h2jd : (2 * j) / p ^ a = 0 := Nat.div_eq_of_lt (by omega)
    have h4nd : (u - j) / p ^ a = 0 := Nat.div_eq_of_lt (by dsimp [u]; omega)
    dsimp [L, R]
    rw [hjd, h2jd, h4nd]
    rcases lt_or_ge u (p ^ a) with hud | hdu
    · have huq : u / p ^ a = 0 := Nat.div_eq_of_lt hud
      have h2uq : (2 * u) / p ^ a = 1 :=
        Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [huq, h2uq]
      norm_num
    · have hu2d : u < 2 * p ^ a := by omega
      have huq : u / p ^ a = 1 := Nat.div_eq_of_lt_le (by simpa using hdu) hu2d
      have h2u3d : 2 * u < 3 * p ^ a := by
        have hn : 1 ≤ n := by omega
        dsimp [u]
        nlinarith
      have h2uq : (2 * u) / p ^ a = 2 :=
        Nat.div_eq_of_lt_le (by omega) h2u3d
      rw [huq, h2uq]
      norm_num
  have hsum : (∑ i ∈ Finset.Ico 1 b, L i) < ∑ i ∈ Finset.Ico 1 b, R i :=
    Finset.sum_lt_sum hle ⟨a, hamem, hstrict⟩
  omega
/-- Natural realization of the scaled positive `A₂` coefficient. -/
def nestA2ScaledNat (n j : ℕ) : ℕ :=
  2 * Nat.choose (3 * n) j * nestFactorialRatioNat (4 * n + j) j *
    nestFactorialRatioNat (3 * n) j

theorem nestA2ScaledNat_cast (n j : ℕ) (hj : j ≤ 3 * n) :
    (nestA2ScaledNat n j : ℚ) = (4 : ℚ) ^ (7 * n - j) * nestA2 n j := by
  rw [nestA2_scaled_factorization n j hj, nestA2ScaledNat,
    Nat.cast_mul, Nat.cast_mul, Nat.cast_mul,
    nestFactorialRatioNat_cast (4 * n + j) j (by omega),
    nestFactorialRatioNat_cast (3 * n) j hj]
  norm_num

/-- Every long odd logarithmic-derivative denominator divides the LCM times
the scaled `A₂` coefficient.  If its largest prime power exceeds `6n`, oddness
and the bound `<14n` force the denominator to be that prime power; the LCM
supplies all but one copy of the prime, and the top factorial quotient supplies
the last one. -/
theorem long_odd_dvd_Dlcm_mul_nestA2ScaledNat (n j r : ℕ)
    (hj : j ≤ 3 * n) (hr : r < 4 * n) :
    2 * (j + r) + 1 ∣ Dlcm (6 * n) * nestA2ScaledNat n j := by
  let m := 2 * (j + r) + 1
  have hmpos : m ≠ 0 := by dsimp [m]; omega
  have hR : Dlcm (6 * n) * nestA2ScaledNat n j ≠ 0 := by
    apply Nat.mul_ne_zero (Dlcm_ne_zero _)
    unfold nestA2ScaledNat
    have hF1ne := nestFactorialRatioNat_ne_zero (4 * n + j) j (by omega)
    have hF2ne := nestFactorialRatioNat_ne_zero (3 * n) j hj
    exact Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero (by norm_num)
      (Nat.choose_ne_zero hj)) hF1ne) hF2ne
  rw [← Nat.factorization_le_iff_dvd hmpos hR, Finsupp.le_def]
  intro p
  by_cases hp : p.Prime
  · let a := m.factorization p
    have ha : m.factorization p = a := rfl
    rw [Nat.factorization_mul (Dlcm_ne_zero _) (by
      exact Nat.ne_zero_of_mul_ne_zero_right hR)]
    change a ≤ (Dlcm (6 * n)).factorization p + (nestA2ScaledNat n j).factorization p
    by_cases hsmall : p ^ a ≤ 6 * n
    · exact (le_factorization_Dlcm hp hsmall).trans (Nat.le_add_right _ _)
    · have hn : 1 ≤ n := by
        by_contra h
        have : n = 0 := by omega
        omega
      have ha1 : 1 ≤ a := by
        by_contra h
        have : a = 0 := by omega
        rw [this, pow_zero] at hsmall
        omega
      have hpadvd : p ^ a ∣ m :=
        (hp.pow_dvd_iff_le_factorization hmpos).2 (by rw [ha])
      obtain ⟨q, hq⟩ := hpadvd
      have hmOdd : Odd m := by
        exact ⟨j + r, by dsimp [m]⟩
      have hpne2 : p ≠ 2 := by
        intro heq
        subst p
        have hpoweq : 2 ^ a = 2 * 2 ^ (a - 1) := by
          calc
            2 ^ a = 2 ^ (a - 1 + 1) := by congr 1 <;> omega
            _ = 2 * 2 ^ (a - 1) := by rw [pow_succ]; ring
        have h2m : 2 ∣ m := by
          refine ⟨2 ^ (a - 1) * q, ?_⟩
          rw [hq, hpoweq]
          ring
        obtain ⟨w, hw⟩ := h2m
        obtain ⟨v, hv⟩ := hmOdd
        omega
      have hqOdd : Odd q := by
        rw [← Nat.not_even_iff_odd]
        intro hqEven
        obtain ⟨w, hw⟩ := hqEven
        obtain ⟨v, hv⟩ := hmOdd
        rw [hw] at hq
        have heven : m = 2 * (p ^ a * w) := by
          rw [hq]
          ring
        omega
      have hq1 : q = 1 := by
        by_contra hne
        obtain ⟨t, ht⟩ := hqOdd
        have hq3 : 3 ≤ q := by omega
        have hmle : m ≤ 14 * n - 1 := by dsimp [m]; omega
        have h3 : 3 * p ^ a ≤ m := by
          rw [hq]
          nlinarith
        have : p ^ a ≤ 6 * n := by omega
        exact hsmall this
      have hmeq : m = p ^ a := by simpa [hq1] using hq
      have hp2 : 2 < p := by
        have := hp.two_le
        omega
      have hpred : p ^ (a - 1) ≤ 6 * n := by
        have hpow : p ^ (a - 1) * p = p ^ a := by
          rw [← pow_succ]
          congr 1
          omega
        have hmle : m ≤ 14 * n - 1 := by dsimp [m]; omega
        rw [← hmeq] at hpow
        have h3 : 3 * p ^ (a - 1) ≤ m := by
          rw [← hpow]
          have hp3 : 3 ≤ p := by omega
          calc
            3 * p ^ (a - 1) = p ^ (a - 1) * 3 := by ring
            _ ≤ p ^ (a - 1) * p := Nat.mul_le_mul_left _ hp3
        omega
      have hD : a - 1 ≤ (Dlcm (6 * n)).factorization p :=
        le_factorization_Dlcm hp hpred
      have hpTop : p ≤ 8 * n + 2 * j := by
        have hpm : p ≤ m := by
          rw [hmeq]
          exact Nat.le_pow ha1
        dsimp [m] at hpm
        omega
      have hF : 1 ≤ (nestFactorialRatioNat (4 * n + j) j).factorization p :=
        one_le_factorization_nestFactorialRatioNat_of_pow n j p a hj hp ha1
          (by omega) (by simpa [hmeq] using (show m ≤ 8 * n + 2 * j by dsimp [m]; omega))
      have hScaled : 1 ≤ (nestA2ScaledNat n j).factorization p := by
        unfold nestA2ScaledNat
        rw [Nat.factorization_mul (by
              exact Nat.mul_ne_zero (Nat.mul_ne_zero (by norm_num) (Nat.choose_ne_zero hj))
                (nestFactorialRatioNat_ne_zero (4 * n + j) j (by omega)))
              (nestFactorialRatioNat_ne_zero (3 * n) j hj),
          Nat.factorization_mul
            (Nat.mul_ne_zero (by norm_num) (Nat.choose_ne_zero hj))
            (nestFactorialRatioNat_ne_zero (4 * n + j) j (by omega)),
          Nat.factorization_mul (by norm_num) (Nat.choose_ne_zero hj)]
        change 1 ≤ (Nat.factorization 2) p + (Nat.choose (3 * n) j).factorization p +
          (nestFactorialRatioNat (4 * n + j) j).factorization p +
          (nestFactorialRatioNat (3 * n) j).factorization p
        omega
      omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- Kernel-checked long-odd term needed by the diagonal reduction. -/
theorem nestA2_long_odd_mem_ZSub (n j : ℕ) (hj : j ≤ 3 * n) (r : ℕ)
    (hr : r < 4 * n) :
    ((4 : ℚ) ^ (7 * n - j) * nestA2 n j) *
      (2 * (Dlcm (6 * n) : ℚ) / (2 * (j + r) + 1 : ℚ)) ∈ ZSub := by
  obtain ⟨c, hc⟩ := long_odd_dvd_Dlcm_mul_nestA2ScaledNat n j r hj hr
  rw [← nestA2ScaledNat_cast n j hj]
  refine (mem_ZSub_iff _).mpr ⟨2 * (c : ℤ), ?_⟩
  have hcQ := congrArg (fun x : ℕ => (x : ℚ)) hc
  push_cast at hcQ
  field_simp
  push_cast
  nlinarith [hcQ]

/-- The specialized simple-pole coefficient clearing, proved without a
literature hypothesis. -/
theorem nestA1_scaled_isInt (n j : ℕ) (hj : j ≤ 3 * n) :
    ∃ z : ℤ, (z : ℚ) =
      (4 : ℚ) ^ (7 * n - j) * (Dlcm (6 * n) : ℚ) * nestA1 n j := by
  exact nestA1_scaled_isInt_of_diagonal n
    (fun k hk => nestA2_diagonal_mem_of_long_odd n
      (fun i hi r hr => nestA2_long_odd_mem_ZSub n i hi r hr) k hk)
    j hj

/-- Unconditional conservative integrality of the concrete Nesterenko
numerator. -/
theorem nestCConcrete_scaled_isInt (n : ℕ) :
    ∃ z : ℤ, (z : ℚ) =
      (4 : ℚ) ^ (7 * n) * (Dlcm (6 * n) : ℚ) ^ 2 * nestCConcrete n := by
  exact nestC_scaled_isInt_of_A1_clearing nestA1 n fun j hj =>
    nestA1_scaled_isInt n j hj

end Catalan
