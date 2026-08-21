import RequestProject.Worthiness

/-!
# The corrected balanced two-row selection

Theorem 11.1 of the unconditional note (correcting Theorem 22.1 of the base note).

The input is, for each `n`, the pair of divided integer rows produced by the two successive
minima of the balanced rectangle, together with the exponential bounds (22.20)–(22.23) and the
determinant lower bound (22.25).  The parameter `r n ≥ 0` measures the imbalance
`r n = -(1/n) log μ₁,ₙ` and `ε n → 0` dominates all the normalized rate errors.

`exists_good_row` is the per-`n` selection (Cases A, B and C of the note, reorganized so that the
trichotomy is made separately for each `n`).
-/

namespace Catalan

open Filter Topology

/-! ### Elementary facts -/

lemma log_le_of_le_exp {v Y : ℝ} (hv : 0 < v) (h : v ≤ Real.exp Y) : Real.log v ≤ Y := by
  calc Real.log v ≤ Real.log (Real.exp Y) := Real.log_le_log hv h
    _ = Y := Real.log_exp Y

lemma le_log_of_exp_div_two_le {X v : ℝ} (h : Real.exp X / 2 ≤ v) :
    X - Real.log 2 ≤ Real.log v := by
  have hpos : (0 : ℝ) < Real.exp X / 2 := by positivity
  calc X - Real.log 2 = Real.log (Real.exp X / 2) := by
        rw [Real.log_div (Real.exp_ne_zero X) (by norm_num), Real.log_exp]
    _ ≤ Real.log v := Real.log_le_log hpos h

/-- The property required of the selected output row: nonzero denominator and linear form, a
denominator of size at least `e^D`, and a normalized linear form at most `Nm / D`. -/
def GoodRow (α D Nm : ℝ) (q p : ℤ) : Prop :=
  q ≠ 0 ∧ (q : ℝ) * α - (p : ℝ) ≠ 0 ∧ D ≤ Real.log |(q : ℝ)| ∧
    Real.log |(q : ℝ) * α - (p : ℝ)| / Real.log |(q : ℝ)| ≤ Nm / D

lemma goodRow_of_log_bounds {α D Nm : ℝ} {q p : ℤ} (hD : 0 < D) (hNm : 0 ≤ Nm)
    (hq : q ≠ 0) (hl : (q : ℝ) * α - (p : ℝ) ≠ 0)
    (h1 : D ≤ Real.log |(q : ℝ)|) (h2 : Real.log |(q : ℝ) * α - (p : ℝ)| ≤ Nm) :
    GoodRow α D Nm q p := by
  refine ⟨hq, hl, h1, ?_⟩
  rcases le_or_gt (Real.log |(q : ℝ) * α - (p : ℝ)|) 0 with h | h
  · have h3 : Real.log |(q : ℝ) * α - (p : ℝ)| / Real.log |(q : ℝ)| ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg h (by linarith)
    have h4 : (0 : ℝ) ≤ Nm / D := by positivity
    linarith
  · exact div_le_div₀ hNm h2 hD h1

lemma abs_int_cast_ne_zero {z : ℤ} (h : z ≠ 0) : (0 : ℝ) < |((z : ℤ) : ℝ)| := by
  have : ((z : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr h
  positivity

lemma int_ne_zero_of_log_pos {D : ℝ} {z : ℤ} (hD : 0 < D) (h : D ≤ Real.log |((z : ℤ) : ℝ)|) :
    z ≠ 0 := by
  intro hz
  rw [show ((z : ℤ) : ℝ) = 0 by exact_mod_cast congrArg (fun w : ℤ => (w : ℝ)) hz,
    abs_zero, Real.log_zero] at h
  linarith

/-! ### Case C: the first linear form vanishes -/

/-- Case C of the note: if `ℓ₁ = 0` (so `Q₁ ≠ 0` and `ℓ₂ ≠ 0` by nonvanishing of the determinant),
inflating the second row by a huge multiple of the first keeps the linear form and makes the
denominator as large as we please. -/
lemma good_row_of_L1_zero {α D Nm : ℝ} (Q1 Q2 P1 P2 : ℤ) (hD : 0 < D) (hNm : 0 < Nm)
    (hQ1 : Q1 ≠ 0) (hL1 : (Q1 : ℝ) * α - (P1 : ℝ) = 0) (hL2 : (Q2 : ℝ) * α - (P2 : ℝ) ≠ 0) :
    ∃ q p : ℤ, GoodRow α D Nm q p := by
  set L2 : ℝ := (Q2 : ℝ) * α - (P2 : ℝ) with hL2def
  set M : ℝ := max D (Real.log |L2| * D / Nm) with hMdef
  set T : ℤ := (⌈Real.exp M⌉₊ : ℤ) + |Q2| with hTdef
  set k : ℤ := if 0 ≤ Q1 then T else -T with hkdef
  have hTpos : 0 ≤ T := by
    have : (0 : ℤ) ≤ |Q2| := abs_nonneg _
    have h2 : (0 : ℤ) ≤ (⌈Real.exp M⌉₊ : ℤ) := Int.natCast_nonneg _
    omega
  have hkQ1 : k * Q1 = T * |Q1| := by
    rw [hkdef]
    split
    · rw [abs_of_nonneg (by assumption)]
    · rw [abs_of_neg (by omega)]
      ring
  have hQ1abs : (1 : ℤ) ≤ |Q1| := by
    rcases lt_trichotomy Q1 0 with h | h | h
    · rw [abs_of_neg h]; omega
    · exact absurd h hQ1
    · rw [abs_of_pos h]; omega
  have hlowZ : (⌈Real.exp M⌉₊ : ℤ) ≤ |Q2 + k * Q1| := by
    have h1 : |k * Q1| ≤ |Q2 + k * Q1| + |Q2| := by
      have h := abs_sub (Q2 + k * Q1) Q2
      simpa using h
    have h2 : |k * Q1| = T * |Q1| := by
      rw [hkQ1, abs_mul, abs_of_nonneg hTpos, abs_abs]
    have h3 : T ≤ T * |Q1| := le_mul_of_one_le_right hTpos hQ1abs
    rw [h2] at h1
    have hT : T = (⌈Real.exp M⌉₊ : ℤ) + |Q2| := hTdef
    linarith
  have hexpM : Real.exp M ≤ |((Q2 + k * Q1 : ℤ) : ℝ)| := by
    have h1 : Real.exp M ≤ (⌈Real.exp M⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈Real.exp M⌉₊ : ℤ) : ℝ) ≤ ((|Q2 + k * Q1| : ℤ) : ℝ) := by exact_mod_cast hlowZ
    have h3 : ((|Q2 + k * Q1| : ℤ) : ℝ) = |((Q2 + k * Q1 : ℤ) : ℝ)| := by
      push_cast [Int.cast_abs]
      ring
    rw [h3] at h2
    exact le_trans (by exact_mod_cast h1) h2
  have hlogq : M ≤ Real.log |((Q2 + k * Q1 : ℤ) : ℝ)| := by
    have := Real.log_le_log (Real.exp_pos M) hexpM
    rwa [Real.log_exp] at this
  have hMD : D ≤ M := le_max_left _ _
  have hqpos : 0 < Real.log |((Q2 + k * Q1 : ℤ) : ℝ)| := lt_of_lt_of_le hD (hMD.trans hlogq)
  have hval : ((Q2 + k * Q1 : ℤ) : ℝ) * α - ((P2 + k * P1 : ℤ) : ℝ) = L2 := by
    rw [hL2def]
    push_cast
    linear_combination (k : ℝ) * hL1
  refine ⟨Q2 + k * Q1, P2 + k * P1, ?_, ?_, hMD.trans hlogq, ?_⟩
  · exact int_ne_zero_of_log_pos hD (hMD.trans hlogq)
  · rw [hval]; exact hL2
  · rw [hval]
    rw [div_le_div_iff₀ hqpos hD]
    rcases le_or_gt (Real.log |L2|) 0 with h | h
    · nlinarith
    · have h1 : Real.log |L2| * D / Nm ≤ M := le_max_right _ _
      have h2 : Real.log |L2| * D / Nm ≤ Real.log |((Q2 + k * Q1 : ℤ) : ℝ)| := h1.trans hlogq
      rw [div_le_iff₀ hNm] at h2
      nlinarith

/-! ### Case B: a reduced combination -/

/-- A nonzero integer combination with a controlled linear form: there is `m` with
`0 < |ℓ₂ - m ℓ₁| ≤ (3/2)|ℓ₁|`. -/
lemma exists_reduction {L1 L2 : ℝ} (hL1 : L1 ≠ 0) :
    ∃ m : ℤ, L2 - m * L1 ≠ 0 ∧ |L2 - m * L1| ≤ 3 / 2 * |L1| := by
  set m0 : ℤ := round (L2 / L1) with hm0
  have habs : |L2 / L1 - m0| ≤ 1 / 2 := by
    have := abs_sub_round (L2 / L1)
    simpa [hm0] using this
  have hkey : |L2 - m0 * L1| ≤ 1 / 2 * |L1| := by
    have hrw : L2 - (m0 : ℝ) * L1 = (L2 / L1 - m0) * L1 := by
      field_simp
    rw [hrw, abs_mul]
    exact mul_le_mul_of_nonneg_right habs (abs_nonneg _)
  by_cases hz : L2 - (m0 : ℝ) * L1 = 0
  · have hval : L2 - ((m0 + 1 : ℤ) : ℝ) * L1 = -L1 := by
      push_cast
      linear_combination hz
    refine ⟨m0 + 1, ?_, ?_⟩
    · rw [hval]; simpa using hL1
    · rw [hval, abs_neg]
      linarith [abs_nonneg L1]
  · exact ⟨m0, hz, by linarith [abs_nonneg L1]⟩

lemma good_row_case_B {α H F D Nm r e nR : ℝ} (Q1 Q2 P1 P2 : ℤ)
    (hD : 0 < D) (hNm : 0 < Nm) (hr : 0 ≤ r) (he : 0 < e) (he9 : e ≤ 1 / 9) (hn : 0 < nR)
    (hq1 : |(Q1 : ℝ)| ≤ Real.exp ((H - r + e) * nR))
    (hl1 : |(Q1 : ℝ) * α - (P1 : ℝ)| ≤ Real.exp ((F - r + e) * nR))
    (hdet : Real.exp ((H + F - e) * nR) ≤ |((Q1 * P2 - Q2 * P1 : ℤ) : ℝ)|)
    (h3 : 3 ≤ Real.exp (Real.sqrt e * nR))
    (hDle : D ≤ (H - 2 * e) * nR - Real.log 2)
    (hNmge : (F + e) * nR + Real.log (3 / 2) ≤ Nm)
    (hrbig : Real.sqrt e < r) (hL1z : (Q1 : ℝ) * α - (P1 : ℝ) ≠ 0) :
    ∃ q p : ℤ, GoodRow α D Nm q p := by
  set L1 : ℝ := (Q1 : ℝ) * α - (P1 : ℝ) with hL1def
  set L2 : ℝ := (Q2 : ℝ) * α - (P2 : ℝ) with hL2def
  set Dt : ℝ := ((Q1 * P2 - Q2 * P1 : ℤ) : ℝ) with hDtdef
  obtain ⟨m, hm0, hmle⟩ := exists_reduction (L1 := L1) (L2 := L2) hL1z
  have hL1pos : 0 < |L1| := abs_pos.mpr hL1z
  have hident : ((Q2 - m * Q1 : ℤ) : ℝ) * L1 - (Q1 : ℝ) * (L2 - m * L1) = Dt := by
    rw [hL1def, hL2def, hDtdef]
    push_cast
    ring
  have hQ1L1 : |(Q1 : ℝ)| * |L1| ≤ Real.exp ((H + F - 2 * r + 2 * e) * nR) := by
    have hmul := mul_le_mul hq1 hl1 (abs_nonneg _) (by positivity)
    rw [← Real.exp_add] at hmul
    refine hmul.trans (Real.exp_le_exp.mpr ?_)
    ring_nf
    linarith
  have hsqe : Real.sqrt e * Real.sqrt e = e := Real.mul_self_sqrt he.le
  have hsq0 : 0 ≤ Real.sqrt e := Real.sqrt_nonneg e
  have hsqsmall : Real.sqrt e ≤ 1 / 3 := by nlinarith
  have hdom : 3 * (|(Q1 : ℝ)| * |L1|) ≤ |Dt| := by
    have hexp : Real.exp ((H + F - 2 * r + 2 * e) * nR) * Real.exp (Real.sqrt e * nR)
        ≤ Real.exp ((H + F - e) * nR) := by
      rw [← Real.exp_add]
      refine Real.exp_le_exp.mpr ?_
      have h1 : 3 * e ≤ Real.sqrt e := by nlinarith
      nlinarith
    have hp : (0 : ℝ) < Real.exp ((H + F - 2 * r + 2 * e) * nR) := Real.exp_pos _
    have hstep : Real.exp ((H + F - 2 * r + 2 * e) * nR) * 3
        ≤ Real.exp ((H + F - 2 * r + 2 * e) * nR) * Real.exp (Real.sqrt e * nR) :=
      mul_le_mul_of_nonneg_left h3 hp.le
    linarith
  have hqp : |Dt| / 2 ≤ |((Q2 - m * Q1 : ℤ) : ℝ)| * |L1| := by
    have h1 : |Dt| ≤ |((Q2 - m * Q1 : ℤ) : ℝ)| * |L1| + |(Q1 : ℝ)| * |L2 - m * L1| := by
      calc |Dt| = |((Q2 - m * Q1 : ℤ) : ℝ) * L1 - (Q1 : ℝ) * (L2 - m * L1)| := by rw [hident]
        _ ≤ |((Q2 - m * Q1 : ℤ) : ℝ) * L1| + |(Q1 : ℝ) * (L2 - m * L1)| := abs_sub _ _
        _ = |((Q2 - m * Q1 : ℤ) : ℝ)| * |L1| + |(Q1 : ℝ)| * |L2 - m * L1| := by
            rw [abs_mul, abs_mul]
    have h2 : |(Q1 : ℝ)| * |L2 - m * L1| ≤ 3 / 2 * (|(Q1 : ℝ)| * |L1|) := by
      have := mul_le_mul_of_nonneg_left hmle (abs_nonneg (Q1 : ℝ))
      linarith
    linarith
  have hL1le : |L1| ≤ Real.exp ((F + e) * nR) := by
    refine hl1.trans (Real.exp_le_exp.mpr ?_)
    nlinarith
  have hqlow : Real.exp ((H - 2 * e) * nR) / 2 ≤ |((Q2 - m * Q1 : ℤ) : ℝ)| := by
    have h2 : Real.exp ((H + F - e) * nR) / 2 ≤ |((Q2 - m * Q1 : ℤ) : ℝ)| * |L1| := by
      linarith
    have h3' : |((Q2 - m * Q1 : ℤ) : ℝ)| * |L1|
        ≤ |((Q2 - m * Q1 : ℤ) : ℝ)| * Real.exp ((F + e) * nR) :=
      mul_le_mul_of_nonneg_left hL1le (abs_nonneg _)
    have hexp : Real.exp ((H + F - e) * nR)
        = Real.exp ((H - 2 * e) * nR) * Real.exp ((F + e) * nR) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp] at h2
    have hpos : (0 : ℝ) < Real.exp ((F + e) * nR) := Real.exp_pos _
    have h5 : Real.exp ((H - 2 * e) * nR) / 2 * Real.exp ((F + e) * nR)
        ≤ |((Q2 - m * Q1 : ℤ) : ℝ)| * Real.exp ((F + e) * nR) := by linarith
    exact le_of_mul_le_mul_right h5 hpos
  have hlogq : D ≤ Real.log |((Q2 - m * Q1 : ℤ) : ℝ)| := by
    have := le_log_of_exp_div_two_le hqlow
    linarith
  have hval : ((Q2 - m * Q1 : ℤ) : ℝ) * α - ((P2 - m * P1 : ℤ) : ℝ) = L2 - m * L1 := by
    rw [hL1def, hL2def]
    push_cast
    ring
  refine ⟨Q2 - m * Q1, P2 - m * P1,
    goodRow_of_log_bounds hD hNm.le (int_ne_zero_of_log_pos hD hlogq) (by rw [hval]; exact hm0)
      hlogq ?_⟩
  rw [hval]
  have h1 : Real.log |L2 - m * L1| ≤ Real.log (3 / 2 * |L1|) :=
    Real.log_le_log (abs_pos.mpr hm0) hmle
  have h2 : Real.log (3 / 2 * |L1|) = Real.log (3 / 2) + Real.log |L1| := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hL1pos)]
  have h3' : Real.log |L1| ≤ (F + e) * nR := log_le_of_le_exp hL1pos hL1le
  linarith

/-! ### Case A: a balanced pair -/

lemma good_row_case_A {α H F D Nm r e nR : ℝ} (Q1 Q2 P1 P2 : ℤ)
    (hD : 0 < D) (hNm : 0 < Nm) (hr : 0 ≤ r) (hn : 0 < nR)
    (hl1 : |(Q1 : ℝ) * α - (P1 : ℝ)| ≤ Real.exp ((F - r + e) * nR))
    (hl2 : |(Q2 : ℝ) * α - (P2 : ℝ)| ≤ Real.exp ((F + r + e) * nR))
    (hdet : Real.exp ((H + F - e) * nR) ≤ |((Q1 * P2 - Q2 * P1 : ℤ) : ℝ)|)
    (hDle : D ≤ (H - Real.sqrt e - 2 * e) * nR - Real.log 2)
    (hNmge : (F + Real.sqrt e + e) * nR ≤ Nm)
    (hrle : r ≤ Real.sqrt e) (hL1z : (Q1 : ℝ) * α - (P1 : ℝ) ≠ 0) :
    ∃ q p : ℤ, GoodRow α D Nm q p := by
  set L1 : ℝ := (Q1 : ℝ) * α - (P1 : ℝ) with hL1def
  set L2 : ℝ := (Q2 : ℝ) * α - (P2 : ℝ) with hL2def
  set Dt : ℝ := ((Q1 * P2 - Q2 * P1 : ℤ) : ℝ) with hDtdef
  have hcross : (Q1 : ℝ) * L2 - (Q2 : ℝ) * L1 = -Dt := by
    rw [hL1def, hL2def, hDtdef]
    push_cast
    ring
  have hsplit : |Dt| ≤ |(Q1 : ℝ)| * |L2| + |(Q2 : ℝ)| * |L1| := by
    calc |Dt| = |(Q1 : ℝ) * L2 - (Q2 : ℝ) * L1| := by rw [hcross, abs_neg]
      _ ≤ |(Q1 : ℝ) * L2| + |(Q2 : ℝ) * L1| := abs_sub _ _
      _ = |(Q1 : ℝ)| * |L2| + |(Q2 : ℝ)| * |L1| := by rw [abs_mul, abs_mul]
  have hbig : Real.exp ((H - Real.sqrt e - 2 * e) * nR) / 2 ≤ |(Q1 : ℝ)| ∨
      Real.exp ((H - Real.sqrt e - 2 * e) * nR) / 2 ≤ |(Q2 : ℝ)| := by
    rcases le_or_gt (|Dt| / 2) (|(Q1 : ℝ)| * |L2|) with hA | hB
    · left
      have h1 : Real.exp ((H + F - e) * nR) / 2 ≤ |(Q1 : ℝ)| * Real.exp ((F + r + e) * nR) := by
        have := mul_le_mul_of_nonneg_left hl2 (abs_nonneg (Q1 : ℝ))
        linarith
      have hexp : Real.exp ((H + F - e) * nR)
          = Real.exp ((H - r - 2 * e) * nR) * Real.exp ((F + r + e) * nR) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp] at h1
      have hpos : (0 : ℝ) < Real.exp ((F + r + e) * nR) := Real.exp_pos _
      have h2 : Real.exp ((H - r - 2 * e) * nR) / 2 ≤ |(Q1 : ℝ)| := by
        have h5 : Real.exp ((H - r - 2 * e) * nR) / 2 * Real.exp ((F + r + e) * nR)
            ≤ |(Q1 : ℝ)| * Real.exp ((F + r + e) * nR) := by linarith
        exact le_of_mul_le_mul_right h5 hpos
      have hmono : Real.exp ((H - Real.sqrt e - 2 * e) * nR)
          ≤ Real.exp ((H - r - 2 * e) * nR) := by
        refine Real.exp_le_exp.mpr ?_
        nlinarith
      linarith
    · right
      have hB' : |Dt| / 2 ≤ |(Q2 : ℝ)| * |L1| := by linarith
      have h1 : Real.exp ((H + F - e) * nR) / 2 ≤ |(Q2 : ℝ)| * Real.exp ((F - r + e) * nR) := by
        have := mul_le_mul_of_nonneg_left hl1 (abs_nonneg (Q2 : ℝ))
        linarith
      have hexp : Real.exp ((H + F - e) * nR)
          = Real.exp ((H + r - 2 * e) * nR) * Real.exp ((F - r + e) * nR) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp] at h1
      have hpos : (0 : ℝ) < Real.exp ((F - r + e) * nR) := Real.exp_pos _
      have h2 : Real.exp ((H + r - 2 * e) * nR) / 2 ≤ |(Q2 : ℝ)| := by
        have h5 : Real.exp ((H + r - 2 * e) * nR) / 2 * Real.exp ((F - r + e) * nR)
            ≤ |(Q2 : ℝ)| * Real.exp ((F - r + e) * nR) := by linarith
        exact le_of_mul_le_mul_right h5 hpos
      have hmono : Real.exp ((H - Real.sqrt e - 2 * e) * nR)
          ≤ Real.exp ((H + r - 2 * e) * nR) := by
        refine Real.exp_le_exp.mpr ?_
        have : 0 ≤ Real.sqrt e := Real.sqrt_nonneg e
        nlinarith
      linarith
  have hL1bound : Real.log |L1| ≤ Nm := by
    have hle : |L1| ≤ Real.exp ((F + Real.sqrt e + e) * nR) := by
      refine hl1.trans (Real.exp_le_exp.mpr ?_)
      have : 0 ≤ Real.sqrt e := Real.sqrt_nonneg e
      nlinarith
    have := log_le_of_le_exp (abs_pos.mpr hL1z) hle
    linarith
  rcases hbig with hQ1 | hQ2
  · have hlogq : D ≤ Real.log |(Q1 : ℝ)| := by
      have := le_log_of_exp_div_two_le hQ1
      linarith
    exact ⟨Q1, P1, goodRow_of_log_bounds hD hNm.le (int_ne_zero_of_log_pos hD hlogq) hL1z hlogq
      hL1bound⟩
  · by_cases hL2z : L2 = 0
    · -- the second linear form vanishes: add the first row, choosing a non-cancelling sign
      set s : ℤ := if 0 ≤ Q2 * Q1 then 1 else -1 with hsdef
      have hsign : (0 : ℤ) ≤ Q2 * (s * Q1) := by
        rw [hsdef]
        split
        · simpa using (by assumption : (0 : ℤ) ≤ Q2 * Q1)
        · have h := not_le.mp (by assumption : ¬ (0 : ℤ) ≤ Q2 * Q1)
          nlinarith
      have hsignR : (0 : ℝ) ≤ (Q2 : ℝ) * ((s : ℝ) * (Q1 : ℝ)) := by
        have := (Int.cast_le (R := ℝ)).mpr hsign
        push_cast at this
        linarith
      have hcastsum : ((Q2 + s * Q1 : ℤ) : ℝ) = (Q2 : ℝ) + (s : ℝ) * (Q1 : ℝ) := by push_cast; ring
      have hcast : |(Q2 : ℝ)| ≤ |((Q2 + s * Q1 : ℤ) : ℝ)| := by
        rw [hcastsum]
        have hsq : (Q2 : ℝ) ^ 2 ≤ ((Q2 : ℝ) + (s : ℝ) * (Q1 : ℝ)) ^ 2 := by nlinarith
        calc |(Q2 : ℝ)| = Real.sqrt ((Q2 : ℝ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
          _ ≤ Real.sqrt (((Q2 : ℝ) + (s : ℝ) * (Q1 : ℝ)) ^ 2) := Real.sqrt_le_sqrt hsq
          _ = |(Q2 : ℝ) + (s : ℝ) * (Q1 : ℝ)| := Real.sqrt_sq_eq_abs _
      have hq2pos : 0 < |(Q2 : ℝ)| := by
        have h1 : D ≤ Real.log |(Q2 : ℝ)| := by
          have := le_log_of_exp_div_two_le hQ2
          linarith
        by_contra hc
        push_neg at hc
        have hz : |(Q2 : ℝ)| = 0 := le_antisymm hc (abs_nonneg _)
        rw [hz, Real.log_zero] at h1
        linarith
      have hlogq : D ≤ Real.log |((Q2 + s * Q1 : ℤ) : ℝ)| := by
        have h1 : D ≤ Real.log |(Q2 : ℝ)| := by
          have := le_log_of_exp_div_two_le hQ2
          linarith
        exact h1.trans (Real.log_le_log hq2pos hcast)
      have hval : ((Q2 + s * Q1 : ℤ) : ℝ) * α - ((P2 + s * P1 : ℤ) : ℝ) = L2 + s * L1 := by
        rw [hL1def, hL2def]; push_cast; ring
      have hsne : (s : ℝ) ≠ 0 := by rw [hsdef]; split <;> norm_num
      have habs1 : |(s : ℝ) * L1| = |L1| := by
        rw [abs_mul, hsdef]
        split <;> norm_num
      refine ⟨Q2 + s * Q1, P2 + s * P1,
        goodRow_of_log_bounds hD hNm.le (int_ne_zero_of_log_pos hD hlogq) ?_ hlogq ?_⟩
      · rw [hval, hL2z, zero_add]
        exact mul_ne_zero hsne hL1z
      · rw [hval, hL2z, zero_add, habs1]
        exact hL1bound
    · have hlogq : D ≤ Real.log |(Q2 : ℝ)| := by
        have := le_log_of_exp_div_two_le hQ2
        linarith
      have hL2bound : Real.log |L2| ≤ Nm := by
        have hle : |L2| ≤ Real.exp ((F + Real.sqrt e + e) * nR) := by
          refine hl2.trans (Real.exp_le_exp.mpr ?_)
          nlinarith
        have := log_le_of_le_exp (abs_pos.mpr hL2z) hle
        linarith
      exact ⟨Q2, P2, goodRow_of_log_bounds hD hNm.le (int_ne_zero_of_log_pos hD hlogq) hL2z hlogq
        hL2bound⟩

/-! ### The per-`n` selection -/

/-- The heart of Theorem 11.1: from the two rows produced by the successive minima one can select
a single integer row whose denominator is large and whose normalized linear form is small.  The
three branches are Cases C, B and A of the note. -/
theorem exists_good_row {α H F : ℝ} (hF : 0 < F) (Q1 Q2 P1 P2 : ℤ) {r e nR : ℝ}
    (hr : 0 ≤ r) (he : 0 < e) (he9 : e ≤ 1 / 9) (hn : 0 < nR)
    (hq1 : |(Q1 : ℝ)| ≤ Real.exp ((H - r + e) * nR))
    (hl1 : |(Q1 : ℝ) * α - (P1 : ℝ)| ≤ Real.exp ((F - r + e) * nR))
    (hl2 : |(Q2 : ℝ) * α - (P2 : ℝ)| ≤ Real.exp ((F + r + e) * nR))
    (hdet : Real.exp ((H + F - e) * nR) ≤ |((Q1 * P2 - Q2 * P1 : ℤ) : ℝ)|)
    (h3 : 3 ≤ Real.exp (Real.sqrt e * nR))
    (hD : 0 < (H - Real.sqrt e - 2 * e) * nR - Real.log 2) :
    ∃ q p : ℤ, GoodRow α ((H - Real.sqrt e - 2 * e) * nR - Real.log 2)
      ((F + Real.sqrt e + e) * nR + Real.log (3 / 2)) q p := by
  have hsq : 0 ≤ Real.sqrt e := Real.sqrt_nonneg e
  have hlog32 : 0 ≤ Real.log (3 / 2) := Real.log_nonneg (by norm_num)
  have hNm : 0 < (F + Real.sqrt e + e) * nR + Real.log (3 / 2) := by
    have : 0 < (F + Real.sqrt e + e) * nR := by positivity
    linarith
  have hDtpos : 0 < |((Q1 * P2 - Q2 * P1 : ℤ) : ℝ)| := lt_of_lt_of_le (Real.exp_pos _) hdet
  by_cases hL1z : (Q1 : ℝ) * α - (P1 : ℝ) = 0
  · -- Case C
    have hcross : (Q1 : ℝ) * ((Q2 : ℝ) * α - (P2 : ℝ)) = -((Q1 * P2 - Q2 * P1 : ℤ) : ℝ) := by
      push_cast
      push_cast at hL1z
      linear_combination (Q2 : ℝ) * hL1z
    have hQ1ne : Q1 ≠ 0 := by
      intro h
      rw [show ((Q1 : ℝ)) = 0 by exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) h,
        zero_mul] at hcross
      have hz : ((Q1 * P2 - Q2 * P1 : ℤ) : ℝ) = 0 := by linarith
      rw [hz, abs_zero] at hDtpos
      exact lt_irrefl _ hDtpos
    have hL2ne : (Q2 : ℝ) * α - (P2 : ℝ) ≠ 0 := by
      intro h
      rw [h, mul_zero] at hcross
      have hz : ((Q1 * P2 - Q2 * P1 : ℤ) : ℝ) = 0 := by linarith
      rw [hz, abs_zero] at hDtpos
      exact lt_irrefl _ hDtpos
    exact good_row_of_L1_zero Q1 Q2 P1 P2 hD hNm hQ1ne hL1z hL2ne
  · by_cases hrbig : Real.sqrt e < r
    · exact good_row_case_B Q1 Q2 P1 P2 hD hNm hr he he9 hn hq1 hl1 hdet h3
        (by nlinarith) (by nlinarith) hrbig hL1z
    · push_neg at hrbig
      exact good_row_case_A Q1 Q2 P1 P2 hD hNm hr hn hl1 hl2 hdet (by linarith) (by linarith)
        hrbig hL1z


/-! ### Theorem 11.1 -/

/-- The denominator scale of the selected rows. -/
noncomputable def Dfun (H : ℝ) (ε : ℕ → ℝ) (n : ℕ) : ℝ :=
  (H - Real.sqrt (ε n) - 2 * ε n) * n - Real.log 2

/-- The linear-form scale of the selected rows. -/
noncomputable def Nfun (F : ℝ) (ε : ℕ → ℝ) (n : ℕ) : ℝ :=
  (F + Real.sqrt (ε n) + ε n) * n + Real.log (3 / 2)

lemma tendsto_sqrt_eps {ε : ℕ → ℝ} (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => Real.sqrt (ε n)) atTop (𝓝 0) := by
  have := (Real.continuous_sqrt.tendsto 0).comp hε0
  rw [Real.sqrt_zero] at this
  change Tendsto ((fun x : ℝ => Real.sqrt x) ∘ ε) atTop (𝓝 0)
  exact this

lemma tendsto_Dfun_div {H : ℝ} {ε : ℕ → ℝ} (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Dfun H ε n / n) atTop (𝓝 H) := by
  have h1 : Tendsto (fun n : ℕ => (H - Real.sqrt (ε n) - 2 * ε n) - Real.log 2 / n) atTop
      (𝓝 (H - 0 - 2 * 0 - 0)) := by
    exact ((tendsto_const_nhds.sub (tendsto_sqrt_eps hε0)).sub
      (tendsto_const_nhds.mul hε0)).sub (tendsto_const_div_atTop_nhds_zero_nat _)
  have h2 : Tendsto (fun n : ℕ => (H - Real.sqrt (ε n) - 2 * ε n) - Real.log 2 / n) atTop (𝓝 H) := by
    simpa using h1
  refine h2.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Dfun]
  field_simp

lemma tendsto_Nfun_div {F : ℝ} {ε : ℕ → ℝ} (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Nfun F ε n / n) atTop (𝓝 F) := by
  have h1 : Tendsto (fun n : ℕ => (F + Real.sqrt (ε n) + ε n) + Real.log (3 / 2) / n) atTop
      (𝓝 (F + 0 + 0 + 0)) :=
    ((tendsto_const_nhds.add (tendsto_sqrt_eps hε0)).add hε0).add
      (tendsto_const_div_atTop_nhds_zero_nat _)
  have h2 : Tendsto (fun n : ℕ => (F + Real.sqrt (ε n) + ε n) + Real.log (3 / 2) / n) atTop
      (𝓝 F) := by simpa using h1
  refine h2.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Nfun]
  field_simp

lemma tendsto_ratio {H F : ℝ} {ε : ℕ → ℝ} (hH : 0 < H) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Nfun F ε n / Dfun H ε n) atTop (𝓝 (F / H)) := by
  have hdiv := (tendsto_Nfun_div (F := F) hε0).div (tendsto_Dfun_div (H := H) hε0) (ne_of_gt hH)
  refine hdiv.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hnR : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < n := by exact_mod_cast hn
    exact ne_of_gt this
  simp only [Pi.div_apply]
  rw [div_div_div_cancel_right₀]
  exact hnR

lemma tendsto_Dfun_atTop {H : ℝ} {ε : ℕ → ℝ} (hH : 0 < H) (hε0 : Tendsto ε atTop (𝓝 0)) :
    Tendsto (Dfun H ε) atTop atTop := by
  have hcoef : Tendsto (fun n : ℕ => H - Real.sqrt (ε n) - 2 * ε n) atTop (𝓝 (H - 0 - 2 * 0)) :=
    (tendsto_const_nhds.sub (tendsto_sqrt_eps hε0)).sub (tendsto_const_nhds.mul hε0)
  have hcoef' : ∀ᶠ n in atTop, H / 2 ≤ H - Real.sqrt (ε n) - 2 * ε n := by
    have h := hcoef.eventually
      (eventually_ge_nhds (show H / 2 < H - 0 - 2 * 0 by linarith))
    filter_upwards [h] with n hn using hn
  refine tendsto_atTop_mono' _ ?_ (Filter.tendsto_atTop_add_const_right _ (-Real.log 2)
    (Filter.Tendsto.const_mul_atTop (by linarith : (0:ℝ) < H / 2) tendsto_natCast_atTop_atTop))
  filter_upwards [hcoef', Filter.eventually_ge_atTop 0] with n hn _
  have hnn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rw [Dfun]
  nlinarith

/-- Theorem 11.1: the corrected balanced two-row selection.  From the successive-minima data one
obtains an admissible approximation sequence of worthiness at least `1 - F/H`. -/
theorem two_row_selection {α H F : ℝ} (hH : 0 < H) (hF : 0 < F)
    (Q1 Q2 P1 P2 : ℕ → ℤ) (r ε : ℕ → ℝ)
    (hr : ∀ n, 0 ≤ r n) (hε : ∀ n, 0 < ε n) (hε0 : Tendsto ε atTop (𝓝 0))
    (hεn : Tendsto (fun n : ℕ => Real.sqrt (ε n) * n) atTop atTop)
    (hq1 : ∀ᶠ n in atTop, |(Q1 n : ℝ)| ≤ Real.exp ((H - r n + ε n) * n))
    (hl1 : ∀ᶠ n in atTop, |(Q1 n : ℝ) * α - (P1 n : ℝ)| ≤ Real.exp ((F - r n + ε n) * n))
    (hl2 : ∀ᶠ n in atTop, |(Q2 n : ℝ) * α - (P2 n : ℝ)| ≤ Real.exp ((F + r n + ε n) * n))
    (hdet : ∀ᶠ n in atTop,
      Real.exp ((H + F - ε n) * n) ≤ |((Q1 n * P2 n - Q2 n * P1 n : ℤ) : ℝ)|) :
    ∃ q p : ℕ → ℤ, IsAdmissible α q p ∧ ((1 - F / H : ℝ) : EReal) ≤ worthiness α q p := by
  have key : ∀ n : ℕ, ((ε n ≤ 1 / 9 ∧ (0 : ℝ) < n ∧ 3 ≤ Real.exp (Real.sqrt (ε n) * n) ∧
      0 < Dfun H ε n) ∧ (|(Q1 n : ℝ)| ≤ Real.exp ((H - r n + ε n) * n) ∧
      |(Q1 n : ℝ) * α - (P1 n : ℝ)| ≤ Real.exp ((F - r n + ε n) * n) ∧
      |(Q2 n : ℝ) * α - (P2 n : ℝ)| ≤ Real.exp ((F + r n + ε n) * n) ∧
      Real.exp ((H + F - ε n) * n) ≤ |((Q1 n * P2 n - Q2 n * P1 n : ℤ) : ℝ)|)) →
      ∃ qp : ℤ × ℤ, GoodRow α (Dfun H ε n) (Nfun F ε n) qp.1 qp.2 := by
    rintro n ⟨⟨h2, h3, h4, h5⟩, hb1, hb2, hb3, hb4⟩
    obtain ⟨qq, pp, hgr⟩ := exists_good_row (α := α) (H := H) (F := F) hF
      (Q1 n) (Q2 n) (P1 n) (P2 n) (hr n) (hε n) h2 h3 hb1 hb2 hb3 hb4 h4 h5
    exact ⟨(qq, pp), hgr⟩
  choose! f hf using key
  refine ⟨fun n => (f n).1, fun n => (f n).2, ?_, ?_⟩ <;>
  · have hDinf := tendsto_Dfun_atTop (H := H) (ε := ε) hH hε0
    have hcond0 : ∀ᶠ n in atTop, ε n ≤ 1 / 9 ∧ (0 : ℝ) < n ∧
        3 ≤ Real.exp (Real.sqrt (ε n) * n) ∧ 0 < Dfun H ε n := by
      have he9 : ∀ᶠ n in atTop, ε n ≤ 1 / 9 := by
        have := hε0.eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1 / 9))
        simpa using this
      have hnpos : ∀ᶠ n : ℕ in atTop, (0 : ℝ) < (n : ℝ) := by
        filter_upwards [Filter.eventually_gt_atTop 0] with n hn
        exact_mod_cast hn
      have h3ev : ∀ᶠ n in atTop, 3 ≤ Real.exp (Real.sqrt (ε n) * n) := by
        filter_upwards [hεn.eventually_ge_atTop (Real.log 3)] with n hn
        calc (3 : ℝ) = Real.exp (Real.log 3) := (Real.exp_log (by norm_num)).symm
          _ ≤ Real.exp (Real.sqrt (ε n) * n) := Real.exp_le_exp.mpr hn
      have hDev : ∀ᶠ n in atTop, 0 < Dfun H ε n := hDinf.eventually_gt_atTop 0
      filter_upwards [he9, hnpos, h3ev, hDev] with n a b c d
      exact ⟨a, b, c, d⟩
    have hcond := hcond0.and (hq1.and (hl1.and (hl2.and hdet)))
    have hgood : ∀ᶠ n in atTop, GoodRow α (Dfun H ε n) (Nfun F ε n) (f n).1 (f n).2 := by
      filter_upwards [hcond] with n hn
      exact hf n ⟨hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2⟩
    have hadm : IsAdmissible α (fun n => (f n).1) (fun n => (f n).2) := by
      refine ⟨hgood.mono (fun n h => h.1), hgood.mono (fun n h => h.2.1), ?_⟩
      refine tendsto_atTop_mono' _ ?_ (Real.tendsto_exp_atTop.comp hDinf)
      filter_upwards [hgood] with n hn
      have hq0 : ((f n).1 : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn.1
      have hpos : 0 < |((f n).1 : ℝ)| := abs_pos.mpr hq0
      have := Real.exp_le_exp.mpr hn.2.2.1
      rwa [Real.exp_log hpos] at this
    first
    | exact hadm
    | · refine worthiness_ge_of_ratio hadm (F / H) ?_
        intro θ hθ
        have hlim := tendsto_ratio (F := F) hH hε0
        have hev : ∀ᶠ n in atTop, Nfun F ε n / Dfun H ε n < F / H + θ :=
          hlim.eventually (eventually_lt_nhds (by linarith))
        filter_upwards [hgood, hev] with n hn hn2
        exact le_trans hn.2.2.2 hn2.le

end Catalan
