import Mathlib

/-!
# Construction quality (worthiness)

Section 1 of the base note.

* `IsAdmissible α q p` is Definition 1.1: an admissible approximation sequence;
* `worthiness α q p` is Definition 1.2, `δ(q,p) = liminf (-log|α - pₙ/qₙ|)/log|qₙ|`, taken in
  `EReal` so that the `liminf` always exists;
* `worthiness_ge_of_ratio` is the criterion used throughout: if the linear forms satisfy
  `log|qₙα - pₙ| / log|qₙ| ≤ c + o(1)` then `δ(q,p) ≥ 1 - c`;
* `worthiness_ge_of_rates` is the form quoted in Definition 1.2: if `log|qₙ| ≥ Hn - o(n)` and
  `log|qₙα - pₙ| ≤ Fn + o(n)` with `H > 0`, then `δ(q,p) ≥ 1 - F/H`.
-/

namespace Catalan

open Filter Topology

/-- Definition 1.1: an admissible approximation sequence to `α`. -/
structure IsAdmissible (α : ℝ) (q p : ℕ → ℤ) : Prop where
  q_ne_zero : ∀ᶠ n in atTop, q n ≠ 0
  form_ne_zero : ∀ᶠ n in atTop, (q n : ℝ) * α - (p n : ℝ) ≠ 0
  tendsto_abs : Tendsto (fun n => |(q n : ℝ)|) atTop atTop

/-- Definition 1.2: the worthiness (construction quality) of an approximation sequence. -/
noncomputable def worthiness (α : ℝ) (q p : ℕ → ℤ) : EReal :=
  liminf (fun n => ((-Real.log |α - (p n : ℝ) / (q n : ℝ)|) / Real.log |(q n : ℝ)| : ℝ) : ℕ → EReal)
    atTop

lemma eventually_log_abs_q_pos {α : ℝ} {q p : ℕ → ℤ} (h : IsAdmissible α q p) :
    ∀ᶠ n in atTop, 0 < Real.log |(q n : ℝ)| := by
  have h2 : ∀ᶠ n in atTop, (2 : ℝ) ≤ |(q n : ℝ)| :=
    h.tendsto_abs.eventually_ge_atTop 2
  filter_upwards [h2] with n hn
  have : (1 : ℝ) < |(q n : ℝ)| := by linarith
  exact Real.log_pos this

/-- The basic algebraic identity behind Definition 1.2. -/
lemma ratio_eq {α qv pv : ℝ} (hq : qv ≠ 0) (hl : qv * α - pv ≠ 0)
    (hlog : Real.log |qv| ≠ 0) :
    (-Real.log |α - pv / qv|) / Real.log |qv|
      = 1 - Real.log |qv * α - pv| / Real.log |qv| := by
  have hsplit : α - pv / qv = (qv * α - pv) / qv := by
    field_simp
  have habs : |α - pv / qv| = |qv * α - pv| / |qv| := by
    rw [hsplit, abs_div]
  rw [habs, Real.log_div (by simpa [abs_eq_zero] using hl) (by simpa [abs_eq_zero] using hq)]
  field_simp
  ring

/-- If the normalized linear forms are eventually at most `c + ε` for every `ε > 0`, then the
worthiness is at least `1 - c`. -/
theorem worthiness_ge_of_ratio {α : ℝ} {q p : ℕ → ℤ} (h : IsAdmissible α q p) (c : ℝ)
    (hratio : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log |(q n : ℝ) * α - (p n : ℝ)| / Real.log |(q n : ℝ)| ≤ c + ε) :
    ((1 - c : ℝ) : EReal) ≤ worthiness α q p := by
  have key : ∀ ε : ℝ, 0 < ε → ((1 - c - ε : ℝ) : EReal) ≤ worthiness α q p := by
    intro ε hε
    refine le_liminf_of_le (by isBoundedDefault) ?_
    filter_upwards [hratio ε hε, eventually_log_abs_q_pos h, h.q_ne_zero, h.form_ne_zero]
      with n hn hpos hq0 hl0
    have hne : Real.log |(q n : ℝ)| ≠ 0 := ne_of_gt hpos
    have hgoal : (1 - c - ε : ℝ)
        ≤ (-Real.log |α - (p n : ℝ) / (q n : ℝ)|) / Real.log |(q n : ℝ)| := by
      rw [ratio_eq (Int.cast_ne_zero.mpr hq0) hl0 hne]
      linarith
    exact_mod_cast hgoal
  by_contra hcon
  push_neg at hcon
  have hlt : worthiness α q p < ((1 - c : ℝ) : EReal) := hcon
  obtain ⟨r, hr1, hr2⟩ := exists_between hlt
  -- `r` is a real number strictly between the liminf and `1 - c`
  rcases EReal.lt_iff_exists_rat_btwn.mp hr2 with ⟨t, ht1, ht2⟩
  have hεpos : 0 < 1 - c - (t : ℝ) := by
    have : ((t : ℝ) : EReal) < ((1 - c : ℝ) : EReal) := ht2
    have := EReal.coe_lt_coe_iff.mp this
    linarith
  have := key (1 - c - (t : ℝ)) hεpos
  have hcast : ((1 - c - (1 - c - (t : ℝ)) : ℝ) : EReal) = ((t : ℝ) : EReal) := by
    norm_num
  rw [hcast] at this
  exact absurd (lt_of_le_of_lt this (lt_of_le_of_lt hr1.le ht1)) (lt_irrefl _)

/-- The form quoted in Definition 1.2: exponential rates `H` for the denominators and `F` for the
linear forms give `δ(q,p) ≥ 1 - F/H`. -/
theorem worthiness_ge_of_rates {α : ℝ} {q p : ℕ → ℤ} (h : IsAdmissible α q p) {H F : ℝ}
    (hH : 0 < H) (hF : 0 < F)
    (hq : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, (H - ε) * n ≤ Real.log |(q n : ℝ)|)
    (hl : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log |(q n : ℝ) * α - (p n : ℝ)| ≤ (F + ε) * n) :
    ((1 - F / H : ℝ) : EReal) ≤ worthiness α q p := by
  refine worthiness_ge_of_ratio h (F / H) ?_
  intro ε hε
  -- choose `η` small enough that `(F+η)/(H-η) ≤ F/H + ε`
  have hcont : Filter.Tendsto (fun t : ℝ => (F + t) / (H - t)) (𝓝[>] 0) (𝓝 (F / H)) := by
    have h1 : Filter.Tendsto (fun t : ℝ => (F + t) / (H - t)) (𝓝 0) (𝓝 ((F + 0) / (H - 0))) := by
      apply Filter.Tendsto.div
      · exact (continuous_const.add continuous_id).tendsto 0
      · exact (continuous_const.sub continuous_id).tendsto 0
      · simpa using ne_of_gt hH
    simpa using h1.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), (F + t) / (H - t) < F / H + ε :=
    hcont (Iio_mem_nhds (by linarith))
  obtain ⟨η, hη0, hηlt⟩ : ∃ η : ℝ, (0 < η ∧ η < H / 2) ∧ (F + η) / (H - η) < F / H + ε := by
    have hmem : Set.Ioo (0 : ℝ) (H / 2) ∈ 𝓝[>] (0 : ℝ) :=
      Ioo_mem_nhdsGT (by linarith)
    have hpos : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧ t < H / 2 :=
      Filter.eventually_of_mem hmem (fun x hx => ⟨hx.1, hx.2⟩)
    obtain ⟨t, ht1, ht2⟩ := ((hpos.and hev).exists)
    exact ⟨t, ht1, ht2⟩
  obtain ⟨hη, hηH⟩ := hη0
  have hHη : 0 < H - η := by linarith
  filter_upwards [hq η hη, hl η hη, eventually_log_abs_q_pos h,
    Filter.eventually_ge_atTop 1] with n hn1 hn2 hpos hn3
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn3
  have hden : 0 < (H - η) * n := by positivity
  have hle : Real.log |(q n : ℝ) * α - (p n : ℝ)| / Real.log |(q n : ℝ)|
      ≤ ((F + η) * n) / ((H - η) * n) := by
    rcases le_or_gt (Real.log |(q n : ℝ) * α - (p n : ℝ)|) 0 with hneg | hposl
    · have h1 : Real.log |(q n : ℝ) * α - (p n : ℝ)| / Real.log |(q n : ℝ)| ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hneg hpos.le
      have h2 : (0 : ℝ) ≤ ((F + η) * n) / ((H - η) * n) :=
        div_nonneg (mul_nonneg (by linarith) hnpos.le) (mul_nonneg (by linarith) hnpos.le)
      linarith
    · exact div_le_div₀ (by positivity) hn2 hden hn1
  refine hle.trans ?_
  rw [mul_div_mul_right _ _ (ne_of_gt hnpos)]
  exact hηlt.le

end Catalan
