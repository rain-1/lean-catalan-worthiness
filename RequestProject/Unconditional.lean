import RequestProject.NearCriticalAssembly

/-!
# A regression theorem exposing a gap in the public statement

`IsAdmissible` asks only that the denominators tend to infinity and that the
linear forms do not vanish. Consequently the elementary floor construction
already has worthiness at least one for every real number. The results in this
file are retained as regression tests for that specification gap; they are not
the intended structured Nesterenko-row theorem.
-/

namespace Catalan

open Filter Topology

def roundingQ (n : ℕ) : ℤ := (2 : ℤ) ^ (n + 1)

noncomputable def roundingP (α : ℝ) (n : ℕ) : ℤ :=
  ⌊((roundingQ n : ℤ) : ℝ) * α⌋ - 1

lemma roundingQ_cast (n : ℕ) :
    ((roundingQ n : ℤ) : ℝ) = (2 : ℝ) ^ (n + 1) := by
  simp [roundingQ]

lemma rounding_form_bounds (α : ℝ) (n : ℕ) :
    1 ≤ ((roundingQ n : ℤ) : ℝ) * α - ((roundingP α n : ℤ) : ℝ) ∧
      ((roundingQ n : ℤ) : ℝ) * α - ((roundingP α n : ℤ) : ℝ) < 2 := by
  have hlo := Int.floor_le (((roundingQ n : ℤ) : ℝ) * α)
  have hhi := Int.lt_floor_add_one (((roundingQ n : ℤ) : ℝ) * α)
  unfold roundingP
  push_cast
  constructor <;> linarith

theorem rounding_admissible (α : ℝ) :
    IsAdmissible α roundingQ (roundingP α) where
  q_ne_zero := Eventually.of_forall fun n => by
    unfold roundingQ
    positivity
  form_ne_zero := Eventually.of_forall fun n =>
    ne_of_gt (lt_of_lt_of_le (by norm_num) (rounding_form_bounds α n).1)
  tendsto_abs := by
    have hpow : Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have hshift := hpow.comp (tendsto_add_atTop_nat 1)
    convert hshift using 1
    ext n
    rw [roundingQ_cast, abs_of_pos (by positivity)]
    rfl

theorem rounding_worthiness_ge_one (α : ℝ) :
    ((1 : ℝ) : EReal) ≤ worthiness α roundingQ (roundingP α) := by
  have hmain := worthiness_ge_of_ratio (rounding_admissible α) 0 (by
    intro ε hε
    have hone : Tendsto (fun n : ℕ => (1 : ℝ) / (n + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have heps : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / (n + 1) < ε :=
      hone.eventually_lt_const hε
    filter_upwards [heps] with n hn
    have hform := rounding_form_bounds α n
    let L : ℝ := ((roundingQ n : ℤ) : ℝ) * α - ((roundingP α n : ℤ) : ℝ)
    have hL1 : 1 ≤ L := hform.1
    have hL2 : L < 2 := hform.2
    have hlogL : Real.log |L| ≤ Real.log 2 := by
      rw [abs_of_pos (lt_of_lt_of_le (by norm_num) hL1)]
      exact Real.log_le_log (by linarith) hL2.le
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hn1 : (0 : ℝ) < n + 1 := by positivity
    have hden : 0 < Real.log |((roundingQ n : ℤ) : ℝ)| := by
      rw [roundingQ_cast, abs_of_pos (by positivity), Real.log_pow]
      positivity
    have hbound :
        Real.log |L| / Real.log |((roundingQ n : ℤ) : ℝ)| ≤ (1 : ℝ) / (n + 1) := by
      rw [roundingQ_cast, abs_of_pos (pow_pos (by norm_num : (0 : ℝ) < 2) _), Real.log_pow]
      push_cast
      rw [div_le_iff₀ (mul_pos hn1 hlog2)]
      calc
        Real.log |L| ≤ Real.log 2 := hlogL
        _ = (1 / ((n : ℝ) + 1)) * (((n : ℝ) + 1) * Real.log 2) := by
          field_simp
    change Real.log |L| / Real.log |((roundingQ n : ℤ) : ℝ)| ≤ 0 + ε
    simpa using hbound.trans hn.le)
  simpa using hmain

/-- A definition-level `1-ε` consequence, valid for every real number and
therefore demonstrating that the public existential statement is too weak to
characterize the intended Nesterenko construction. -/
theorem worthiness_one_sub_eps_unconditional (α : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ q p : ℕ → ℤ, IsAdmissible α q p ∧
      ((1 - ε : ℝ) : EReal) < worthiness α q p := by
  refine ⟨roundingQ, roundingP α, rounding_admissible α,
    lt_of_lt_of_le ?_ (rounding_worthiness_ge_one α)⟩
  exact_mod_cast EReal.coe_lt_coe_iff.mpr (by linarith : 1 - ε < (1 : ℝ))

/-- The Catalan specialization of the specification-gap regression theorem. -/
theorem catalan_worthiness_one_sub_eps_unconditional {ε : ℝ} (hε : 0 < ε) :
    ∃ q p : ℕ → ℤ, IsAdmissible catalanReal q p ∧
      ((1 - ε : ℝ) : EReal) < worthiness catalanReal q p :=
  worthiness_one_sub_eps_unconditional catalanReal hε

end Catalan
