import RequestProject.Rec2
import RequestProject.BinaryDigits

/-!
# The modular `E`-family Catalan recurrence (Sections 9, 10, 11.1 of the source note)

We define the two solutions `Ae`, `Be` of

`(n+1)² u_{n+1} = (12n(n+1)+4) u_n - 32 n² u_{n-1}`,

with `(A₀,A₁) = (1,4)` and `(B₀,B₁) = (0,1)`, prove the exact Wronskian (9.4),
the exact `2`-adic valuations (Lemma 10.1) and the exact valuations of the increments
of `2B_n/A_n` (Lemma 11.1).
-/

namespace Catalan

/-- Leading coefficient of the `E`-recurrence. -/
def LE (n : ℕ) : ℤ := ((n : ℤ) + 1) ^ 2

/-- Middle coefficient of the `E`-recurrence. -/
def CE (n : ℕ) : ℤ := 12 * (n : ℤ) * ((n : ℤ) + 1) + 4

/-- Trailing coefficient of the `E`-recurrence. -/
def RE (n : ℕ) : ℤ := -32 * (n : ℤ) ^ 2

/-- The modular `E`-family denominator sequence `A_n`. -/
noncomputable def Ae : ℕ → ℚ :=
  rec2 (fun n => (LE n : ℚ)) (fun n => (CE n : ℚ)) (fun n => (RE n : ℚ)) 1 4

/-- The modular `E`-family numerator sequence `B_n`. -/
noncomputable def Be : ℕ → ℚ :=
  rec2 (fun n => (LE n : ℚ)) (fun n => (CE n : ℚ)) (fun n => (RE n : ℚ)) 0 1

@[simp] lemma Ae_zero : Ae 0 = 1 := rfl
@[simp] lemma Ae_one : Ae 1 = 4 := rfl
@[simp] lemma Be_zero : Be 0 = 0 := rfl
@[simp] lemma Be_one : Be 1 = 1 := rfl

lemma LE_ne_zero (n : ℕ) : LE n ≠ 0 := by
  unfold LE
  have : ((n : ℤ) + 1) ≠ 0 := by omega
  exact pow_ne_zero _ this

lemma CE_odd_part (n : ℕ) : Odd (3 * (n : ℤ) * ((n : ℤ) + 1) + 1) := by
  obtain ⟨j, hj⟩ : Even ((n : ℤ) * ((n : ℤ) + 1)) := Int.even_mul_succ_self _
  exact ⟨3 * j, by rw [mul_assoc, hj]; ring⟩

lemma CE_ne_zero (n : ℕ) : CE n ≠ 0 := by
  have h : CE n = 4 * (3 * (n : ℤ) * ((n : ℤ) + 1) + 1) := by unfold CE; ring
  have hodd := CE_odd_part n
  intro hc
  rw [h] at hc
  have : (3 * (n : ℤ) * ((n : ℤ) + 1) + 1) = 0 := by omega
  rw [this] at hodd
  simp at hodd

lemma RE_succ_ne_zero (n : ℕ) : RE (n + 1) ≠ 0 := by
  unfold RE
  have h : ((n : ℤ) + 1) ≠ 0 := by omega
  push_cast
  exact mul_ne_zero (by norm_num) (pow_ne_zero _ h)

lemma Ae_rec (n : ℕ) :
    (LE (n + 1) : ℚ) * Ae (n + 2) = (CE (n + 1) : ℚ) * Ae (n + 1) + (RE (n + 1) : ℚ) * Ae n := by
  have h := rec2_rec (fun n => (LE n : ℚ)) (fun n => (CE n : ℚ)) (fun n => (RE n : ℚ)) 1 4 n
    (by show ((LE (n + 1) : ℤ) : ℚ) ≠ 0; exact_mod_cast LE_ne_zero (n + 1))
  simpa [Ae] using h

lemma Be_rec (n : ℕ) :
    (LE (n + 1) : ℚ) * Be (n + 2) = (CE (n + 1) : ℚ) * Be (n + 1) + (RE (n + 1) : ℚ) * Be n := by
  have h := rec2_rec (fun n => (LE n : ℚ)) (fun n => (CE n : ℚ)) (fun n => (RE n : ℚ)) 0 1 n
    (by show ((LE (n + 1) : ℤ) : ℚ) ≠ 0; exact_mod_cast LE_ne_zero (n + 1))
  simpa [Be] using h

/-! ### Valuations of the coefficients -/

lemma val_LE (n : ℕ) :
    padicValRat 2 ((LE n : ℚ)) = 2 * (padicValNat 2 (n + 1) : ℤ) := by
  have hfac : ((LE n : ℤ) : ℚ) = ((n + 1 : ℕ) : ℚ) ^ 2 := by
    unfold LE; push_cast; ring
  have hne : ((n + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  rw [hfac, padicValRat.pow hne, padicValRat_two_natCast]
  ring

lemma val_CE (n : ℕ) : padicValRat 2 ((CE n : ℚ)) = 2 := by
  have hfac : ((CE n : ℤ) : ℚ)
      = (2 : ℚ) ^ 2 * (((3 * (n : ℤ) * ((n : ℤ) + 1) + 1 : ℤ)) : ℚ) := by
    unfold CE; push_cast; ring
  have h1 : ((2 : ℚ) ^ 2) ≠ 0 := by norm_num
  have h2 : (((3 * (n : ℤ) * ((n : ℤ) + 1) + 1 : ℤ)) : ℚ) ≠ 0 := by
    have hodd := CE_odd_part n
    have : (3 * (n : ℤ) * ((n : ℤ) + 1) + 1) ≠ 0 := by
      intro h
      rw [h] at hodd
      simp at hodd
    exact_mod_cast this
  rw [hfac, padicValRat.mul h1 h2, padicValRat_two_two_pow 2,
    padicValRat_two_of_odd_int (CE_odd_part n)]
  ring

lemma val_RE_succ (n : ℕ) :
    padicValRat 2 ((RE (n + 1) : ℚ)) = 5 + 2 * (padicValNat 2 (n + 1) : ℤ) := by
  have hfac : ((RE (n + 1) : ℤ) : ℚ)
      = (2 : ℚ) ^ 5 * ((n + 1 : ℕ) : ℚ) ^ 2 * (((-1 : ℤ)) : ℚ) := by
    unfold RE; push_cast; ring
  have hne : ((n + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  have h1 : ((2 : ℚ) ^ 5) ≠ 0 := by norm_num
  have h2 : (((n + 1 : ℕ) : ℚ) ^ 2) ≠ 0 := pow_ne_zero _ hne
  have h3 : (((-1 : ℤ)) : ℚ) ≠ 0 := by norm_num
  rw [hfac, padicValRat.mul (mul_ne_zero h1 h2) h3, padicValRat.mul h1 h2,
    padicValRat_two_two_pow 5, padicValRat.pow hne, padicValRat_two_natCast,
    padicValRat_two_of_odd_int ⟨-1, by ring⟩]
  ring

/-! ### Lemma 10.1: exact `2`-adic valuations of the `E`-row -/

/-- The generic induction step for both `E`-family solutions. -/
lemma efam_val_step {u : ℕ → ℚ} (c : ℤ) (n : ℕ)
    (hrec : (LE (n + 1) : ℚ) * u (n + 2) = (CE (n + 1) : ℚ) * u (n + 1) + (RE (n + 1) : ℚ) * u n)
    (hun : u n ≠ 0) (hun1 : u (n + 1) ≠ 0)
    (hvn : padicValRat 2 (u n) = 2 * (s2 n : ℤ) + c)
    (hvn1 : padicValRat 2 (u (n + 1)) = 2 * (s2 (n + 1) : ℤ) + c) :
    u (n + 2) ≠ 0 ∧ padicValRat 2 (u (n + 2)) = 2 * (s2 (n + 2) : ℤ) + c := by
  have hL : ((LE (n + 1) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast LE_ne_zero (n + 1)
  have hC : ((CE (n + 1) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast CE_ne_zero (n + 1)
  have hR : ((RE (n + 1) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast RE_succ_ne_zero n
  have hs1 : (s2 (n + 1) : ℤ) = (s2 n : ℤ) + 1 - (padicValNat 2 (n + 1) : ℤ) := s2_succ n
  have hs2 : (s2 (n + 2) : ℤ) = (s2 (n + 1) : ℤ) + 1 - (padicValNat 2 (n + 2) : ℤ) := s2_succ (n + 1)
  have hlt : padicValRat 2 ((CE (n + 1) : ℚ)) + padicValRat 2 (u (n + 1))
      < padicValRat 2 ((RE (n + 1) : ℚ)) + padicValRat 2 (u n) := by
    rw [val_CE, val_RE_succ, hvn, hvn1]
    have hv : (0 : ℤ) ≤ (padicValNat 2 (n + 1) : ℤ) := Int.natCast_nonneg _
    omega
  obtain ⟨hne, hval⟩ := padicValRat_two_rec_step hrec hL hC hR hun hun1 hlt
  refine ⟨hne, ?_⟩
  have hLval : padicValRat 2 ((LE (n + 1) : ℚ)) = 2 * (padicValNat 2 (n + 2) : ℤ) := by
    have := val_LE (n + 1)
    simpa using this
  rw [hval, val_CE, hLval, hvn1]
  omega

/-- Lemma 10.1, first half: `v₂(A_n) = 2 s₂(n)`. -/
theorem Ae_ne_zero_and_val (n : ℕ) :
    Ae n ≠ 0 ∧ padicValRat 2 (Ae n) = 2 * (s2 n : ℤ) := by
  have key : ∀ k : ℕ,
      (Ae k ≠ 0 ∧ padicValRat 2 (Ae k) = 2 * (s2 k : ℤ)) ∧
      (Ae (k + 1) ≠ 0 ∧ padicValRat 2 (Ae (k + 1)) = 2 * (s2 (k + 1) : ℤ)) := by
    intro k
    induction k with
    | zero =>
        refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, ?_⟩⟩
        have h4 : padicValRat 2 ((4 : ℚ)) = 2 := by
          rw [show ((4 : ℚ)) = ((2 : ℚ) ^ 2) by norm_num, padicValRat_two_two_pow 2]
          norm_num
        rw [show Ae 1 = 4 from rfl, h4]
        norm_num [s2]
    | succ n ih =>
        refine ⟨ih.2, ?_⟩
        have := efam_val_step (u := Ae) 0 n (Ae_rec n) ih.1.1 ih.2.1
          (by simpa using ih.1.2) (by simpa using ih.2.2)
        exact ⟨this.1, by simpa using this.2⟩
  exact (key n).1

theorem Ae_ne_zero (n : ℕ) : Ae n ≠ 0 := (Ae_ne_zero_and_val n).1

theorem val_Ae (n : ℕ) : padicValRat 2 (Ae n) = 2 * (s2 n : ℤ) := (Ae_ne_zero_and_val n).2

/-- Lemma 10.1, second half: `v₂(B_n) = 2 s₂(n) - 2` for `n ≥ 1`. -/
theorem Be_ne_zero_and_val (n : ℕ) :
    Be (n + 1) ≠ 0 ∧ padicValRat 2 (Be (n + 1)) = 2 * (s2 (n + 1) : ℤ) - 2 := by
  have key : ∀ k : ℕ,
      (Be (k + 1) ≠ 0 ∧ padicValRat 2 (Be (k + 1)) = 2 * (s2 (k + 1) : ℤ) - 2) ∧
      (Be (k + 2) ≠ 0 ∧ padicValRat 2 (Be (k + 2)) = 2 * (s2 (k + 2) : ℤ) - 2) := by
    intro k
    induction k with
    | zero =>
        constructor
        · refine ⟨by norm_num, ?_⟩
          rw [show Be 1 = 1 from rfl]
          norm_num [s2]
        · -- `B₂ = C₁ B₁ / L₁ = 7`
          have hrec := Be_rec 0
          have hB0 : Be 0 = 0 := rfl
          rw [hB0, mul_zero, add_zero] at hrec
          have hL : ((LE 1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast LE_ne_zero 1
          have hC : ((CE 1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast CE_ne_zero 1
          have hB1 : Be 1 ≠ 0 := by norm_num
          have hB2 : Be 2 = ((CE 1 : ℤ) : ℚ) * Be 1 / ((LE 1 : ℤ) : ℚ) := by
            field_simp at hrec ⊢
            linarith [hrec]
          refine ⟨by rw [hB2]; exact div_ne_zero (mul_ne_zero hC hB1) hL, ?_⟩
          rw [hB2, padicValRat.div (mul_ne_zero hC hB1) hL, padicValRat.mul hC hB1,
            val_CE, show Be 1 = 1 from rfl]
          have hLval : padicValRat 2 ((LE 1 : ℚ)) = 2 * (padicValNat 2 2 : ℤ) := by
            have := val_LE 1
            simpa using this
          rw [hLval]
          norm_num [s2]
    | succ n ih =>
        refine ⟨ih.2, ?_⟩
        have := efam_val_step (u := Be) (-2) (n + 1) (Be_rec (n + 1)) ih.1.1 ih.2.1
          (by linarith [ih.1.2]) (by linarith [ih.2.2])
        exact ⟨this.1, by linarith [this.2]⟩
  exact (key n).1

theorem Be_ne_zero (n : ℕ) (hn : 1 ≤ n) : Be n ≠ 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  exact (Be_ne_zero_and_val k).1

theorem val_Be (n : ℕ) : padicValRat 2 (Be (n + 1)) = 2 * (s2 (n + 1) : ℤ) - 2 :=
  (Be_ne_zero_and_val n).2

/-! ### The exact Wronskian (9.4) -/

/-- The Wronskian of the `E`-row, `W_{n+1} = A_{n+1} B_n - A_n B_{n+1}`. -/
noncomputable def WE (n : ℕ) : ℚ := Ae (n + 1) * Be n - Ae n * Be (n + 1)

lemma WE_step (n : ℕ) :
    (LE (n + 1) : ℚ) * WE (n + 1) = -((RE (n + 1) : ℚ)) * WE n := by
  have hA := Ae_rec n
  have hB := Be_rec n
  have e : n + 1 + 1 = n + 2 := rfl
  unfold WE
  rw [e]
  linear_combination Be (n + 1) * hA - Ae (n + 1) * hB

/-- Equation (9.4): `A_n B_{n-1} - A_{n-1} B_n = -32^{n-1}/n²`. -/
theorem WE_closed_form_mul (n : ℕ) :
    ((n : ℚ) + 1) ^ 2 * WE n = -(32 : ℚ) ^ n := by
  induction n with
  | zero => norm_num [WE]
  | succ k ih =>
      have hA : (LE (k + 1) : ℚ) * WE (k + 1) = -((RE (k + 1) : ℚ)) * WE k := WE_step k
      have hL : ((LE (k + 1) : ℤ) : ℚ) = ((k : ℚ) + 2) ^ 2 := by unfold LE; push_cast; ring
      have hR : ((RE (k + 1) : ℤ) : ℚ) = -32 * ((k : ℚ) + 1) ^ 2 := by unfold RE; push_cast; ring
      rw [hL, hR] at hA
      push_cast
      linear_combination hA + 32 * ih

theorem WE_ne_zero (n : ℕ) : WE n ≠ 0 := by
  intro h
  have := WE_closed_form_mul n
  rw [h, mul_zero] at this
  have : (32 : ℚ) ^ n = 0 := by linarith
  exact absurd this (by positivity)

theorem WE_closed_form (n : ℕ) : WE n = -(32 : ℚ) ^ n / ((n : ℚ) + 1) ^ 2 := by
  have hne : (((n : ℚ) + 1) ^ 2) ≠ 0 := by positivity
  field_simp
  linarith [WE_closed_form_mul n]

/-! ### Lemma 11.1: valuations of the increments of `2B_n/A_n` -/

/-- Lemma 11.1: `v₂(2B_n/A_n - 2B_{n-1}/A_{n-1}) = 5n - 2 - 4 s₂(n) - 4 v₂(n)`. -/
theorem val_E_ratio_diff (n : ℕ) :
    padicValRat 2 (2 * Be (n + 1) / Ae (n + 1) - 2 * Be n / Ae n)
      = 5 * ((n : ℤ) + 1) - 2 - 4 * (s2 (n + 1) : ℤ) - 4 * (padicValNat 2 (n + 1) : ℤ) := by
  have hA1 : Ae (n + 1) ≠ 0 := Ae_ne_zero (n + 1)
  have hA0 : Ae n ≠ 0 := Ae_ne_zero n
  have hW : WE n ≠ 0 := WE_ne_zero n
  have hnum : (-2 : ℚ) * WE n ≠ 0 := mul_ne_zero (by norm_num) hW
  have hden : Ae (n + 1) * Ae n ≠ 0 := mul_ne_zero hA1 hA0
  have hdiff : 2 * Be (n + 1) / Ae (n + 1) - 2 * Be n / Ae n
      = (-2 * WE n) / (Ae (n + 1) * Ae n) := by
    unfold WE
    field_simp
    ring
  have hval2 : padicValRat 2 ((-2 : ℚ)) = 1 := by
    rw [show ((-2 : ℚ)) = ((-1 : ℤ) : ℚ) * ((2 : ℚ) ^ 1) by norm_num,
      padicValRat.mul (by norm_num) (by norm_num),
      padicValRat_two_of_odd_int ⟨-1, by ring⟩, padicValRat_two_two_pow 1]
    norm_num
  have hWval : padicValRat 2 ((-2 : ℚ) * WE n) = 1 + padicValRat 2 (WE n) := by
    rw [padicValRat.mul (by norm_num) hW, hval2]
  have hWE : padicValRat 2 (WE n) = 5 * (n : ℤ) - 2 * (padicValNat 2 (n + 1) : ℤ) := by
    rw [WE_closed_form]
    have h1 : (-(32 : ℚ) ^ n) ≠ 0 := by
      have h : ((32 : ℚ) ^ n) ≠ 0 := by positivity
      exact neg_ne_zero.mpr h
    have hne : ((n + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    have h2 : (((n : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    have hden' : ((n : ℚ) + 1) ^ 2 = ((n + 1 : ℕ) : ℚ) ^ 2 := by push_cast; ring
    have hnum' : (-(32 : ℚ) ^ n) = ((-1 : ℤ) : ℚ) * ((2 : ℚ) ^ 5) ^ n := by push_cast; ring
    rw [padicValRat.div h1 h2, hden', hnum',
      padicValRat.mul (by norm_num) (by positivity),
      padicValRat_two_of_odd_int ⟨-1, by ring⟩,
      padicValRat.pow (by norm_num), padicValRat_two_two_pow 5,
      padicValRat.pow hne, padicValRat_two_natCast]
    ring
  have hs : (s2 n : ℤ) = (s2 (n + 1) : ℤ) - 1 + (padicValNat 2 (n + 1) : ℤ) := by
    have := s2_pred (n + 1) (by omega)
    simpa using this
  rw [hdiff, padicValRat.div hnum hden, padicValRat.mul hA1 hA0, hWval, hWE, val_Ae, val_Ae]
  omega

end Catalan
