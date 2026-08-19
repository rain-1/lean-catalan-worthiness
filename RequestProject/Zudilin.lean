import RequestProject.Rec2
import RequestProject.BinaryDigits

/-!
# Zudilin's Catalan recurrence (Sections 4, 6, 7, 8.1 of the source note)

We define the two solutions `Qz`, `Pz` of Zudilin's recurrence

`(2m+1)²(2m+2)²φ(m) z_{m+1} = C_m z_m + (2m-1)²(2m)²φ(m+1) z_{m-1}`,

`φ(m) = 20m² - 8m + 1`, with `(Q₀,Q₁) = (1, 7/4)` and `(P₀,P₁) = (0, 13/8)`,
and prove the exact `2`-adic valuations (Lemma 6.1), the exact Wronskian (Lemma 7.1)
and the exact valuation of the increments of `P_m/Q_m` (Lemma 8.1).
-/

namespace Catalan

/-- `φ(m) = 20m² - 8m + 1`. -/
def phiZ (m : ℕ) : ℤ := 20 * (m : ℤ) ^ 2 - 8 * (m : ℤ) + 1

/-- The middle coefficient of Zudilin's recurrence. -/
def CZ (m : ℕ) : ℤ :=
  3520 * (m : ℤ) ^ 6 + 5632 * (m : ℤ) ^ 5 + 2064 * (m : ℤ) ^ 4 - 384 * (m : ℤ) ^ 3
    - 156 * (m : ℤ) ^ 2 + 16 * (m : ℤ) + 7

/-- The leading coefficient of Zudilin's recurrence. -/
def LZ (m : ℕ) : ℤ := (2 * (m : ℤ) + 1) ^ 2 * (2 * (m : ℤ) + 2) ^ 2 * phiZ m

/-- The trailing coefficient of Zudilin's recurrence. -/
def RZ (m : ℕ) : ℤ := (2 * (m : ℤ) - 1) ^ 2 * (2 * (m : ℤ)) ^ 2 * phiZ (m + 1)

/-- Zudilin's denominator sequence `Q_m`. -/
noncomputable def Qz : ℕ → ℚ :=
  rec2 (fun m => (LZ m : ℚ)) (fun m => (CZ m : ℚ)) (fun m => (RZ m : ℚ)) 1 (7 / 4)

/-- Zudilin's numerator sequence `P_m`. -/
noncomputable def Pz : ℕ → ℚ :=
  rec2 (fun m => (LZ m : ℚ)) (fun m => (CZ m : ℚ)) (fun m => (RZ m : ℚ)) 0 (13 / 8)

@[simp] lemma Qz_zero : Qz 0 = 1 := rfl
@[simp] lemma Qz_one : Qz 1 = 7 / 4 := rfl
@[simp] lemma Pz_zero : Pz 0 = 0 := rfl
@[simp] lemma Pz_one : Pz 1 = 13 / 8 := rfl

lemma phiZ_odd (m : ℕ) : Odd (phiZ m) := ⟨10 * (m : ℤ) ^ 2 - 4 * (m : ℤ), by unfold phiZ; ring⟩

lemma CZ_odd (m : ℕ) : Odd (CZ m) :=
  ⟨1760 * (m : ℤ) ^ 6 + 2816 * (m : ℤ) ^ 5 + 1032 * (m : ℤ) ^ 4 - 192 * (m : ℤ) ^ 3
      - 78 * (m : ℤ) ^ 2 + 8 * (m : ℤ) + 3, by unfold CZ; ring⟩

lemma phiZ_ne_zero (m : ℕ) : phiZ m ≠ 0 := by
  intro h
  have := phiZ_odd m
  rw [h] at this
  simp at this

lemma CZ_ne_zero (m : ℕ) : CZ m ≠ 0 := by
  intro h
  have := CZ_odd m
  rw [h] at this
  simp at this

lemma LZ_ne_zero (m : ℕ) : LZ m ≠ 0 := by
  unfold LZ
  have h1 : (2 * (m : ℤ) + 1) ^ 2 ≠ 0 := by positivity
  have h2 : (2 * (m : ℤ) + 2) ^ 2 ≠ 0 := by positivity
  exact mul_ne_zero (mul_ne_zero h1 h2) (phiZ_ne_zero m)

lemma RZ_succ_ne_zero (m : ℕ) : RZ (m + 1) ≠ 0 := by
  unfold RZ
  have h1 : (2 * ((m + 1 : ℕ) : ℤ) - 1) ^ 2 ≠ 0 := by
    have : 2 * ((m + 1 : ℕ) : ℤ) - 1 ≠ 0 := by push_cast; omega
    exact pow_ne_zero _ this
  have h2 : (2 * ((m + 1 : ℕ) : ℤ)) ^ 2 ≠ 0 := by
    have : (2 : ℤ) * ((m + 1 : ℕ) : ℤ) ≠ 0 := by push_cast; omega
    exact pow_ne_zero _ this
  exact mul_ne_zero (mul_ne_zero h1 h2) (phiZ_ne_zero (m + 1 + 1))

/-- The recurrence satisfied by `Qz` (and by `Pz`). -/
lemma Qz_rec (m : ℕ) :
    (LZ (m + 1) : ℚ) * Qz (m + 2) = (CZ (m + 1) : ℚ) * Qz (m + 1) + (RZ (m + 1) : ℚ) * Qz m := by
  have h := rec2_rec (fun m => (LZ m : ℚ)) (fun m => (CZ m : ℚ)) (fun m => (RZ m : ℚ)) 1 (7 / 4) m
    (by show ((LZ (m + 1) : ℤ) : ℚ) ≠ 0; exact_mod_cast LZ_ne_zero (m + 1))
  simpa [Qz] using h

lemma Pz_rec (m : ℕ) :
    (LZ (m + 1) : ℚ) * Pz (m + 2) = (CZ (m + 1) : ℚ) * Pz (m + 1) + (RZ (m + 1) : ℚ) * Pz m := by
  have h := rec2_rec (fun m => (LZ m : ℚ)) (fun m => (CZ m : ℚ)) (fun m => (RZ m : ℚ)) 0 (13 / 8) m
    (by show ((LZ (m + 1) : ℤ) : ℚ) ≠ 0; exact_mod_cast LZ_ne_zero (m + 1))
  simpa [Pz] using h

/-! ### Valuations of the coefficients -/

lemma val_CZ (m : ℕ) : padicValRat 2 ((CZ m : ℚ)) = 0 :=
  padicValRat_two_of_odd_int (CZ_odd m)

lemma val_LZ (m : ℕ) :
    padicValRat 2 ((LZ m : ℚ)) = 2 + 2 * (padicValNat 2 (m + 1) : ℤ) := by
  have hfac : (LZ m : ℚ)
      = ((2 : ℚ) ^ 2) * ((m + 1 : ℕ) : ℚ) ^ 2 * (((2 * (m : ℤ) + 1) ^ 2 * phiZ m : ℤ) : ℚ) := by
    unfold LZ
    push_cast
    ring
  have hodd : Odd ((2 * (m : ℤ) + 1) ^ 2 * phiZ m) :=
    (Odd.pow ⟨(m : ℤ), by ring⟩).mul (phiZ_odd m)
  have h1 : ((2 : ℚ) ^ 2) ≠ 0 := by norm_num
  have h2 : (((m + 1 : ℕ)) : ℚ) ^ 2 ≠ 0 := by
    have : ((m + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    exact pow_ne_zero _ this
  have h3 : (((2 * (m : ℤ) + 1) ^ 2 * phiZ m : ℤ) : ℚ) ≠ 0 := by
    have : ((2 * (m : ℤ) + 1) ^ 2 * phiZ m) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by omega)) (phiZ_ne_zero m)
    exact_mod_cast this
  have h2' : ((m + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  rw [hfac, padicValRat.mul (mul_ne_zero h1 h2) h3, padicValRat.mul h1 h2,
    padicValRat_two_two_pow 2, padicValRat.pow, padicValRat_two_natCast,
    padicValRat_two_of_odd_int hodd]
  push_cast
  ring

lemma val_RZ_succ (m : ℕ) :
    padicValRat 2 ((RZ (m + 1) : ℚ)) = 2 + 2 * (padicValNat 2 (m + 1) : ℤ) := by
  have hfac : (RZ (m + 1) : ℚ)
      = ((2 : ℚ) ^ 2) * ((m + 1 : ℕ) : ℚ) ^ 2
        * (((2 * ((m : ℤ) + 1) - 1) ^ 2 * phiZ (m + 2) : ℤ) : ℚ) := by
    unfold RZ
    push_cast
    ring
  have hodd : Odd ((2 * ((m : ℤ) + 1) - 1) ^ 2 * phiZ (m + 2)) :=
    (Odd.pow ⟨(m : ℤ), by ring⟩).mul (phiZ_odd (m + 2))
  have h1 : ((2 : ℚ) ^ 2) ≠ 0 := by norm_num
  have h2 : (((m + 1 : ℕ)) : ℚ) ^ 2 ≠ 0 := by
    have : ((m + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    exact pow_ne_zero _ this
  have h3 : (((2 * ((m : ℤ) + 1) - 1) ^ 2 * phiZ (m + 2) : ℤ) : ℚ) ≠ 0 := by
    have h4 : (2 * ((m : ℤ) + 1) - 1) ≠ 0 := by omega
    have : ((2 * ((m : ℤ) + 1) - 1) ^ 2 * phiZ (m + 2)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ h4) (phiZ_ne_zero (m + 2))
    exact_mod_cast this
  have h2' : ((m + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  rw [hfac, padicValRat.mul (mul_ne_zero h1 h2) h3, padicValRat.mul h1 h2,
    padicValRat_two_two_pow 2, padicValRat.pow, padicValRat_two_natCast,
    padicValRat_two_of_odd_int hodd]
  push_cast
  ring

/-! ### Lemma 6.1: exact `2`-adic valuations of the Zudilin solutions -/

/-- The generic induction step for both Zudilin solutions. -/
lemma zud_val_step {z : ℕ → ℚ} (c : ℤ) (m : ℕ)
    (hrec : (LZ (m + 1) : ℚ) * z (m + 2) = (CZ (m + 1) : ℚ) * z (m + 1) + (RZ (m + 1) : ℚ) * z m)
    (hzm : z m ≠ 0) (hzm1 : z (m + 1) ≠ 0)
    (hvm : padicValRat 2 (z m) = -4 * m + 2 * (s2 m : ℤ) + c)
    (hvm1 : padicValRat 2 (z (m + 1)) = -4 * (m + 1 : ℤ) + 2 * (s2 (m + 1) : ℤ) + c) :
    z (m + 2) ≠ 0 ∧
      padicValRat 2 (z (m + 2)) = -4 * (m + 2 : ℤ) + 2 * (s2 (m + 2) : ℤ) + c := by
  have hL : ((LZ (m + 1) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast LZ_ne_zero (m + 1)
  have hC : ((CZ (m + 1) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast CZ_ne_zero (m + 1)
  have hR : ((RZ (m + 1) : ℤ) : ℚ) ≠ 0 := by exact_mod_cast RZ_succ_ne_zero m
  have hs1 : (s2 (m + 1) : ℤ) = (s2 m : ℤ) + 1 - (padicValNat 2 (m + 1) : ℤ) := s2_succ m
  have hs2 : (s2 (m + 2) : ℤ) = (s2 (m + 1) : ℤ) + 1 - (padicValNat 2 (m + 2) : ℤ) := s2_succ (m + 1)
  have hlt : padicValRat 2 ((CZ (m + 1) : ℚ)) + padicValRat 2 (z (m + 1))
      < padicValRat 2 ((RZ (m + 1) : ℚ)) + padicValRat 2 (z m) := by
    rw [val_CZ, val_RZ_succ, hvm, hvm1]
    have hv : (0 : ℤ) ≤ (padicValNat 2 (m + 1) : ℤ) := Int.natCast_nonneg _
    omega
  obtain ⟨hne, hval⟩ := padicValRat_two_rec_step hrec hL hC hR hzm hzm1 hlt
  refine ⟨hne, ?_⟩
  have hLval : padicValRat 2 ((LZ (m + 1) : ℚ)) = 2 + 2 * (padicValNat 2 (m + 2) : ℤ) := by
    have := val_LZ (m + 1)
    simpa using this
  rw [hval, val_CZ, hLval, hvm1]
  omega

/-- Lemma 6.1, first half: `v₂(Q_m) = -4m + 2 s₂(m)`. -/
theorem Qz_ne_zero_and_val (m : ℕ) :
    Qz m ≠ 0 ∧ padicValRat 2 (Qz m) = -4 * (m : ℤ) + 2 * (s2 m : ℤ) := by
  have key : ∀ k : ℕ,
      (Qz k ≠ 0 ∧ padicValRat 2 (Qz k) = -4 * (k : ℤ) + 2 * (s2 k : ℤ)) ∧
      (Qz (k + 1) ≠ 0 ∧ padicValRat 2 (Qz (k + 1)) = -4 * ((k : ℤ) + 1) + 2 * (s2 (k + 1) : ℤ)) := by
    intro k
    induction k with
    | zero =>
        refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, ?_⟩⟩
        have : Qz 1 = 7 / 4 := rfl
        rw [this]
        have h7 : padicValRat 2 ((7 : ℚ) / 4) = -2 := by
          rw [show ((7 : ℚ) / 4) = ((7 : ℤ) : ℚ) / ((2 : ℚ) ^ 2) by norm_num,
            padicValRat.div (by norm_num) (by norm_num), padicValRat_two_of_odd_int ⟨3, by ring⟩,
            padicValRat_two_two_pow 2]
          norm_num
        rw [h7]
        norm_num [s2]
    | succ n ih =>
        refine ⟨ih.2, ?_⟩
        have := zud_val_step (z := Qz) 0 n (Qz_rec n) ih.1.1 ih.2.1
          (by simpa using ih.1.2) (by linarith [ih.2.2])
        refine ⟨this.1, ?_⟩
        have h := this.2
        push_cast at h ⊢
        linarith [h]
  exact (key m).1

theorem Qz_ne_zero (m : ℕ) : Qz m ≠ 0 := (Qz_ne_zero_and_val m).1

theorem val_Qz (m : ℕ) : padicValRat 2 (Qz m) = -4 * (m : ℤ) + 2 * (s2 m : ℤ) :=
  (Qz_ne_zero_and_val m).2

/-- Lemma 6.1, second half: `v₂(P_m) = -4m + 2 s₂(m) - 1` for `m ≥ 1`. -/
theorem Pz_ne_zero_and_val (m : ℕ) :
    Pz (m + 1) ≠ 0 ∧ padicValRat 2 (Pz (m + 1)) = -4 * ((m : ℤ) + 1) + 2 * (s2 (m + 1) : ℤ) - 1 := by
  have key : ∀ k : ℕ,
      (Pz (k + 1) ≠ 0 ∧
        padicValRat 2 (Pz (k + 1)) = -4 * ((k : ℤ) + 1) + 2 * (s2 (k + 1) : ℤ) - 1) ∧
      (Pz (k + 2) ≠ 0 ∧
        padicValRat 2 (Pz (k + 2)) = -4 * ((k : ℤ) + 2) + 2 * (s2 (k + 2) : ℤ) - 1) := by
    intro k
    induction k with
    | zero =>
        constructor
        · refine ⟨by norm_num, ?_⟩
          have h13 : padicValRat 2 ((13 : ℚ) / 8) = -3 := by
            rw [show ((13 : ℚ) / 8) = ((13 : ℤ) : ℚ) / ((2 : ℚ) ^ 3) by norm_num,
              padicValRat.div (by norm_num) (by norm_num),
              padicValRat_two_of_odd_int ⟨6, by ring⟩, padicValRat_two_two_pow 3]
            norm_num
          rw [show Pz 1 = 13 / 8 from rfl, h13]
          norm_num [s2]
        · -- `P₂ = C₁ P₁ / L₁`
          have hrec := Pz_rec 0
          have hP0 : Pz 0 = 0 := rfl
          rw [hP0, mul_zero, add_zero] at hrec
          have hL : ((LZ 1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast LZ_ne_zero 1
          have hC : ((CZ 1 : ℤ) : ℚ) ≠ 0 := by exact_mod_cast CZ_ne_zero 1
          have hP1 : Pz 1 ≠ 0 := by norm_num
          have hP2 : Pz 2 = ((CZ 1 : ℤ) : ℚ) * Pz 1 / ((LZ 1 : ℤ) : ℚ) := by
            field_simp at hrec ⊢
            linarith [hrec]
          have h13 : padicValRat 2 ((13 : ℚ) / 8) = -3 := by
            rw [show ((13 : ℚ) / 8) = ((13 : ℤ) : ℚ) / ((2 : ℚ) ^ 3) by norm_num,
              padicValRat.div (by norm_num) (by norm_num),
              padicValRat_two_of_odd_int ⟨6, by ring⟩, padicValRat_two_two_pow 3]
            norm_num
          refine ⟨by rw [hP2]; exact div_ne_zero (mul_ne_zero hC hP1) hL, ?_⟩
          rw [hP2, padicValRat.div (mul_ne_zero hC hP1) hL, padicValRat.mul hC hP1,
            val_CZ, val_LZ, show Pz 1 = 13 / 8 from rfl, h13]
          norm_num [s2]
    | succ n ih =>
        refine ⟨ih.2, ?_⟩
        have := zud_val_step (z := Pz) (-1) (n + 1) (Pz_rec (n + 1)) ih.1.1 ih.2.1
          (by push_cast; linarith [ih.1.2]) (by push_cast; linarith [ih.2.2])
        refine ⟨this.1, ?_⟩
        have h := this.2
        push_cast at h ⊢
        linarith [h]
  exact (key m).1

theorem Pz_ne_zero (m : ℕ) (hm : 1 ≤ m) : Pz m ≠ 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  exact (Pz_ne_zero_and_val k).1

theorem val_Pz (m : ℕ) :
    padicValRat 2 (Pz (m + 1)) = -4 * ((m : ℤ) + 1) + 2 * (s2 (m + 1) : ℤ) - 1 :=
  (Pz_ne_zero_and_val m).2


/-! ### Lemma 7.1: Zudilin's discrete Wronskian -/

lemma phiZ_cast (m : ℕ) : ((phiZ m : ℤ) : ℚ) = 20 * (m : ℚ) ^ 2 - 8 * (m : ℚ) + 1 := by
  unfold phiZ; push_cast; ring

lemma LZ_cast (m : ℕ) :
    ((LZ m : ℤ) : ℚ)
      = (2 * (m : ℚ) + 1) ^ 2 * (2 * (m : ℚ) + 2) ^ 2 * (20 * (m : ℚ) ^ 2 - 8 * (m : ℚ) + 1) := by
  unfold LZ phiZ; push_cast; ring

lemma RZ_cast (m : ℕ) :
    ((RZ m : ℤ) : ℚ)
      = (2 * (m : ℚ) - 1) ^ 2 * (2 * (m : ℚ)) ^ 2
        * (20 * ((m : ℚ) + 1) ^ 2 - 8 * ((m : ℚ) + 1) + 1) := by
  unfold RZ phiZ; push_cast; ring

/-- The Wronskian of the two Zudilin solutions, `W_{k+1} = P_{k+1} Q_k - Q_{k+1} P_k`. -/
noncomputable def WZ (k : ℕ) : ℚ := Pz (k + 1) * Qz k - Qz (k + 1) * Pz k

/-- The Wronskian recursion `L_m W_{m+1} = -R_m W_m`. -/
lemma WZ_step (k : ℕ) :
    (LZ (k + 1) : ℚ) * WZ (k + 1) = -((RZ (k + 1) : ℚ)) * WZ k := by
  have hP := Pz_rec k
  have hQ := Qz_rec k
  have e : k + 1 + 1 = k + 2 := rfl
  unfold WZ
  rw [e]
  linear_combination Qz (k + 1) * hP - Pz (k + 1) * hQ

/-- Lemma 7.1 (cleared-denominator form): `8m²(2m-1)² W_m = (-1)^{m-1} φ(m)`. -/
theorem WZ_closed_form_mul (k : ℕ) :
    8 * ((k : ℚ) + 1) ^ 2 * (2 * (k : ℚ) + 1) ^ 2 * WZ k
      = (-1 : ℚ) ^ k * (20 * ((k : ℚ) + 1) ^ 2 - 8 * ((k : ℚ) + 1) + 1) := by
  induction k with
  | zero => norm_num [WZ]
  | succ n ih =>
      have hA : (LZ (n + 1) : ℚ) * WZ (n + 1) = -((RZ (n + 1) : ℚ)) * WZ n := WZ_step n
      rw [LZ_cast, RZ_cast] at hA
      push_cast at hA ⊢
      have hp1 : (20 * ((n : ℚ) + 1) ^ 2 - 8 * ((n : ℚ) + 1) + 1) ≠ 0 := by
        have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
        nlinarith [sq_nonneg ((n : ℚ) + 1)]
      have hc : (4 * ((n : ℚ) + 1) ^ 2 * (2 * (n : ℚ) + 1) ^ 2
          * (20 * ((n : ℚ) + 1) ^ 2 - 8 * ((n : ℚ) + 1) + 1)) ≠ 0 := by
        have hn : (0 : ℚ) ≤ (n : ℚ) := Nat.cast_nonneg n
        have h1 : ((n : ℚ) + 1) ^ 2 ≠ 0 := by positivity
        have h2 : (2 * (n : ℚ) + 1) ^ 2 ≠ 0 := by positivity
        exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) h1) h2) hp1
      refine mul_left_cancel₀ hc ?_
      linear_combination (8 * ((n : ℚ) + 1) ^ 2 * (2 * (n : ℚ) + 1) ^ 2) * hA
        - ((2 * ((n : ℚ) + 1) - 1) ^ 2 * (2 * ((n : ℚ) + 1)) ^ 2
            * (20 * ((n : ℚ) + 2) ^ 2 - 8 * ((n : ℚ) + 2) + 1)) * ih

/-- Lemma 7.1: `W_m = (-1)^{m-1} φ(m) / (8 m² (2m-1)²)`. -/
theorem WZ_closed_form (k : ℕ) :
    WZ k = (-1 : ℚ) ^ k * (20 * ((k : ℚ) + 1) ^ 2 - 8 * ((k : ℚ) + 1) + 1)
      / (8 * ((k : ℚ) + 1) ^ 2 * (2 * (k : ℚ) + 1) ^ 2) := by
  have hne : (8 * ((k : ℚ) + 1) ^ 2 * (2 * (k : ℚ) + 1) ^ 2) ≠ 0 := by positivity
  field_simp
  linarith [WZ_closed_form_mul k]

/-! ### Lemma 8.1: valuations of the increments of `P_m/Q_m` -/

lemma WZ_eq_div (k : ℕ) :
    WZ k = ((((-1 : ℤ) ^ k * phiZ (k + 1)) : ℤ) : ℚ)
      / ((2 : ℚ) ^ 3 * ((k + 1 : ℕ) : ℚ) ^ 2 * (((2 * (k : ℤ) + 1) ^ 2 : ℤ) : ℚ)) := by
  rw [WZ_closed_form]
  push_cast [phiZ]
  field_simp
  ring

lemma WZ_ne_zero (k : ℕ) : WZ k ≠ 0 := by
  rw [WZ_eq_div]
  have h1 : ((((-1 : ℤ) ^ k * phiZ (k + 1)) : ℤ) : ℚ) ≠ 0 := by
    have : ((-1 : ℤ) ^ k * phiZ (k + 1)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (phiZ_ne_zero (k + 1))
    exact_mod_cast this
  have h2 : ((2 : ℚ) ^ 3 * ((k + 1 : ℕ) : ℚ) ^ 2 * (((2 * (k : ℤ) + 1) ^ 2 : ℤ) : ℚ)) ≠ 0 := by
    have ha : ((k + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hb : (((2 * (k : ℤ) + 1) ^ 2 : ℤ) : ℚ) ≠ 0 := by
      have : ((2 * (k : ℤ) + 1) ^ 2 : ℤ) ≠ 0 := pow_ne_zero _ (by omega)
      exact_mod_cast this
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ha)) hb
  exact div_ne_zero h1 h2

/-- `v₂(W_m) = -3 - 2 v₂(m)`. -/
theorem val_WZ (k : ℕ) :
    padicValRat 2 (WZ k) = -3 - 2 * (padicValNat 2 (k + 1) : ℤ) := by
  have hodd : Odd ((-1 : ℤ) ^ k * phiZ (k + 1)) :=
    (Odd.pow ⟨-1, by ring⟩).mul (phiZ_odd (k + 1))
  have hoddb : Odd (((2 * (k : ℤ) + 1) ^ 2 : ℤ)) := Odd.pow ⟨(k : ℤ), by ring⟩
  have h1 : ((((-1 : ℤ) ^ k * phiZ (k + 1)) : ℤ) : ℚ) ≠ 0 := by
    have : ((-1 : ℤ) ^ k * phiZ (k + 1)) ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (by norm_num)) (phiZ_ne_zero (k + 1))
    exact_mod_cast this
  have ha : ((k + 1 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hb : (((2 * (k : ℤ) + 1) ^ 2 : ℤ) : ℚ) ≠ 0 := by
    have : ((2 * (k : ℤ) + 1) ^ 2 : ℤ) ≠ 0 := pow_ne_zero _ (by omega)
    exact_mod_cast this
  have h2 : ((2 : ℚ) ^ 3 * ((k + 1 : ℕ) : ℚ) ^ 2) ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero _ ha)
  rw [WZ_eq_div, padicValRat.div h1 (mul_ne_zero h2 hb), padicValRat.mul h2 hb,
    padicValRat.mul (by norm_num : ((2 : ℚ) ^ 3) ≠ 0) (pow_ne_zero _ ha),
    padicValRat_two_two_pow 3, padicValRat.pow, padicValRat_two_natCast,
    padicValRat_two_of_odd_int hodd, padicValRat_two_of_odd_int hoddb]
  ring

/-- Lemma 8.1: `v₂(P_m/Q_m - P_{m-1}/Q_{m-1}) = 8m - 5 - 4 s₂(m) - 4 v₂(m)`. -/
theorem val_ratio_diff (k : ℕ) :
    padicValRat 2 (Pz (k + 1) / Qz (k + 1) - Pz k / Qz k)
      = 8 * ((k : ℤ) + 1) - 5 - 4 * (s2 (k + 1) : ℤ) - 4 * (padicValNat 2 (k + 1) : ℤ) := by
  have hQ1 : Qz (k + 1) ≠ 0 := Qz_ne_zero (k + 1)
  have hQ0 : Qz k ≠ 0 := Qz_ne_zero k
  have hdiff : Pz (k + 1) / Qz (k + 1) - Pz k / Qz k = WZ k / (Qz (k + 1) * Qz k) := by
    unfold WZ
    field_simp
  have hs : (s2 k : ℤ) = (s2 (k + 1) : ℤ) - 1 + (padicValNat 2 (k + 1) : ℤ) := by
    have := s2_pred (k + 1) (by omega)
    simpa using this
  rw [hdiff, padicValRat.div (WZ_ne_zero k) (mul_ne_zero hQ1 hQ0),
    padicValRat.mul hQ1 hQ0, val_WZ, val_Qz, val_Qz]
  omega


end Catalan
