import RequestProject.PadeNumerator

/-!
# Beukers' uniform `2`-adic Padé estimate

This file proves Lemma 3.1 of the note (Beukers, Proposition 7.1(4)):

`‖p_n(a/2) - Ξ(a/2) q_n(a/2)‖₂ ≤ 4 n² 2^{-4n}`  for odd `a` and `n ≥ 1`,

where `p_n`, `q_n` are the two solutions of Beukers' Padé recurrence (`bp`, `bq`) and `Ξ` is the
`2`-adic Padé function of `XiSeries.lean`.

The proof has four steps.

1. *Exact valuations of the denominators.*  For half-odd `x` the middle coefficient of the
   recurrence has valuation `-2`, which dominates the trailing term, so the valuation
   `v₂(q_n(x)) = -4n + 2 s₂(n)` propagates through the recurrence exactly as for the Zudilin row.

2. *The Casoratian.*  `p_{n+1} q_n - p_n q_{n+1} = 1/(n+1)²`, by induction.  Hence the increments
   of the Padé ratio `r_n = p_n/q_n` are `1/((n+1)² q_n q_{n+1})`, of exact valuation
   `8n + 2 - 4 s₂(n)`, which is strictly increasing; by `padic2_limit_of_strictMono_val` the row
   `r_n` converges `2`-adically and the tail `L - r_n` has valuation exactly `8n + 2 - 4 s₂(n)`.

3. *The limit is `Ξ`.*  Using the closed forms of `PadeNumerator.lean` and `ClosedForm.lean`,

   `Ξ q_n - p_n = ∑_{k≤n} (n choose k) (β_k(y)/(k!)²) (Ξ + h_k) = -∑_{k≤n} (n choose k) g_k T_k`,

   where `T_k = ∑_{j≥k} [j/x][j/(1-x)]` is the tail of Beukers' series.  The norms satisfy
   `‖g_k‖ = 2^{4k - 2 s₂(k)}` and `‖T_k‖ ≤ 2^{-(4k + 2 - 2 s₂(k))}`, so every term has norm at
   most `1/4`; therefore `‖Ξ - r_n‖ ≤ (1/4)·2^{-(4n - 2 s₂ n)} → 0` and `L = Ξ`.

4. *Conclusion.*  `‖p_n - Ξ q_n‖ = ‖q_n‖ ‖r_n - Ξ‖ = 2^{2 s₂(n) - 4n - 2} ≤ 4 n² 2^{-4n}`.
-/

namespace Catalan

open Filter Topology Finset

/-! ### 1. The exact `2`-adic valuation of the Padé denominators -/

lemma bC_ne_zero_and_val {x : ℚ} (hx : HalfOdd x) (n : ℕ) :
    bC x n ≠ 0 ∧ padicValRat 2 (bC x n) = -2 := by
  obtain ⟨a, ha, rfl⟩ := hx
  set A : ℤ := 4 * (2 * (n : ℤ) * ((n : ℤ) + 1) + 1) + a ^ 2 - 2 * a with hA
  have hAodd : Odd A := by
    rcases ha with ⟨b, hb⟩
    exact ⟨4 * (n : ℤ) * ((n : ℤ) + 1) + 2 * b ^ 2 + 1, by rw [hA, hb]; ring⟩
  have hAne : (A : ℚ) ≠ 0 := by
    have : A ≠ 0 := by
      rintro h
      rw [h] at hAodd
      simp at hAodd
    exact_mod_cast this
  have hval : bC ((a : ℚ) / 2) n = (A : ℚ) / (2 : ℚ) ^ 2 := by
    unfold bC
    rw [hA]
    push_cast
    ring
  refine ⟨by rw [hval]; exact div_ne_zero hAne (by norm_num), ?_⟩
  rw [hval, padicValRat.div hAne (by norm_num), padicValRat_two_of_odd_int hAodd,
    padicValRat_two_two_pow 2]
  norm_num

lemma bq_ne_zero_and_val {x : ℚ} (hx : HalfOdd x) (n : ℕ) :
    bq x n ≠ 0 ∧ padicValRat 2 (bq x n) = -4 * (n : ℤ) + 2 * (s2 n : ℤ) := by
  have key : ∀ k : ℕ,
      (bq x k ≠ 0 ∧ padicValRat 2 (bq x k) = -4 * (k : ℤ) + 2 * (s2 k : ℤ)) ∧
      (bq x (k + 1) ≠ 0 ∧
        padicValRat 2 (bq x (k + 1)) = -4 * ((k : ℤ) + 1) + 2 * (s2 (k + 1) : ℤ)) := by
    intro k
    induction k with
    | zero =>
        refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
        have h1 : bq x 1 = bC x 0 := by
          unfold bC
          simp
          ring
        obtain ⟨hne, hv⟩ := bC_ne_zero_and_val hx 0
        rw [h1]
        exact ⟨hne, by rw [hv]; norm_num [s2]⟩
    | succ n ih =>
        refine ⟨ih.2, ?_⟩
        obtain ⟨hne0, hv0⟩ := ih.1
        obtain ⟨hne1, hv1⟩ := ih.2
        obtain ⟨hCne, hCv⟩ := bC_ne_zero_and_val hx (n + 1)
        have hLne : bL (n + 1) ≠ 0 := bL_ne_zero (n + 1)
        have hRne : bR (n + 1) ≠ 0 := by
          unfold bR
          have : ((n : ℚ) + 1) ≠ 0 := by positivity
          push_cast
          simpa using pow_ne_zero 2 this
        have hs1 : (s2 (n + 1) : ℤ) = (s2 n : ℤ) + 1 - (padicValNat 2 (n + 1) : ℤ) := s2_succ n
        have hs2 : (s2 (n + 1 + 1) : ℤ)
            = (s2 (n + 1) : ℤ) + 1 - (padicValNat 2 (n + 1 + 1) : ℤ) := s2_succ (n + 1)
        have hRv : padicValRat 2 (bR (n + 1)) = 2 * (padicValNat 2 (n + 1) : ℤ) := by
          have h : bR (n + 1) = -(((n + 1 : ℕ) : ℚ) ^ 2) := by unfold bR; push_cast; ring
          rw [h, padicValRat.neg, padicValRat.pow,
            padicValRat_two_natCast]
          ring
        have hLv : padicValRat 2 (bL (n + 1)) = 2 * (padicValNat 2 (n + 1 + 1) : ℤ) := by
          have h : bL (n + 1) = (((n + 1 + 1 : ℕ) : ℚ) ^ 2) := by unfold bL; push_cast; ring
          rw [h, padicValRat.pow,
            padicValRat_two_natCast]
          ring
        have hlt : padicValRat 2 (bC x (n + 1)) + padicValRat 2 (bq x (n + 1))
            < padicValRat 2 (bR (n + 1)) + padicValRat 2 (bq x n) := by
          rw [hCv, hRv, hv0, hv1]
          have hv : (0 : ℤ) ≤ (padicValNat 2 (n + 1) : ℤ) := Int.natCast_nonneg _
          omega
        obtain ⟨hne, hval⟩ :=
          padicValRat_two_rec_step (bq_rec x n) hLne hCne hRne hne0 hne1 hlt
        refine ⟨hne, ?_⟩
        have key : padicValRat 2 (bq x (n + 1 + 1))
            = -4 * ((n : ℤ) + 2) + 2 * (s2 (n + 1 + 1) : ℤ) := by
          rw [hval, hCv, hLv, hv1]
          omega
        rw [key]
        push_cast
        ring
  exact (key n).1

lemma bq_ne_zero {x : ℚ} (hx : HalfOdd x) (n : ℕ) : bq x n ≠ 0 := (bq_ne_zero_and_val hx n).1

lemma val_bq {x : ℚ} (hx : HalfOdd x) (n : ℕ) :
    padicValRat 2 (bq x n) = -4 * (n : ℤ) + 2 * (s2 n : ℤ) := (bq_ne_zero_and_val hx n).2

/-! ### 2. The Casoratian -/

/-- The Casoratian of the two Padé solutions: `p_{n+1} q_n - p_n q_{n+1} = 1/(n+1)²`. -/
theorem bp_bq_casoratian (x : ℚ) (n : ℕ) :
    bp x (n + 1) * bq x n - bp x n * bq x (n + 1) = 1 / (((n : ℚ) + 1) ^ 2) := by
  induction n with
  | zero => norm_num
  | succ k ih =>
      have hq := bq_rec x k
      have hp := bp_rec x k
      have hL : bL (k + 1) = ((k : ℚ) + 2) ^ 2 := by unfold bL; push_cast; ring
      have hR : bR (k + 1) = -(((k : ℚ) + 1) ^ 2) := by unfold bR; push_cast; ring
      rw [hL, hR] at hq hp
      have hk2 : ((k : ℚ) + 2) ^ 2 ≠ 0 := by positivity
      have hk1 : ((k : ℚ) + 1) ^ 2 ≠ 0 := by positivity
      have key : ((k : ℚ) + 2) ^ 2 * (bp x (k + 2) * bq x (k + 1) - bp x (k + 1) * bq x (k + 2))
          = ((k : ℚ) + 1) ^ 2 * (bp x (k + 1) * bq x k - bp x k * bq x (k + 1)) := by
        have h1 : ((k : ℚ) + 2) ^ 2 * bp x (k + 2)
            = bC x (k + 1) * bp x (k + 1) - ((k : ℚ) + 1) ^ 2 * bp x k := by linarith [hp]
        have h2 : ((k : ℚ) + 2) ^ 2 * bq x (k + 2)
            = bC x (k + 1) * bq x (k + 1) - ((k : ℚ) + 1) ^ 2 * bq x k := by linarith [hq]
        calc ((k : ℚ) + 2) ^ 2 * (bp x (k + 2) * bq x (k + 1) - bp x (k + 1) * bq x (k + 2))
            = (((k : ℚ) + 2) ^ 2 * bp x (k + 2)) * bq x (k + 1)
              - bp x (k + 1) * (((k : ℚ) + 2) ^ 2 * bq x (k + 2)) := by ring
          _ = ((k : ℚ) + 1) ^ 2 * (bp x (k + 1) * bq x k - bp x k * bq x (k + 1)) := by
              rw [h1, h2]; ring
      rw [ih] at key
      have : bp x (k + 2) * bq x (k + 1) - bp x (k + 1) * bq x (k + 2)
          = 1 / (((k : ℚ) + 2) ^ 2) := by
        field_simp at key ⊢
        linarith [key]
      rw [show ((((k + 1 : ℕ) : ℚ)) + 1) ^ 2 = (((k : ℚ) + 2) ^ 2) by push_cast; ring]
      exact this

/-! ### 3. The Padé ratio row converges `2`-adically -/

/-- The Padé ratio `r_n = p_n(x)/q_n(x)`. -/
noncomputable def bratio (x : ℚ) (n : ℕ) : ℚ := bp x n / bq x n

lemma bratio_diff {x : ℚ} (hx : HalfOdd x) (n : ℕ) :
    bratio x (n + 1) - bratio x n
      = 1 / ((((n : ℚ) + 1) ^ 2) * (bq x n * bq x (n + 1))) := by
  have h0 := bq_ne_zero hx n
  have h1 := bq_ne_zero hx (n + 1)
  have hcas := bp_bq_casoratian x n
  have hn : (((n : ℚ) + 1) ^ 2) ≠ 0 := by positivity
  unfold bratio
  rw [div_sub_div _ _ h1 h0,
    show bp x (n + 1) * bq x n - bq x (n + 1) * bp x n = 1 / (((n : ℚ) + 1) ^ 2) by
      linarith [hcas]]
  field_simp

/-- The weight function `w n = 8n + 2 - 4 s₂(n)` of the increments. -/
def bwt (n : ℕ) : ℤ := 8 * (n : ℤ) + 2 - 4 * (s2 n : ℤ)

lemma bwt_strictMono : StrictMono bwt := by
  refine strictMono_nat_of_lt_succ ?_
  intro n
  have hs := s2_succ n
  have hv : (0 : ℤ) ≤ (padicValNat 2 (n + 1) : ℤ) := Int.natCast_nonneg _
  unfold bwt
  push_cast
  omega

lemma bratio_diff_ne_zero {x : ℚ} (hx : HalfOdd x) (n : ℕ) :
    bratio x (n + 1) - bratio x n ≠ 0 := by
  rw [bratio_diff hx n]
  have h0 := bq_ne_zero hx n
  have h1 := bq_ne_zero hx (n + 1)
  have hn : (((n : ℚ) + 1) ^ 2) ≠ 0 := by positivity
  exact one_div_ne_zero (by exact mul_ne_zero hn (mul_ne_zero h0 h1))

lemma val_bratio_diff {x : ℚ} (hx : HalfOdd x) (n : ℕ) :
    padicValRat 2 (bratio x (n + 1) - bratio x n) = bwt n := by
  have h0 := bq_ne_zero hx n
  have h1 := bq_ne_zero hx (n + 1)
  have hn1 : ((n : ℚ) + 1) ≠ 0 := by positivity
  have hn : (((n : ℚ) + 1) ^ 2) ≠ 0 := pow_ne_zero _ hn1
  have hvn : padicValRat 2 ((n : ℚ) + 1) = (padicValNat 2 (n + 1) : ℤ) := by
    rw [show ((n : ℚ) + 1) = ((n + 1 : ℕ) : ℚ) by push_cast; ring, padicValRat_two_natCast]
  rw [bratio_diff hx n, one_div, padicValRat.inv,
    padicValRat.mul hn (mul_ne_zero h0 h1), padicValRat.mul h0 h1,
    padicValRat.pow, hvn, val_bq hx n, val_bq hx (n + 1)]
  have hs := s2_succ n
  unfold bwt
  push_cast
  omega

/-- The Padé ratio row converges in `ℚ₂`, with exact tail valuations `8n + 2 - 4 s₂(n)`. -/
theorem bratio_limit {x : ℚ} (hx : HalfOdd x) :
    ∃ L : ℚ_[2], Tendsto (fun n => ((bratio x n : ℚ) : ℚ_[2])) atTop (𝓝 L) ∧
      ∀ n, L - ((bratio x n : ℚ) : ℚ_[2]) ≠ 0 ∧
        Padic.valuation (L - ((bratio x n : ℚ) : ℚ_[2])) = bwt n :=
  padic2_limit_of_strictMono_val (bratio_diff_ne_zero hx) (val_bratio_diff hx) bwt_strictMono

/-! ### 4. The limit of the Padé ratio row is `Ξ` -/

lemma val_brkDen {x : ℚ} (hx : HalfOdd x) (k : ℕ) :
    padicValRat 2 (brkDen x k) = -((k : ℤ) + 1) := by
  induction k with
  | zero =>
      have h : brkDen x 0 = x := by simp [brkDen]
      rw [h, hx.padicValRat_eq]
      norm_num
  | succ m ih =>
      have hne : brkDen x m ≠ 0 := brkDen_ne_zero hx m
      have hx1 : HalfOdd (x + ((m : ℚ) + 1)) := by
        have := hx.add_natCast (m + 1)
        push_cast at this ⊢
        exact this
      rw [brkDen_succ, padicValRat.mul hne hx1.ne_zero, ih, hx1.padicValRat_eq]
      push_cast
      ring

lemma val_factorial_rat (k : ℕ) :
    padicValRat 2 ((k.factorial : ℚ)) = (k : ℤ) - (s2 k : ℤ) := by
  rw [padicValRat_two_natCast, padicValNat_two_factorial]
  have : s2 k ≤ k := s2_le k
  omega

lemma xiTerm_ne_zero {x : ℚ} (hx : HalfOdd x) (k : ℕ) : xiTerm x k ≠ 0 := by
  have h1 : brk x k ≠ 0 := by
    unfold brk
    exact div_ne_zero (factorial_ne_zero_rat k) (brkDen_ne_zero hx k)
  have h2 : brk (1 - x) k ≠ 0 := by
    unfold brk
    exact div_ne_zero (factorial_ne_zero_rat k) (brkDen_ne_zero hx.one_sub k)
  exact mul_ne_zero h1 h2

lemma val_xiTerm {x : ℚ} (hx : HalfOdd x) (k : ℕ) :
    padicValRat 2 (xiTerm x k) = 4 * (k : ℤ) + 2 - 2 * (s2 k : ℤ) := by
  have hbrk : ∀ {z : ℚ}, HalfOdd z →
      padicValRat 2 (brk z k) = 2 * (k : ℤ) + 1 - (s2 k : ℤ) := by
    intro z hz
    unfold brk
    rw [padicValRat.div (factorial_ne_zero_rat k) (brkDen_ne_zero hz k), val_factorial_rat,
      val_brkDen hz]
    ring
  unfold xiTerm
  rw [padicValRat.mul (by
      unfold brk; exact div_ne_zero (factorial_ne_zero_rat k) (brkDen_ne_zero hx k)) (by
      unfold brk; exact div_ne_zero (factorial_ne_zero_rat k) (brkDen_ne_zero hx.one_sub k)),
    hbrk hx, hbrk hx.one_sub]
  ring

lemma betaCoef_ne_zero {x : ℚ} (hx : HalfOdd x) (k : ℕ) : betaCoef (x ^ 2 - x) k ≠ 0 := by
  induction k with
  | zero => simp
  | succ m ih =>
      rw [betaCoef_succ]
      refine mul_ne_zero ih ?_
      have h1 : HalfOdd (x + (m : ℚ)) := hx.add_natCast m
      have h2 : HalfOdd (x + (-(1 + (m : ℤ)) : ℤ)) := hx.add_intCast _
      have hfac : (x ^ 2 - x) - (m : ℚ) * ((m : ℚ) + 1)
          = (x + (m : ℚ)) * (x + ((-(1 + (m : ℤ)) : ℤ) : ℚ)) := by push_cast; ring
      rw [hfac]
      exact mul_ne_zero h1.ne_zero h2.ne_zero

lemma val_betaCoef {x : ℚ} (hx : HalfOdd x) (k : ℕ) :
    padicValRat 2 (betaCoef (x ^ 2 - x) k) = -2 * (k : ℤ) := by
  induction k with
  | zero => simp
  | succ m ih =>
      have h1 : HalfOdd (x + (m : ℚ)) := hx.add_natCast m
      have h2 : HalfOdd (x + ((-(1 + (m : ℤ)) : ℤ) : ℚ)) := hx.add_intCast _
      have hfac : (x ^ 2 - x) - (m : ℚ) * ((m : ℚ) + 1)
          = (x + (m : ℚ)) * (x + ((-(1 + (m : ℤ)) : ℤ) : ℚ)) := by push_cast; ring
      rw [betaCoef_succ, padicValRat.mul (betaCoef_ne_zero hx m) (by
        rw [hfac]; exact mul_ne_zero h1.ne_zero h2.ne_zero), ih, hfac,
        padicValRat.mul h1.ne_zero h2.ne_zero, h1.padicValRat_eq, h2.padicValRat_eq]
      push_cast
      ring

lemma gCoef_ne_zero {x : ℚ} (hx : HalfOdd x) (k : ℕ) : gCoef (x ^ 2 - x) k ≠ 0 := by
  unfold gCoef
  exact div_ne_zero (betaCoef_ne_zero hx k) (pow_ne_zero _ (factorial_ne_zero_rat k))

lemma val_gCoef {x : ℚ} (hx : HalfOdd x) (k : ℕ) :
    padicValRat 2 (gCoef (x ^ 2 - x) k) = -4 * (k : ℤ) + 2 * (s2 k : ℤ) := by
  unfold gCoef
  rw [padicValRat.div (betaCoef_ne_zero hx k) (pow_ne_zero _ (factorial_ne_zero_rat k)),
    val_betaCoef hx, padicValRat.pow, val_factorial_rat]
  ring

/-! #### Norms -/

lemma norm_xiTerm_eq {x : ℚ} (hx : HalfOdd x) (k : ℕ) :
    ‖((xiTerm x k : ℚ) : ℚ_[2])‖ = (2 : ℝ) ^ (-(4 * (k : ℤ) + 2 - 2 * (s2 k : ℤ))) := by
  rw [norm_ratCast_padic2 (xiTerm_ne_zero hx k), val_xiTerm hx]

lemma norm_gCoef_eq {x : ℚ} (hx : HalfOdd x) (k : ℕ) :
    ‖((gCoef (x ^ 2 - x) k : ℚ) : ℚ_[2])‖ = (2 : ℝ) ^ (4 * (k : ℤ) - 2 * (s2 k : ℤ)) := by
  rw [norm_ratCast_padic2 (gCoef_ne_zero hx k), val_gCoef hx]
  congr 1
  ring

/-- The exponent `4k + 2 - 2 s₂(k)` of the terms of Beukers' series is monotone. -/
lemma xiExp_mono : Monotone (fun k : ℕ => 4 * (k : ℤ) + 2 - 2 * (s2 k : ℤ)) := by
  refine monotone_nat_of_le_succ ?_
  intro n
  have hs := s2_succ n
  have hv : (0 : ℤ) ≤ (padicValNat 2 (n + 1) : ℤ) := Int.natCast_nonneg _
  push_cast
  omega

lemma norm_xiTail_le {x : ℚ} (hx : HalfOdd x) (k : ℕ) :
    ‖∑' j : ℕ, ((xiTerm x (j + k) : ℚ) : ℚ_[2])‖
      ≤ (2 : ℝ) ^ (-(4 * (k : ℤ) + 2 - 2 * (s2 k : ℤ))) := by
  refine le_trans (IsUltrametricDist.norm_tsum_le _) (ciSup_le ?_)
  intro j
  rw [norm_xiTerm_eq hx]
  refine zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) ?_
  have h := xiExp_mono (Nat.le_add_left k j)
  simp only at h
  push_cast at h ⊢
  omega

lemma xi_add_xiPart {x : ℚ} (hx : HalfOdd x) (k : ℕ) :
    XiPade x + ((xiPart x k : ℚ) : ℚ_[2])
      = -∑' j : ℕ, ((xiTerm x (j + k) : ℚ) : ℚ_[2]) := by
  have hs := summable_xiTerm hx
  have h := hs.sum_add_tsum_nat_add k
  have hcast : ((xiPart x k : ℚ) : ℚ_[2]) = ∑ i ∈ range k, ((xiTerm x i : ℚ) : ℚ_[2]) := by
    unfold xiPart
    push_cast
    ring
  unfold XiPade
  rw [hcast]
  linear_combination h

/-- The key identity: `Ξ q_n - p_n = -∑_{k≤n} (n choose k) g_k T_k` with `T_k` the tail of
Beukers' series. -/
lemma xi_mul_bq_sub_bp {x : ℚ} (hx : HalfOdd x) (n : ℕ) :
    XiPade x * ((bq x n : ℚ) : ℚ_[2]) - ((bp x n : ℚ) : ℚ_[2])
      = ∑ k ∈ range (n + 1),
          -((((n.choose k : ℚ) * gCoef (x ^ 2 - x) k : ℚ)) : ℚ_[2])
            * (∑' j : ℕ, ((xiTerm x (j + k) : ℚ) : ℚ_[2])) := by
  have hq : ((bq x n : ℚ) : ℚ_[2])
      = ∑ k ∈ range (n + 1), ((((n.choose k : ℚ) * gCoef (x ^ 2 - x) k : ℚ)) : ℚ_[2]) := by
    rw [bq_eq_qSum]
    unfold qSum qPart
    push_cast
    ring
  have hp : ((bp x n : ℚ) : ℚ_[2])
      = -∑ k ∈ range (n + 1), ((((n.choose k : ℚ) * gCoef (x ^ 2 - x) k : ℚ)) : ℚ_[2])
          * ((xiPart x k : ℚ) : ℚ_[2]) := by
    rw [bp_eq_pSum hx]
    unfold pSum pPart pWeight
    push_cast
    ring_nf
  rw [hq, hp, sub_neg_eq_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro k _
  have h := xi_add_xiPart hx k
  linear_combination ((((n.choose k : ℚ) * gCoef (x ^ 2 - x) k : ℚ)) : ℚ_[2]) * h

lemma norm_xi_mul_bq_sub_bp_le {x : ℚ} (hx : HalfOdd x) (n : ℕ) :
    ‖XiPade x * ((bq x n : ℚ) : ℚ_[2]) - ((bp x n : ℚ) : ℚ_[2])‖ ≤ (1 : ℝ) / 4 := by
  rw [xi_mul_bq_sub_bp hx n]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by norm_num) ?_
  intro k _
  rw [neg_mul, norm_neg, norm_mul]
  have hchoose : ‖(((n.choose k : ℚ)) : ℚ_[2])‖ ≤ 1 := by
    have hc : (((n.choose k : ℚ)) : ℚ_[2]) = ((n.choose k : ℤ) : ℚ_[2]) := by push_cast; ring
    rw [hc]
    exact Padic.norm_int_le_one _
  have hsplit : ((((n.choose k : ℚ) * gCoef (x ^ 2 - x) k : ℚ)) : ℚ_[2])
      = (((n.choose k : ℚ)) : ℚ_[2]) * ((gCoef (x ^ 2 - x) k : ℚ) : ℚ_[2]) := by
    push_cast
    ring
  rw [hsplit, norm_mul]
  have hg := norm_gCoef_eq hx k
  have ht := norm_xiTail_le hx k
  have hgpos : (0 : ℝ) ≤ ‖((gCoef (x ^ 2 - x) k : ℚ) : ℚ_[2])‖ := norm_nonneg _
  calc ‖(((n.choose k : ℚ)) : ℚ_[2])‖ * ‖((gCoef (x ^ 2 - x) k : ℚ) : ℚ_[2])‖
        * ‖∑' j : ℕ, ((xiTerm x (j + k) : ℚ) : ℚ_[2])‖
      ≤ 1 * ((2 : ℝ) ^ (4 * (k : ℤ) - 2 * (s2 k : ℤ)))
          * ((2 : ℝ) ^ (-(4 * (k : ℤ) + 2 - 2 * (s2 k : ℤ)))) := by
        refine mul_le_mul (mul_le_mul hchoose (le_of_eq hg) hgpos (by norm_num)) ht
          (norm_nonneg _) (by positivity)
    _ = (1 : ℝ) / 4 := by
        rw [one_mul, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
        norm_num

/-- `Ξ` is the `2`-adic limit of the Padé ratios. -/
theorem tendsto_bratio_XiPade {x : ℚ} (hx : HalfOdd x) :
    Tendsto (fun n => ((bratio x n : ℚ) : ℚ_[2])) atTop (𝓝 (XiPade x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hbound : ∀ n : ℕ,
      ‖((bratio x n : ℚ) : ℚ_[2]) - XiPade x‖ ≤ (1 / 4 : ℝ) * (1 / 4 : ℝ) ^ n := by
    intro n
    have hqne : ((bq x n : ℚ) : ℚ_[2]) ≠ 0 := by
      simpa using (Rat.cast_injective (α := ℚ_[2])).ne_iff.mpr (bq_ne_zero hx n)
    have hr : ((bratio x n : ℚ) : ℚ_[2]) - XiPade x
        = -((XiPade x * ((bq x n : ℚ) : ℚ_[2]) - ((bp x n : ℚ) : ℚ_[2]))
            / ((bq x n : ℚ) : ℚ_[2])) := by
      have : ((bratio x n : ℚ) : ℚ_[2])
          = ((bp x n : ℚ) : ℚ_[2]) / ((bq x n : ℚ) : ℚ_[2]) := by
        unfold bratio
        push_cast
        ring
      rw [this]
      field_simp
      ring
    have hnq : ‖((bq x n : ℚ) : ℚ_[2])‖ = (2 : ℝ) ^ (4 * (n : ℤ) - 2 * (s2 n : ℤ)) := by
      rw [norm_ratCast_padic2 (bq_ne_zero hx n), val_bq hx]
      congr 1
      ring
    have hqpos : (0 : ℝ) < ‖((bq x n : ℚ) : ℚ_[2])‖ := by
      rw [hnq]; positivity
    rw [hr, norm_neg, norm_div, div_le_iff₀ hqpos]
    have h1 := norm_xi_mul_bq_sub_bp_le hx n
    have h2 : (1 : ℝ) / 4 ≤ (1 / 4 : ℝ) * (1 / 4 : ℝ) ^ n * ‖((bq x n : ℚ) : ℚ_[2])‖ := by
      have hs : (s2 n : ℤ) ≤ (n : ℤ) := by exact_mod_cast s2_le n
      have hpow : ((1 : ℝ) / 4) ^ n = (2 : ℝ) ^ (-(2 * (n : ℤ))) := by
        rw [show (-(2 * (n : ℤ))) = (-2 : ℤ) * (n : ℤ) by ring, zpow_mul, zpow_natCast]
        norm_num
      have hmul : (2 : ℝ) ^ (-(2 * (n : ℤ))) * (2 : ℝ) ^ (4 * (n : ℤ) - 2 * (s2 n : ℤ))
          = (2 : ℝ) ^ (2 * (n : ℤ) - 2 * (s2 n : ℤ)) := by
        rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
        congr 1
        ring
      have hge : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * (n : ℤ) - 2 * (s2 n : ℤ)) :=
        one_le_zpow₀ (by norm_num) (by omega)
      calc (1 : ℝ) / 4 = 1 / 4 * 1 := by ring
        _ ≤ 1 / 4 * (2 : ℝ) ^ (2 * (n : ℤ) - 2 * (s2 n : ℤ)) := by linarith
        _ = (1 / 4 : ℝ) * (1 / 4 : ℝ) ^ n * ‖((bq x n : ℚ) : ℚ_[2])‖ := by
            rw [hnq, hpow, mul_assoc, hmul]
    linarith [h1, h2]
  refine squeeze_zero (fun n => norm_nonneg _) hbound ?_
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
  simpa using h.const_mul (1 / 4 : ℝ)

/-! ### 5. The estimate -/

/-- The exact norm of the Padé remainder: `‖p_n - Ξ q_n‖ = 2^{2 s₂(n) - 4n - 2}`. -/
theorem norm_bp_sub_xi_mul_bq {x : ℚ} (hx : HalfOdd x) (n : ℕ) :
    ‖((bp x n : ℚ) : ℚ_[2]) - XiPade x * ((bq x n : ℚ) : ℚ_[2])‖
      = (2 : ℝ) ^ (2 * (s2 n : ℤ) - 4 * (n : ℤ) - 2) := by
  obtain ⟨L, hL, htail⟩ := bratio_limit hx
  have hLxi : L = XiPade x := tendsto_nhds_unique hL (tendsto_bratio_XiPade hx)
  obtain ⟨hne, hval⟩ := htail n
  rw [← hLxi]
  have hnorm : ‖L - ((bratio x n : ℚ) : ℚ_[2])‖ = (2 : ℝ) ^ (-(bwt n)) := by
    rw [Padic.norm_eq_zpow_neg_valuation hne, hval]
    norm_num
  have hqne : ((bq x n : ℚ) : ℚ_[2]) ≠ 0 := by
    simpa using (Rat.cast_injective (α := ℚ_[2])).ne_iff.mpr (bq_ne_zero hx n)
  have hfac : ((bp x n : ℚ) : ℚ_[2]) - L * ((bq x n : ℚ) : ℚ_[2])
      = -(((bq x n : ℚ) : ℚ_[2]) * (L - ((bratio x n : ℚ) : ℚ_[2]))) := by
    have hr : ((bratio x n : ℚ) : ℚ_[2]) * ((bq x n : ℚ) : ℚ_[2]) = ((bp x n : ℚ) : ℚ_[2]) := by
      have : ((bratio x n : ℚ) : ℚ_[2])
          = ((bp x n : ℚ) : ℚ_[2]) / ((bq x n : ℚ) : ℚ_[2]) := by
        unfold bratio; push_cast; ring
      rw [this]
      field_simp
    linear_combination -hr
  have hnq : ‖((bq x n : ℚ) : ℚ_[2])‖ = (2 : ℝ) ^ (4 * (n : ℤ) - 2 * (s2 n : ℤ)) := by
    rw [norm_ratCast_padic2 (bq_ne_zero hx n), val_bq hx]
    congr 1
    ring
  rw [hfac, norm_neg, norm_mul, hnq, hnorm, ← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
  congr 1
  unfold bwt
  ring

lemma two_pow_s2_le (n : ℕ) : 2 ^ s2 n ≤ n + 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
      · have hm2 : n = 2 * m := by omega
        have hs : s2 n = s2 m := by rw [hm2, s2_two_mul]
        have hmn : m < n := by omega
        have := ih m hmn
        rw [hs]
        omega
      · have hs : s2 n = s2 m + 1 := by
          have hd : Nat.digits 2 n = n % 2 :: Nat.digits 2 (n / 2) :=
            Nat.digits_def' (by norm_num) hn
          have h1 : n % 2 = 1 := by omega
          have h2 : n / 2 = m := by omega
          simp [s2, hd, h1, h2]
          ring
        have hmn : m < n := by omega
        have := ih m hmn
        rw [hs, pow_succ]
        omega

/-- **Beukers' uniform `2`-adic Padé estimate** (Lemma 3.1; Beukers, Proposition 7.1(4)):
for odd `a` and `n ≥ 1`, `‖p_n(a/2) - Ξ(a/2) q_n(a/2)‖₂ ≤ 4 n² 2^{-4n}`. -/
theorem beukers_pade_estimate (a : ℤ) (ha : Odd a) (n : ℕ) (hn : 1 ≤ n) :
    ‖((bp ((a : ℚ) / 2) n : ℚ) : ℚ_[2]) -
        XiPade ((a : ℚ) / 2) * ((bq ((a : ℚ) / 2) n : ℚ) : ℚ_[2])‖
      ≤ 4 * (n : ℝ) ^ 2 * (2 : ℝ) ^ (-(4 * (n : ℤ))) := by
  have hx : HalfOdd ((a : ℚ) / 2) := ⟨a, ha, rfl⟩
  rw [norm_bp_sub_xi_mul_bq hx n]
  have hA : (2 : ℝ) ^ (2 * (s2 n : ℤ) - 2) = ((2 : ℝ) ^ (s2 n)) ^ 2 / 4 := by
    rw [zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0),
      show (2 * (s2 n : ℤ)) = ((s2 n : ℤ)) * 2 by ring, zpow_mul, zpow_natCast]
    norm_num
    norm_cast
  have hpow : (2 : ℝ) ^ (2 * (s2 n : ℤ) - 4 * (n : ℤ) - 2)
      = ((2 : ℝ) ^ (s2 n)) ^ 2 / 4 * (2 : ℝ) ^ (-(4 * (n : ℤ))) := by
    rw [show (2 * (s2 n : ℤ) - 4 * (n : ℤ) - 2)
        = (2 * (s2 n : ℤ) - 2) + (-(4 * (n : ℤ))) by ring,
      zpow_add₀ (by norm_num : (2:ℝ) ≠ 0), hA]
  rw [hpow]
  have hle : ((2 : ℝ) ^ (s2 n)) ^ 2 / 4 ≤ 4 * (n : ℝ) ^ 2 := by
    have h1 : (2 : ℝ) ^ (s2 n) ≤ (n : ℝ) + 1 := by
      have := two_pow_s2_le n
      have hc : ((2 ^ s2 n : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at hc
      exact hc
    have h2 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h3 : (0 : ℝ) < (2 : ℝ) ^ (s2 n) := by positivity
    nlinarith [h1, h2, h3]
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (-(4 * (n : ℤ))) := by positivity
  exact mul_le_mul_of_nonneg_right hle (le_of_lt hpos)

end Catalan
