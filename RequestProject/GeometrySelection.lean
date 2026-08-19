import RequestProject.Final
import RequestProject.RateTools
import RequestProject.Lattice2
import RequestProject.CongruenceLattice

/-!
# The geometry-of-numbers step

Sections 19–22 of the base note, proved here rather than imported.

Given two integer rows `(X₁, Y₁)`, `(X₂, Y₂)` with `Xᵢ = S aᵢ`, a division modulus `M = S T`
with `T` dividing the reduced cross determinant `a₁Y₂ - a₂Y₁`, and the crossed gap
`A₁ + E₂ < A₂ + E₁`, we produce the balanced-minima data of Theorem 11.1.

The construction, for each `n`:

* `CongrLattice.exists_thinned_basis` gives two explicit vectors `w₁, w₂ ∈ ℤ²` all of whose
  integer combinations `c` make both `q(c) = (c₁X₁+c₂X₂)/M` and `p(c) = (c₁Y₁+c₂Y₂)/M` integers,
  and whose determinant `δ` lies in the window `[M, 2M]`;
* the plane lattice spanned by `(q, qα - p)` therefore has covolume
  `𝒟 = δ |X₁Y₂ - X₂Y₁| / M² ∈ [|Δ|/M, 2|Δ|/M]`;
* `Lattice2.exists_balanced_pair` (two-dimensional Minkowski) applied to the rectangle with
  half-widths `U = e^{Hn}`, `V = 2𝒟/U` returns a basis with `|b₁| ≤ (μU, μV)` and
  `|b₂,₂| ≤ V/μ`, for some `0 < μ ≤ 1`;
* writing `μ = e^{-r n}` gives exactly the estimates (22.20), (22.21), (22.23) and (22.25).

`lattice_selection` is the resulting theorem.
-/

namespace Catalan

open Filter Topology

namespace Geometry

open Lattice2 CongrLattice

private lemma four_le_exp_two : (4 : ℝ) ≤ Real.exp 2 := by
  have h : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (1 : ℝ)]

/-- **One step of the construction.**  For a single index, the double-congruence lattice, its
thinning and two-dimensional Minkowski produce a pair of divided rows with the required
estimates relative to the rectangle half-width `U`. -/
lemma single_step (α : ℝ) (a1 a2 Y1 Y2 S T : ℤ) (hS : 0 < S) (hT : 0 < T)
    (hdvd : T ∣ a1 * Y2 - a2 * Y1)
    (hDelta : S * a1 * Y2 - S * a2 * Y1 ≠ 0)
    (U : ℝ) (hU : 0 < U) :
    ∃ (Q1 P1 Q2 P2 : ℤ) (mu D : ℝ), 0 < mu ∧ mu ≤ 1 ∧ 0 < D ∧
      |((S * a1 * Y2 - S * a2 * Y1 : ℤ) : ℝ)| ≤ ((S * T : ℤ) : ℝ) * D ∧
      ((S * T : ℤ) : ℝ) * D ≤ 2 * |((S * a1 * Y2 - S * a2 * Y1 : ℤ) : ℝ)| ∧
      |(Q1 : ℝ)| ≤ mu * U ∧
      |(Q1 : ℝ) * α - (P1 : ℝ)| ≤ mu * (2 * D / U) ∧
      |(Q2 : ℝ) * α - (P2 : ℝ)| ≤ (2 * D / U) / mu ∧
      |((Q1 * P2 - Q2 * P1 : ℤ) : ℝ)| = D := by
  obtain ⟨w1, w2, δ, hδ1, hδ2, hdet, hd1, hd2, he1, he2⟩ :=
    exists_thinned_basis a1 a2 Y1 Y2 S T hS hT hdvd
  obtain ⟨q1, hq1⟩ := hd1
  obtain ⟨q2, hq2⟩ := hd2
  obtain ⟨p1, hp1⟩ := he1
  obtain ⟨p2, hp2⟩ := he2
  have hMpos : (0 : ℤ) < S * T := by positivity
  have hδpos : (0 : ℤ) < δ := lt_of_lt_of_le hMpos hδ1
  -- the integral Plücker relation
  have h2 : (a1 * w1.1 + a2 * w1.2) * (Y1 * w2.1 + Y2 * w2.2)
      - (a1 * w2.1 + a2 * w2.2) * (Y1 * w1.1 + Y2 * w1.2) = (a1 * Y2 - a2 * Y1) * δ := by
    rw [← hdet]; ring
  have h1 : (T * q1) * (S * T * p2) - (T * q2) * (S * T * p1) = (a1 * Y2 - a2 * Y1) * δ := by
    rw [← hq1, ← hq2, ← hp1, ← hp2]; exact h2
  have hkey : (S * T) ^ 2 * (q1 * p2 - q2 * p1) = δ * (S * a1 * Y2 - S * a2 * Y1) := by
    calc (S * T) ^ 2 * (q1 * p2 - q2 * p1)
        = S * ((T * q1) * (S * T * p2) - (T * q2) * (S * T * p1)) := by ring
      _ = S * ((a1 * Y2 - a2 * Y1) * δ) := by rw [h1]
      _ = δ * (S * a1 * Y2 - S * a2 * Y1) := by ring
  have hdne : q1 * p2 - q2 * p1 ≠ 0 := by
    intro h
    have hz : δ * (S * a1 * Y2 - S * a2 * Y1) = 0 := by rw [← hkey, h]; ring
    rcases mul_eq_zero.mp hz with h' | h'
    · omega
    · exact hDelta h'
  -- real quantities
  set MR : ℝ := ((S * T : ℤ) : ℝ) with hMR
  set DR : ℝ := |((q1 * p2 - q2 * p1 : ℤ) : ℝ)| with hDR
  set AB : ℝ := |((S * a1 * Y2 - S * a2 * Y1 : ℤ) : ℝ)| with hAB
  have hMRpos : 0 < MR := by rw [hMR]; exact_mod_cast hMpos
  have hDRpos : 0 < DR := by
    rw [hDR]
    have : ((q1 * p2 - q2 * p1 : ℤ) : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hdne
    exact abs_pos.mpr this
  have habs : MR ^ 2 * DR = ((δ : ℤ) : ℝ) * AB := by
    have hc := congrArg (fun z : ℤ => (z : ℝ)) hkey
    simp only at hc
    push_cast at hc
    rw [hMR, hDR, hAB]
    push_cast
    rw [← abs_of_pos (show (0:ℝ) < ((S:ℝ) * T) ^ 2 by positivity),
      ← abs_of_pos (show (0:ℝ) < (δ : ℝ) by exact_mod_cast hδpos), ← abs_mul, ← abs_mul]
    rw [hc]
  have hδR1 : MR ≤ ((δ : ℤ) : ℝ) := by rw [hMR]; exact_mod_cast hδ1
  have hδR2 : ((δ : ℤ) : ℝ) ≤ 2 * MR := by rw [hMR]; exact_mod_cast hδ2
  have hABpos : 0 < AB := by
    rw [hAB]
    exact abs_pos.mpr (Int.cast_ne_zero.mpr hDelta)
  have hlow : AB ≤ MR * DR := by nlinarith [habs, hMRpos, hABpos, hDRpos, hδR1]
  have hhigh : MR * DR ≤ 2 * AB := by nlinarith [habs, hMRpos, hABpos, hDRpos, hδR2]
  -- the plane lattice
  set v : ℝ × ℝ := ((q1 : ℝ), (q1 : ℝ) * α - (p1 : ℝ)) with hv
  set w : ℝ × ℝ := ((q2 : ℝ), (q2 : ℝ) * α - (p2 : ℝ)) with hw
  have hdet2v : det2 v w = -((q1 * p2 - q2 * p1 : ℤ) : ℝ) := by
    rw [hv, hw, det2]
    push_cast
    ring
  have hdet2ne : det2 v w ≠ 0 := by
    rw [hdet2v]
    exact neg_ne_zero.mpr (Int.cast_ne_zero.mpr hdne)
  have hdet2abs : |det2 v w| = DR := by rw [hdet2v, abs_neg, hDR]
  set V : ℝ := 2 * DR / U with hV
  have hVpos : 0 < V := by rw [hV]; positivity
  have harea : U * V = 2 * |det2 v w| := by
    rw [hV, hdet2abs]
    field_simp
  obtain ⟨m1, n1, m2, n2, mu, hmu0, hmu1, hunim, hb1, hb2, hb3⟩ :=
    exists_balanced_pair v w hdet2ne U V hU hVpos harea
  refine ⟨m1 * q1 + n1 * q2, m1 * p1 + n1 * p2, m2 * q1 + n2 * q2, m2 * p1 + n2 * p2,
    mu, DR, hmu0, hmu1, hDRpos, hlow, hhigh, ?_, ?_, ?_, ?_⟩
  · have he : (comb v w m1 n1).1 = ((m1 * q1 + n1 * q2 : ℤ) : ℝ) := by
      rw [comb_fst, hv, hw]; push_cast; ring
    rw [← he]; exact hb1
  · have he : (comb v w m1 n1).2
        = ((m1 * q1 + n1 * q2 : ℤ) : ℝ) * α - ((m1 * p1 + n1 * p2 : ℤ) : ℝ) := by
      rw [comb_snd, hv, hw]; push_cast; ring
    rw [← he, ← hV]; exact hb2
  · have he : (comb v w m2 n2).2
        = ((m2 * q1 + n2 * q2 : ℤ) : ℝ) * α - ((m2 * p1 + n2 * p2 : ℤ) : ℝ) := by
      rw [comb_snd, hv, hw]; push_cast; ring
    rw [← he, ← hV]; exact hb3
  · have hi : (m1 * q1 + n1 * q2) * (m2 * p1 + n2 * p2)
        - (m2 * q1 + n2 * q2) * (m1 * p1 + n1 * p2) = q1 * p2 - q2 * p1 := by
      have : (m1 * q1 + n1 * q2) * (m2 * p1 + n2 * p2)
          - (m2 * q1 + n2 * q2) * (m1 * p1 + n1 * p2)
          = (m1 * n2 - n1 * m2) * (q1 * p2 - q2 * p1) := by ring
      rw [this, hunim, one_mul]
    rw [hi, hDR]

end Geometry

/-! ### The selection theorem -/

open Geometry Lattice2

/-- **The core of the geometry-of-numbers step.**  Given the two rows, the modulus `M = S T`
dividing the reduced cross determinant, the rate `L` of the cross determinant `Del`, the rate `σ`
of `M`, and rates `H, F` with `H + F = L - σ`, the balanced rectangle with half-widths
`U = e^{Hn}`, `V = 2𝒟/U` produces the balanced-minima data. -/
theorem selection_core (α H F L σ : ℝ) (a1 a2 Y1 Y2 S T Del : ℕ → ℤ)
    (hS : ∀ n, 0 < S n) (hT : ∀ n, 0 < T n)
    (hdvd : ∀ n, T n ∣ a1 n * Y2 n - a2 n * Y1 n)
    (hDel : ∀ n, Del n = S n * a1 n * Y2 n - S n * a2 n * Y1 n)
    (rDelta : LogRate (fun n => ((Del n : ℤ) : ℝ)) L)
    (hDne : ∀ᶠ n in atTop, Del n ≠ 0)
    (rM : LogRate (fun n => ((S n * T n : ℤ) : ℝ)) σ)
    (hHF : H + F = L - σ) :
    Nonempty (BalancedMinimaData α H F) := by
  have hFval : F = L - σ - H := by linarith
  obtain ⟨th1, hth1⟩ : ∃ f : ℕ → ℝ, f = fun n => Real.log |((Del n : ℤ) : ℝ)| / n - L :=
    ⟨_, rfl⟩
  obtain ⟨th2, hth2⟩ : ∃ f : ℕ → ℝ, f = fun n => Real.log |((S n * T n : ℤ) : ℝ)| / n - σ :=
    ⟨_, rfl⟩
  obtain ⟨eps, heps⟩ : ∃ f : ℕ → ℝ, f = fun n => |th1 n| + |th2 n| + 4 / ((n : ℝ) + 1) :=
    ⟨_, rfl⟩
  have heps_pos : ∀ n, 0 < eps n := by
    intro n
    simp only [heps]
    have h : (0 : ℝ) < 4 / ((n : ℝ) + 1) := by positivity
    have := abs_nonneg (th1 n)
    have := abs_nonneg (th2 n)
    linarith
  have hlbA : ∀ n : ℕ, 4 / ((n : ℝ) + 1) ≤ eps n - th1 n + th2 n := by
    intro n
    simp only [heps]
    have ha := le_abs_self (th1 n)
    have hb := neg_abs_le (th2 n)
    linarith
  have hlbB : ∀ n : ℕ, 0 ≤ th1 n - th2 n + eps n := by
    intro n
    simp only [heps]
    have ha := neg_abs_le (th1 n)
    have hb := le_abs_self (th2 n)
    have hc : (0 : ℝ) < 4 / ((n : ℝ) + 1) := by positivity
    linarith
  have hlbC : ∀ n : ℕ, 4 / ((n : ℝ) + 1) ≤ eps n := by
    intro n
    simp only [heps]
    have := abs_nonneg (th1 n)
    have := abs_nonneg (th2 n)
    linarith
  -- the error sequence tends to zero
  have hone : Tendsto (fun n : ℕ => 4 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
  have hth1_zero : Tendsto th1 atTop (𝓝 0) := by
    have h := rDelta.sub (tendsto_const_nhds (x := L) (f := atTop (α := ℕ)))
    rw [sub_self] at h
    rw [hth1]
    exact h
  have hth2_zero : Tendsto th2 atTop (𝓝 0) := by
    have h := rM.sub (tendsto_const_nhds (x := σ) (f := atTop (α := ℕ)))
    rw [sub_self] at h
    rw [hth2]
    exact h
  have heps_zero : Tendsto eps atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => |th1 n|) atTop (𝓝 0) := by simpa using hth1_zero.abs
    have h2 : Tendsto (fun n : ℕ => |th2 n|) atTop (𝓝 0) := by simpa using hth2_zero.abs
    have h3 := (h1.add h2).add hone
    rw [heps]
    simpa using h3
  have hsqrt : Tendsto (fun n : ℕ => Real.sqrt (eps n) * n) atTop atTop := by
    have hkey : ∀ n : ℕ, 1 ≤ n → Real.sqrt (2 * (n : ℝ)) ≤ Real.sqrt (eps n) * n := by
      intro n hn
      have hN : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have h4 : (2 : ℝ) * n ≤ 4 / ((n : ℝ) + 1) * n ^ 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
        nlinarith
      have h3 : 4 / ((n : ℝ) + 1) * n ^ 2 ≤ eps n * n ^ 2 :=
        mul_le_mul_of_nonneg_right (hlbC n) (sq_nonneg _)
      calc Real.sqrt (2 * (n : ℝ)) ≤ Real.sqrt (eps n * n ^ 2) :=
            Real.sqrt_le_sqrt (by linarith)
        _ = Real.sqrt (eps n) * n := by
            rw [Real.sqrt_mul (heps_pos n).le, Real.sqrt_sq (Nat.cast_nonneg n)]
    have hbig : Tendsto (fun n : ℕ => Real.sqrt (2 * (n : ℝ))) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp
        (Filter.Tendsto.const_mul_atTop (by norm_num) tendsto_natCast_atTop_atTop)
    refine tendsto_atTop_mono' atTop ?_ hbig
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    exact hkey n hn
  -- the per-index construction
  have key : ∀ n : ℕ, ∃ (Q1 P1 Q2 P2 : ℤ) (r : ℝ), 0 ≤ r ∧
      (1 ≤ n → Del n ≠ 0 →
        |(Q1 : ℝ)| ≤ Real.exp ((H - r + eps n) * n) ∧
        |(Q1 : ℝ) * α - (P1 : ℝ)| ≤ Real.exp ((F - r + eps n) * n) ∧
        |(Q2 : ℝ) * α - (P2 : ℝ)| ≤ Real.exp ((F + r + eps n) * n) ∧
        Real.exp ((H + F - eps n) * n) ≤ |((Q1 * P2 - Q2 * P1 : ℤ) : ℝ)|) := by
    intro n
    by_cases hgood : 1 ≤ n ∧ Del n ≠ 0
    · obtain ⟨hn1, hDn⟩ := hgood
      have hN : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
      have hNpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hNne : (n : ℝ) ≠ 0 := ne_of_gt hNpos
      obtain ⟨Q1, P1, Q2, P2, mu, D, hmu0, hmu1, hDpos, hlow, hhigh, b1, b2, b3, bdet⟩ :=
        single_step α (a1 n) (a2 n) (Y1 n) (Y2 n) (S n) (T n) (hS n) (hT n) (hdvd n)
          (by rw [← hDel n]; exact hDn) (Real.exp (H * n)) (Real.exp_pos _)
      refine ⟨Q1, P1, Q2, P2, -Real.log mu / n, ?_, ?_⟩
      · have hlm : Real.log mu ≤ 0 := Real.log_nonpos hmu0.le hmu1
        exact div_nonneg (by linarith) (Nat.cast_nonneg n)
      intro _ _
      obtain ⟨r, hr⟩ : ∃ r : ℝ, r = -Real.log mu / n := ⟨_, rfl⟩
      rw [← hr]
      have hmuexp : mu = Real.exp (-r * n) := by
        have he : -r * (n : ℝ) = Real.log mu := by rw [hr]; field_simp
        rw [he, Real.exp_log hmu0]
      -- the two exponential identities
      have hABval : |((Del n : ℤ) : ℝ)| = Real.exp ((L + th1 n) * n) := by
        have hpos : (0 : ℝ) < |((Del n : ℤ) : ℝ)| := abs_pos.mpr (Int.cast_ne_zero.mpr hDn)
        have he : (L + th1 n) * (n : ℝ) = Real.log |((Del n : ℤ) : ℝ)| := by
          simp only [hth1]; field_simp; ring
        rw [he, Real.exp_log hpos]
      have hMpos : (0 : ℝ) < ((S n * T n : ℤ) : ℝ) := by
        have h : (0 : ℤ) < S n * T n := mul_pos (hS n) (hT n)
        exact_mod_cast h
      have hMval : ((S n * T n : ℤ) : ℝ) = Real.exp ((σ + th2 n) * n) := by
        have he : (σ + th2 n) * (n : ℝ) = Real.log ((S n * T n : ℤ) : ℝ) := by
          simp only [hth2, abs_of_pos hMpos]; field_simp; ring
        rw [he, Real.exp_log hMpos]
      have hDeltaEq : ((S n * a1 n * Y2 n - S n * a2 n * Y1 n : ℤ) : ℝ) = ((Del n : ℤ) : ℝ) := by
        rw [hDel n]
      rw [hDeltaEq, hABval, hMval] at hlow hhigh
      -- bounds on the covolume
      have hD_lb : Real.exp ((L + th1 n) * n - (σ + th2 n) * n) ≤ D := by
        rw [Real.exp_sub, div_le_iff₀ (Real.exp_pos _)]
        calc Real.exp ((L + th1 n) * n) ≤ Real.exp ((σ + th2 n) * n) * D := hlow
          _ = D * Real.exp ((σ + th2 n) * n) := mul_comm _ _
      have hD_ub : D ≤ 2 * Real.exp ((L + th1 n) * n - (σ + th2 n) * n) := by
        rw [Real.exp_sub, ← mul_div_assoc, le_div_iff₀ (Real.exp_pos _), mul_comm D]
        exact hhigh
      -- the height of the rectangle
      have hVle : 2 * D / Real.exp (H * n) ≤ Real.exp ((F + eps n) * n) := by
        have hfac : (4 : ℝ) ≤ Real.exp ((eps n - th1 n + th2 n) * n) := by
          refine le_trans four_le_exp_two (Real.exp_le_exp.mpr ?_)
          have h2 : (2 : ℝ) ≤ 4 / ((n : ℝ) + 1) * n := by
            rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
            linarith
          have h3 : 4 / ((n : ℝ) + 1) * n ≤ (eps n - th1 n + th2 n) * n :=
            mul_le_mul_of_nonneg_right (hlbA n) hNpos.le
          linarith
        have h2 : 4 * Real.exp ((L + th1 n) * n - (σ + th2 n) * n)
            ≤ Real.exp ((F + eps n) * n) * Real.exp (H * n) := by
          rw [← Real.exp_add]
          have hexpeq : (F + eps n) * (n : ℝ) + H * n
              = ((L + th1 n) * n - (σ + th2 n) * n) + (eps n - th1 n + th2 n) * n := by
            rw [hFval]; ring
          rw [hexpeq, Real.exp_add]
          have hmul := mul_le_mul_of_nonneg_left hfac
            (Real.exp_pos ((L + th1 n) * (n : ℝ) - (σ + th2 n) * n)).le
          linarith
        rw [div_le_iff₀ (Real.exp_pos _)]
        linarith
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine le_trans b1 ?_
        rw [hmuexp, ← Real.exp_add]
        refine Real.exp_le_exp.mpr ?_
        have hd : (H - r + eps n) * (n : ℝ) - (-r * n + H * n) = eps n * n := by ring
        have : 0 ≤ eps n * (n : ℝ) := mul_nonneg (heps_pos n).le hNpos.le
        linarith
      · refine le_trans b2 ?_
        have hstep : mu * (2 * D / Real.exp (H * n)) ≤ mu * Real.exp ((F + eps n) * n) :=
          mul_le_mul_of_nonneg_left hVle hmu0.le
        refine le_trans hstep ?_
        rw [hmuexp, ← Real.exp_add]
        exact Real.exp_le_exp.mpr (le_of_eq (by ring))
      · refine le_trans b3 ?_
        have hstep : 2 * D / Real.exp (H * n) / mu ≤ Real.exp ((F + eps n) * n) / mu := by
          gcongr
        refine le_trans hstep ?_
        rw [hmuexp, ← Real.exp_sub]
        exact Real.exp_le_exp.mpr (le_of_eq (by ring))
      · rw [bdet]
        refine le_trans ?_ hD_lb
        refine Real.exp_le_exp.mpr ?_
        have hd : ((L + th1 n) * (n : ℝ) - (σ + th2 n) * n) - (H + F - eps n) * n
            = (th1 n - th2 n + eps n) * n := by rw [hHF]; ring
        have : 0 ≤ (th1 n - th2 n + eps n) * (n : ℝ) := mul_nonneg (hlbB n) hNpos.le
        linarith
    · exact ⟨0, 0, 0, 0, 0, le_rfl, fun h1 h2 => absurd ⟨h1, h2⟩ hgood⟩
  choose Q1 P1 Q2 P2 r hr hbounds using key
  refine ⟨{
    Q1 := Q1, Q2 := Q2, P1 := P1, P2 := P2, r := r, eps := eps
    r_nonneg := hr
    eps_pos := heps_pos
    eps_tendsto := heps_zero
    sqrt_eps_mul_tendsto := hsqrt
    bound_Q1 := ?_
    bound_l1 := ?_
    bound_l2 := ?_
    bound_det := ?_ }⟩
  · filter_upwards [Filter.eventually_ge_atTop 1, hDne] with n h1 h2
    exact (hbounds n h1 h2).1
  · filter_upwards [Filter.eventually_ge_atTop 1, hDne] with n h1 h2
    exact (hbounds n h1 h2).2.1
  · filter_upwards [Filter.eventually_ge_atTop 1, hDne] with n h1 h2
    exact (hbounds n h1 h2).2.2.1
  · filter_upwards [Filter.eventually_ge_atTop 1, hDne] with n h1 h2
    exact (hbounds n h1 h2).2.2.2

/-- **The geometry-of-numbers step (Sections 19–22 of the base note).**  From two integer rows
with the stated archimedean rates, a division modulus `M = S T` whose factor `T` divides the
reduced cross determinant, and the crossed gap `A₁ + E₂ < A₂ + E₁`, one obtains the
balanced-minima data of Theorem 11.1 at the rates `H = A₂ - x` and `F = x + E₁ - σ`, where
`x = (σ + E₂ - E₁)/2`. -/
theorem lattice_selection (α A1 E1 A2 E2 σ : ℝ) (a1 a2 Y1 Y2 S T : ℕ → ℤ)
    (hS : ∀ n, 0 < S n) (hT : ∀ n, 0 < T n)
    (rX1 : LogRate (fun n => ((S n * a1 n : ℤ) : ℝ)) A1)
    (rl1 : LogRate (fun n => ((S n * a1 n : ℤ) : ℝ) * α - ((Y1 n : ℤ) : ℝ)) E1)
    (rX2 : LogRate (fun n => ((S n * a2 n : ℤ) : ℝ)) A2)
    (rl2 : LogRate (fun n => ((S n * a2 n : ℤ) : ℝ) * α - ((Y2 n : ℤ) : ℝ)) E2)
    (rM : LogRate (fun n => ((S n * T n : ℤ) : ℝ)) σ)
    (hdvd : ∀ n, T n ∣ a1 n * Y2 n - a2 n * Y1 n)
    (hgap : A1 + E2 < A2 + E1)
    (hX2ne : ∀ᶠ n in atTop, ((S n * a2 n : ℤ) : ℝ) ≠ 0)
    (hl1ne : ∀ᶠ n in atTop, ((S n * a1 n : ℤ) : ℝ) * α - ((Y1 n : ℤ) : ℝ) ≠ 0) :
    Nonempty (BalancedMinimaData α (A2 - (σ + E2 - E1) / 2) ((σ + E2 - E1) / 2 + E1 - σ)) := by
  have hfg : ∀ n : ℕ,
      ((S n * a2 n : ℤ) : ℝ) * (((S n * a1 n : ℤ) : ℝ) * α - ((Y1 n : ℤ) : ℝ))
        - ((S n * a1 n : ℤ) : ℝ) * (((S n * a2 n : ℤ) : ℝ) * α - ((Y2 n : ℤ) : ℝ))
        = ((S n * a1 n * Y2 n - S n * a2 n * Y1 n : ℤ) : ℝ) := by
    intro n
    push_cast
    ring
  have hfrate : LogRate
      (fun n => ((S n * a2 n : ℤ) : ℝ) * (((S n * a1 n : ℤ) : ℝ) * α - ((Y1 n : ℤ) : ℝ)))
      (A2 + E1) := rX2.mul rl1 hX2ne hl1ne
  have hgrate : LogRateLE
      (fun n => ((S n * a1 n : ℤ) : ℝ) * (((S n * a2 n : ℤ) : ℝ) * α - ((Y2 n : ℤ) : ℝ)))
      (A1 + E2) := rX1.toLE.mul rl2.toLE
  have hfne : ∀ᶠ n in atTop,
      ((S n * a2 n : ℤ) : ℝ) * (((S n * a1 n : ℤ) : ℝ) * α - ((Y1 n : ℤ) : ℝ)) ≠ 0 := by
    filter_upwards [hX2ne, hl1ne] with n h1 h2
    exact mul_ne_zero h1 h2
  obtain ⟨rDelta0, hDne0⟩ := LogRate.sub_dominant hfrate hgrate hgap hfne
  refine selection_core α _ _ (A2 + E1) σ a1 a2 Y1 Y2 S T
    (fun n => S n * a1 n * Y2 n - S n * a2 n * Y1 n) hS hT hdvd (fun n => rfl)
    (rDelta0.of_eq hfg) ?_ rM (by ring)
  filter_upwards [hDne0] with n hn
  intro h
  apply hn
  rw [hfg n, h]
  simp

end Catalan
