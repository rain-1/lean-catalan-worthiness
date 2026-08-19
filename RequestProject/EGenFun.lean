import RequestProject.AnalyticTools
import RequestProject.CatalanAccel
import RequestProject.EClosedFormA
import RequestProject.LinearForms

/-!
# Generating functions of the modular `E`-family

The two closed forms

`A_n = ∑_{k ≤ n} C(2k,k)^2 (-4)^{n-k} C(k, n-k)`,
`B_n = ∑_{k ≤ n} C(2k,k)^2 c_k (-4)^{n-k} C(k, n-k)`

say that the generating functions of `A` and of `B` are obtained from the two series
`F(w) = ∑_k C(2k,k)^2 w^k` and `Γ(w) = ∑_k C(2k,k)^2 c_k w^k` by the Legendre substitution
`w = x (1 - 4x)`.  Both `F` and `Γ` have radius of convergence `1/16`, and `w = x(1-4x)` maps
`[0, 1/8)` into `[0, 1/16)`; the substitution identity, elementary for `x` near `0` where the
double series converges absolutely, extends to the whole interval by the identity theorem for
real analytic functions (`Catalan.subst_identity`).
-/

namespace Catalan

open Filter Topology Finset Set

/-- `C(2k,k)^2`, the coefficient sequence of `F`. -/
noncomputable def abin (k : ℕ) : ℝ := (Nat.centralBinom k : ℝ) ^ 2

/-- `c_k` as a real number. -/
noncomputable def cRe (k : ℕ) : ℝ := ((cCoef k : ℚ) : ℝ)

/-- `F(w) = ∑_k C(2k,k)^2 w^k`. -/
noncomputable def Fgen (w : ℝ) : ℝ := ∑' k, abin k * w ^ k

/-- `Γ(w) = ∑_k C(2k,k)^2 c_k w^k`. -/
noncomputable def Ggen (w : ℝ) : ℝ := ∑' k, (abin k * cRe k) * w ^ k

/-- The generating function of the modular denominators `A_n`. -/
noncomputable def fA (x : ℝ) : ℝ := ∑' n, aRe n * x ^ n

/-- The generating function of the modular numerators `B_n`. -/
noncomputable def fB (x : ℝ) : ℝ := ∑' n, bRe n * x ^ n

lemma cRe_nonneg (k : ℕ) : 0 ≤ cRe k := cCoef_nonneg k

lemma cRe_le (k : ℕ) : cRe k ≤ catalanReal / 2 := cCoef_le k

lemma abin_pos (k : ℕ) : 0 < abin k := by
  have : (0 : ℝ) < (Nat.centralBinom k : ℝ) := by exact_mod_cast Nat.centralBinom_pos k
  unfold abin; positivity

lemma abin_le (k : ℕ) : abin k ≤ 16 ^ k := by
  have h : (Nat.centralBinom k : ℝ) ≤ 4 ^ k := by
    exact_mod_cast centralBinom_le_four_pow k
  have h0 : (0 : ℝ) ≤ (Nat.centralBinom k : ℝ) := by positivity
  calc abin k = (Nat.centralBinom k : ℝ) ^ 2 := rfl
    _ ≤ (4 ^ k : ℝ) ^ 2 := by exact pow_le_pow_left₀ h0 h 2
    _ = 16 ^ k := by rw [← pow_mul, mul_comm k 2, pow_mul]; norm_num

/-! ### The closed forms as statements about real coefficients -/

lemma aRe_eq_subCoef (n : ℕ) : aRe n = subCoef abin n := by
  have h := Ae_closed_form n
  have := congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_neg,
    Rat.cast_ofNat] at this
  rw [aRe, this, subCoef]
  refine Finset.sum_congr rfl (fun k _ => by rw [abin])

lemma bRe_eq_subCoef (n : ℕ) : bRe n = subCoef (fun k => abin k * cRe k) n := by
  have h := Be_closed_form n
  have := congrArg (fun q : ℚ => (q : ℝ)) h
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_neg,
    Rat.cast_ofNat] at this
  rw [bRe, this, subCoef]
  refine Finset.sum_congr rfl (fun k _ => by rw [abin, cRe])

/-! ### Growth bounds -/

/-- The explicit bound on the modular linear form: `|ℓ_n| ≤ 512 K (n+1)^5 4^n`. -/
lemma linE_abs_le (n : ℕ) :
    |GEreal / 2 * aRe n - bRe n| ≤ 512 * geomPoly4 * ((n : ℝ) + 1) ^ 5 * 4 ^ n := by
  have hT : 0 ≤ ∑' k, tE (n + k) := le_trans (tE_pos n).le (tail_tE_lb n)
  have hA := aRe_pos n
  have heq := linE_eq n
  have habs : |GEreal / 2 * aRe n - bRe n| = aRe n / 2 * (∑' k, tE (n + k)) := by
    rw [heq, abs_of_nonneg (by positivity)]
  rw [habs]
  have h1 : aRe n / 2 ≤ ((n : ℝ) + 1) * 8 ^ n / 2 := by
    have := aRe_ub n; linarith
  have h2 : ∑' k, tE (n + k) ≤ 64 * geomPoly4 * ((n : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ n :=
    tail_tE_ub n
  have hpos2 : (0 : ℝ) ≤ 64 * geomPoly4 * ((n : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ n := by
    have := geomPoly4_pos; positivity
  have hstep : aRe n / 2 * (∑' k, tE (n + k))
      ≤ ((n : ℝ) + 1) * 8 ^ n / 2 * (64 * geomPoly4 * ((n : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ n) :=
    mul_le_mul h1 h2 hT (by positivity)
  refine hstep.trans ?_
  have hpow : (8 : ℝ) ^ n * (1 / 2 : ℝ) ^ n = 4 ^ n := by
    rw [← mul_pow]; norm_num
  have hn2 : ((n : ℝ) + 2) ^ 4 ≤ 16 * ((n : ℝ) + 1) ^ 4 := by
    have h : ((n : ℝ) + 2) ≤ 2 * ((n : ℝ) + 1) := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    calc ((n : ℝ) + 2) ^ 4 ≤ (2 * ((n : ℝ) + 1)) ^ 4 := by
          exact pow_le_pow_left₀ (by positivity) h 4
      _ = 16 * ((n : ℝ) + 1) ^ 4 := by ring
  have hK := geomPoly4_pos
  have hn1 : (0 : ℝ) ≤ ((n : ℝ) + 1) := by positivity
  calc ((n : ℝ) + 1) * 8 ^ n / 2 * (64 * geomPoly4 * ((n : ℝ) + 2) ^ 4 * (1 / 2 : ℝ) ^ n)
      = 32 * geomPoly4 * (((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 4) * ((8 : ℝ) ^ n * (1 / 2 : ℝ) ^ n) := by
        ring
    _ = 32 * geomPoly4 * (((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 4) * 4 ^ n := by rw [hpow]
    _ ≤ 32 * geomPoly4 * (((n : ℝ) + 1) * (16 * ((n : ℝ) + 1) ^ 4)) * 4 ^ n := by
        have : ((n : ℝ) + 1) * ((n : ℝ) + 2) ^ 4 ≤ ((n : ℝ) + 1) * (16 * ((n : ℝ) + 1) ^ 4) :=
          mul_le_mul_of_nonneg_left hn2 hn1
        have h32 : (0 : ℝ) ≤ 32 * geomPoly4 := by positivity
        have := mul_le_mul_of_nonneg_left this h32
        exact mul_le_mul_of_nonneg_right this (by positivity)
    _ = 512 * geomPoly4 * ((n : ℝ) + 1) ^ 5 * 4 ^ n := by ring

lemma aRe_abs_le (n : ℕ) : |aRe n| ≤ ((n : ℝ) + 1) ^ 5 * 8 ^ n := by
  rw [abs_of_pos (aRe_pos n)]
  refine (aRe_ub n).trans ?_
  have h1 : ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) ^ 5 := by
    have h : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    calc ((n : ℝ) + 1) = ((n : ℝ) + 1) ^ 1 := (pow_one _).symm
      _ ≤ ((n : ℝ) + 1) ^ 5 := pow_le_pow_right₀ h (by norm_num)
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-- `|B_n| ≤ C (n+1)^5 8^n`. -/
lemma bRe_abs_le (n : ℕ) :
    |bRe n| ≤ (GEreal / 2 + 512 * geomPoly4) * ((n : ℝ) + 1) ^ 5 * 8 ^ n := by
  have h1 := linE_abs_le n
  have h2 := aRe_abs_le n
  have hGE : 0 < GEreal := GEreal_pos
  have hb : |bRe n| ≤ |GEreal / 2 * aRe n| + |GEreal / 2 * aRe n - bRe n| := by
    have h := abs_sub (GEreal / 2 * aRe n) (GEreal / 2 * aRe n - bRe n)
    simpa using h
  refine hb.trans ?_
  have h3 : |GEreal / 2 * aRe n| ≤ GEreal / 2 * (((n : ℝ) + 1) ^ 5 * 8 ^ n) := by
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < GEreal / 2)]
    exact mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : (4 : ℝ) ^ n ≤ 8 ^ n := by
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have h5 : 512 * geomPoly4 * ((n : ℝ) + 1) ^ 5 * 4 ^ n
      ≤ 512 * geomPoly4 * ((n : ℝ) + 1) ^ 5 * 8 ^ n := by
    have := geomPoly4_pos
    exact mul_le_mul_of_nonneg_left h4 (by positivity)
  linarith [h1.trans h5]

/-! ### Summability -/

lemma summable_aRe_pow (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 8) :
    Summable (fun n => ‖aRe n‖ * ρ ^ n) := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_succ_pow_mul_geometric 5 (r := 8 * ρ) (by positivity) (by linarith))
  rw [Real.norm_eq_abs]
  calc |aRe n| * ρ ^ n ≤ (((n : ℝ) + 1) ^ 5 * 8 ^ n) * ρ ^ n :=
        mul_le_mul_of_nonneg_right (aRe_abs_le n) (by positivity)
    _ = ((n : ℝ) + 1) ^ 5 * (8 * ρ) ^ n := by rw [mul_pow]; ring

lemma summable_bRe_pow (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ : ρ < 1 / 8) :
    Summable (fun n => ‖bRe n‖ * ρ ^ n) := by
  have hC : (0 : ℝ) ≤ GEreal / 2 + 512 * geomPoly4 := by
    have := geomPoly4_pos; have := GEreal_pos; positivity
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_succ_pow_mul_geometric 5 (r := 8 * ρ) (by positivity)
      (by linarith)).mul_left (GEreal / 2 + 512 * geomPoly4))
  rw [Real.norm_eq_abs]
  calc |bRe n| * ρ ^ n
      ≤ ((GEreal / 2 + 512 * geomPoly4) * ((n : ℝ) + 1) ^ 5 * 8 ^ n) * ρ ^ n :=
        mul_le_mul_of_nonneg_right (bRe_abs_le n) (by positivity)
    _ = (GEreal / 2 + 512 * geomPoly4) * (((n : ℝ) + 1) ^ 5 * (8 * ρ) ^ n) := by
        rw [mul_pow]; ring

lemma summable_abin_pow (w : ℝ) (hw : |w| < 1 / 16) : Summable (fun k => abin k * w ^ k) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
    (summable_geometric_of_lt_one (by positivity) (show 16 * |w| < 1 by linarith))
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (abin_pos k), abs_pow]
  calc abin k * |w| ^ k ≤ 16 ^ k * |w| ^ k :=
        mul_le_mul_of_nonneg_right (abin_le k) (by positivity)
    _ = (16 * |w|) ^ k := by rw [mul_pow]

/-! ### The substitution identities -/

/-- On `(-1/24, 1/8)` the Legendre substitution is legitimate for the denominators. -/
theorem fA_eq_Fser {x : ℝ} (hx : x ∈ Ioo (-(1 / 24) : ℝ) (1 / 8)) :
    fA x = Fgen (x * (1 - 4 * x)) := by
  have := subst_identity abin aRe aRe_eq_subCoef 1
    (fun k => by rw [abs_of_pos (abin_pos k), one_mul]; exact abin_le k)
    summable_aRe_pow hx
  rw [fA, Fgen, this]

/-- On `(-1/24, 1/8)` the Legendre substitution is legitimate for the numerators. -/
theorem fB_eq_Gser {x : ℝ} (hx : x ∈ Ioo (-(1 / 24) : ℝ) (1 / 8)) :
    fB x = Ggen (x * (1 - 4 * x)) := by
  have hbound : ∀ k, |abin k * cRe k| ≤ (catalanReal / 2) * 16 ^ k := by
    intro k
    rw [abs_mul, abs_of_pos (abin_pos k), abs_of_nonneg (cRe_nonneg k)]
    calc abin k * cRe k ≤ 16 ^ k * (catalanReal / 2) :=
          mul_le_mul (abin_le k) (cRe_le k) (cRe_nonneg k) (by positivity)
      _ = (catalanReal / 2) * 16 ^ k := by ring
  have := subst_identity (fun k => abin k * cRe k) bRe bRe_eq_subCoef (catalanReal / 2)
    hbound summable_bRe_pow hx
  rw [fB, Ggen, this]

end Catalan
