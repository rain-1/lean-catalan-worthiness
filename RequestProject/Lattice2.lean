import Mathlib

/-!
# Elementary two-dimensional lattice reduction

This file proves, from scratch, the two-dimensional case of Minkowski's theorems on successive
minima, in the sharp enough form needed for the balanced two-row selection.

Everything is phrased with explicit coordinates.  A lattice is presented by two vectors
`v w : ℝ × ℝ` with `det2 v w ≠ 0`; its points are the integer combinations `comb v w m n`.

The main result is `exists_reduced_basis`: there is a basis `b₁ = comb v w m₁ n₁`,
`b₂ = comb v w m₂ n₂` of the lattice (unimodular coefficient matrix, so
`det2 b₁ b₂ = det2 v w`) with

`3 ‖b₁‖⁴ ≤ 4 det²`  and  `3 ‖b₁‖² ‖b₂‖² ≤ 4 det²`.

The first inequality is Minkowski's first theorem, the second Minkowski's second theorem, both in
dimension two.  The proof is the classical one: take `b₁` of minimal length, complete it to a
basis by Bézout, reduce the second vector modulo `b₁`, and use the Lagrange identity
`det² + ⟨b₁,b₂⟩² = ‖b₁‖² ‖b₂‖²`.

`exists_balanced_pair` is the rescaled form actually used: for a rectangle `[-U,U] × [-V,V]` of
area `4 U V = 8 |det|` one gets a basis with `|b₁| ≤ (μU, μV)` and `|b₂,₂| ≤ V/μ` for some
`0 < μ ≤ 1`.
-/

namespace Catalan

namespace Lattice2

/-- Squared Euclidean norm. -/
def nsq (x : ℝ × ℝ) : ℝ := x.1 ^ 2 + x.2 ^ 2

/-- Euclidean inner product. -/
def dot (x y : ℝ × ℝ) : ℝ := x.1 * y.1 + x.2 * y.2

/-- Determinant of a pair of plane vectors. -/
def det2 (x y : ℝ × ℝ) : ℝ := x.1 * y.2 - x.2 * y.1

/-- The lattice point with coefficients `(m, n)` in the basis `(v, w)`. -/
def comb (v w : ℝ × ℝ) (m n : ℤ) : ℝ × ℝ :=
  ((m : ℝ) * v.1 + (n : ℝ) * w.1, (m : ℝ) * v.2 + (n : ℝ) * w.2)

@[simp] lemma comb_fst (v w : ℝ × ℝ) (m n : ℤ) :
    (comb v w m n).1 = (m : ℝ) * v.1 + (n : ℝ) * w.1 := rfl

@[simp] lemma comb_snd (v w : ℝ × ℝ) (m n : ℤ) :
    (comb v w m n).2 = (m : ℝ) * v.2 + (n : ℝ) * w.2 := rfl

lemma nsq_nonneg (x : ℝ × ℝ) : 0 ≤ nsq x := by
  unfold nsq; positivity

lemma abs_fst_le_sqrt_nsq (x : ℝ × ℝ) : |x.1| ≤ Real.sqrt (nsq x) := by
  have h : x.1 ^ 2 ≤ nsq x := by unfold nsq; nlinarith [sq_nonneg x.2]
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq_eq_abs] at this

lemma abs_snd_le_sqrt_nsq (x : ℝ × ℝ) : |x.2| ≤ Real.sqrt (nsq x) := by
  have h : x.2 ^ 2 ≤ nsq x := by unfold nsq; nlinarith [sq_nonneg x.1]
  have := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq_eq_abs] at this

/-- The Lagrange identity in dimension two. -/
lemma lagrange (x y : ℝ × ℝ) : det2 x y ^ 2 + dot x y ^ 2 = nsq x * nsq y := by
  unfold det2 dot nsq; ring

lemma det2_comb (v w : ℝ × ℝ) (m n m' n' : ℤ) :
    det2 (comb v w m n) (comb v w m' n') = ((m * n' - n * m' : ℤ) : ℝ) * det2 v w := by
  unfold det2
  simp only [comb_fst, comb_snd]
  push_cast
  ring

lemma comb_sub_smul (v w : ℝ × ℝ) (m n k m₁ n₁ : ℤ) :
    comb v w (m - k * m₁) (n - k * n₁)
      = ((comb v w m n).1 - (k : ℝ) * (comb v w m₁ n₁).1,
         (comb v w m n).2 - (k : ℝ) * (comb v w m₁ n₁).2) := by
  simp only [comb, Prod.mk.injEq]
  constructor <;> push_cast <;> ring

lemma nsq_comb_mul (v w : ℝ × ℝ) (k m n : ℤ) :
    nsq (comb v w (k * m) (k * n)) = (k : ℝ) ^ 2 * nsq (comb v w m n) := by
  unfold nsq
  simp only [comb_fst, comb_snd]
  push_cast
  ring

lemma dot_sub_smul (x y : ℝ × ℝ) (k : ℝ) :
    dot x (y.1 - k * x.1, y.2 - k * x.2) = dot x y - k * nsq x := by
  unfold dot nsq; ring

/-- The coefficients can be recovered from the point. -/
lemma coeff_fst (v w : ℝ × ℝ) (m n : ℤ) (hD : det2 v w ≠ 0) :
    (m : ℝ) = ((comb v w m n).1 * w.2 - (comb v w m n).2 * w.1) / det2 v w := by
  rw [eq_div_iff hD]
  unfold det2
  simp only [comb_fst, comb_snd]
  ring

lemma coeff_snd (v w : ℝ × ℝ) (m n : ℤ) (hD : det2 v w ≠ 0) :
    (n : ℝ) = ((comb v w m n).2 * v.1 - (comb v w m n).1 * v.2) / det2 v w := by
  rw [eq_div_iff hD]
  unfold det2
  simp only [comb_fst, comb_snd]
  ring

lemma nsq_pos_of_ne_zero {v w : ℝ × ℝ} (hD : det2 v w ≠ 0) {m n : ℤ} (h : ¬(m = 0 ∧ n = 0)) :
    0 < nsq (comb v w m n) := by
  rcases lt_or_eq_of_le (nsq_nonneg (comb v w m n)) with h' | h'
  · exact h'
  · exfalso
    have h1 : (comb v w m n).1 = 0 ∧ (comb v w m n).2 = 0 := by
      have h2 := h'.symm
      unfold nsq at h2
      constructor <;> nlinarith [sq_nonneg (comb v w m n).1, sq_nonneg (comb v w m n).2]
    have hm : (m : ℝ) = 0 := by
      rw [coeff_fst v w m n hD, h1.1, h1.2]; simp
    have hn : (n : ℝ) = 0 := by
      rw [coeff_snd v w m n hD, h1.1, h1.2]; simp
    exact h ⟨by exact_mod_cast hm, by exact_mod_cast hn⟩

private lemma abs_sub_le_add (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rcases abs_cases a with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases abs_cases b with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
    rcases abs_cases (a - b) with ⟨h5, h6⟩ | ⟨h5, h6⟩ <;> linarith

/-- The lattice points of bounded length form a finite set of coefficient pairs. -/
lemma finite_bounded (v w : ℝ × ℝ) (hD : det2 v w ≠ 0) (R : ℝ) :
    {p : ℤ × ℤ | nsq (comb v w p.1 p.2) ≤ R}.Finite := by
  set B : ℝ := (Real.sqrt (max R 0) * (|w.1| + |w.2| + |v.1| + |v.2|)) / |det2 v w| with hB
  have hDpos : 0 < |det2 v w| := abs_pos.mpr hD
  refine Set.Finite.subset (Set.finite_Icc ((⌈-B⌉, ⌈-B⌉) : ℤ × ℤ) (⌊B⌋, ⌊B⌋)) ?_
  rintro ⟨m, n⟩ hp
  simp only [Set.mem_setOf_eq] at hp
  have hsq : 0 ≤ Real.sqrt (max R 0) := Real.sqrt_nonneg _
  have hmax : nsq (comb v w m n) ≤ max R 0 := le_trans hp (le_max_left _ _)
  have hx1 : |(comb v w m n).1| ≤ Real.sqrt (max R 0) :=
    le_trans (abs_fst_le_sqrt_nsq _) (Real.sqrt_le_sqrt hmax)
  have hx2 : |(comb v w m n).2| ≤ Real.sqrt (max R 0) :=
    le_trans (abs_snd_le_sqrt_nsq _) (Real.sqrt_le_sqrt hmax)
  have hmB : |(m : ℝ)| ≤ B := by
    have hnum : |(comb v w m n).1 * w.2 - (comb v w m n).2 * w.1|
        ≤ Real.sqrt (max R 0) * (|w.1| + |w.2| + |v.1| + |v.2|) := by
      calc |(comb v w m n).1 * w.2 - (comb v w m n).2 * w.1|
          ≤ |(comb v w m n).1 * w.2| + |(comb v w m n).2 * w.1| := abs_sub_le_add _ _
        _ = |(comb v w m n).1| * |w.2| + |(comb v w m n).2| * |w.1| := by rw [abs_mul, abs_mul]
        _ ≤ Real.sqrt (max R 0) * |w.2| + Real.sqrt (max R 0) * |w.1| := by
            gcongr
        _ ≤ Real.sqrt (max R 0) * (|w.1| + |w.2| + |v.1| + |v.2|) := by
            nlinarith [abs_nonneg v.1, abs_nonneg v.2, abs_nonneg w.1, abs_nonneg w.2]
    rw [coeff_fst v w m n hD, abs_div, hB]
    gcongr
  have hnB : |(n : ℝ)| ≤ B := by
    have hnum : |(comb v w m n).2 * v.1 - (comb v w m n).1 * v.2|
        ≤ Real.sqrt (max R 0) * (|w.1| + |w.2| + |v.1| + |v.2|) := by
      calc |(comb v w m n).2 * v.1 - (comb v w m n).1 * v.2|
          ≤ |(comb v w m n).2 * v.1| + |(comb v w m n).1 * v.2| := abs_sub_le_add _ _
        _ = |(comb v w m n).2| * |v.1| + |(comb v w m n).1| * |v.2| := by rw [abs_mul, abs_mul]
        _ ≤ Real.sqrt (max R 0) * |v.1| + Real.sqrt (max R 0) * |v.2| := by
            gcongr
        _ ≤ Real.sqrt (max R 0) * (|w.1| + |w.2| + |v.1| + |v.2|) := by
            nlinarith [abs_nonneg v.1, abs_nonneg v.2, abs_nonneg w.1, abs_nonneg w.2]
    rw [coeff_snd v w m n hD, abs_div, hB]
    gcongr
  rw [abs_le] at hmB hnB
  simp only [Set.mem_Icc, Prod.le_def]
  exact ⟨⟨Int.ceil_le.mpr hmB.1, Int.ceil_le.mpr hnB.1⟩,
    ⟨Int.le_floor.mpr hmB.2, Int.le_floor.mpr hnB.2⟩⟩

/-- A shortest nonzero lattice vector exists. -/
lemma exists_min_nsq (v w : ℝ × ℝ) (hD : det2 v w ≠ 0) :
    ∃ m₁ n₁ : ℤ, ¬(m₁ = 0 ∧ n₁ = 0) ∧
      ∀ m n : ℤ, ¬(m = 0 ∧ n = 0) → nsq (comb v w m₁ n₁) ≤ nsq (comb v w m n) := by
  set R : ℝ := nsq (comb v w 1 0) with hR
  set T : Set (ℤ × ℤ) := {p | ¬(p.1 = 0 ∧ p.2 = 0) ∧ nsq (comb v w p.1 p.2) ≤ R} with hT
  have hTfin : T.Finite := (finite_bounded v w hD R).subset (fun p hp => hp.2)
  have hTne : T.Nonempty := ⟨(1, 0), by refine ⟨by simp, le_rfl⟩⟩
  obtain ⟨p, hpT, hmin⟩ := Set.exists_min_image T (fun p => nsq (comb v w p.1 p.2)) hTfin hTne
  refine ⟨p.1, p.2, hpT.1, ?_⟩
  intro m n hmn
  by_cases h : nsq (comb v w m n) ≤ R
  · exact hmin (m, n) ⟨hmn, h⟩
  · push_neg at h
    exact le_trans hpT.2 h.le

/-- A shortest nonzero lattice vector is primitive. -/
lemma gcd_eq_one_of_min {v w : ℝ × ℝ} (hD : det2 v w ≠ 0) {m₁ n₁ : ℤ}
    (h0 : ¬(m₁ = 0 ∧ n₁ = 0))
    (hmin : ∀ m n : ℤ, ¬(m = 0 ∧ n = 0) → nsq (comb v w m₁ n₁) ≤ nsq (comb v w m n)) :
    Int.gcd m₁ n₁ = 1 := by
  set g : ℕ := Int.gcd m₁ n₁ with hg
  have hgne : g ≠ 0 := by
    intro h
    rw [hg, Int.gcd_eq_zero_iff] at h
    exact h0 h
  by_contra hne
  have hg2 : 2 ≤ g := by omega
  obtain ⟨m', hm'⟩ : (g : ℤ) ∣ m₁ := Int.gcd_dvd_left m₁ n₁
  obtain ⟨n', hn'⟩ : (g : ℤ) ∣ n₁ := Int.gcd_dvd_right m₁ n₁
  have h0' : ¬(m' = 0 ∧ n' = 0) := by
    rintro ⟨rfl, rfl⟩
    exact h0 ⟨by simp [hm'], by simp [hn']⟩
  have hpos : 0 < nsq (comb v w m' n') := nsq_pos_of_ne_zero hD h0'
  have hle := hmin m' n' h0'
  have heq : nsq (comb v w m₁ n₁) = (g : ℝ) ^ 2 * nsq (comb v w m' n') := by
    rw [hm', hn']
    exact nsq_comb_mul v w (g : ℤ) m' n'
  have hgR : (2 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg2
  have h4 : (4 : ℝ) ≤ (g : ℝ) ^ 2 := by nlinarith
  have h5 := mul_le_mul_of_nonneg_right h4 hpos.le
  linarith [heq, hle, hpos, h5]

/-- A primitive vector can be completed to a basis. -/
lemma exists_complement {m₁ n₁ : ℤ} (h : Int.gcd m₁ n₁ = 1) :
    ∃ m₂ n₂ : ℤ, m₁ * n₂ - n₁ * m₂ = 1 := by
  have hb := Int.gcd_eq_gcd_ab m₁ n₁
  rw [h] at hb
  push_cast at hb
  exact ⟨-(Int.gcdB m₁ n₁), Int.gcdA m₁ n₁, by linarith [hb]⟩

/-- **Two-dimensional Minkowski reduction.**  Any plane lattice has a basis `b₁, b₂` with
`3 ‖b₁‖⁴ ≤ 4 det²` and `3 ‖b₁‖²‖b₂‖² ≤ 4 det²`. -/
theorem exists_reduced_basis (v w : ℝ × ℝ) (hD : det2 v w ≠ 0) :
    ∃ m₁ n₁ m₂ n₂ : ℤ, m₁ * n₂ - n₁ * m₂ = 1 ∧
      0 < nsq (comb v w m₁ n₁) ∧
      3 * nsq (comb v w m₁ n₁) ^ 2 ≤ 4 * det2 v w ^ 2 ∧
      3 * (nsq (comb v w m₁ n₁) * nsq (comb v w m₂ n₂)) ≤ 4 * det2 v w ^ 2 := by
  obtain ⟨m₁, n₁, h0, hmin⟩ := exists_min_nsq v w hD
  obtain ⟨m₀, n₀, hbez⟩ := exists_complement (gcd_eq_one_of_min hD h0 hmin)
  set b₁ : ℝ × ℝ := comb v w m₁ n₁ with hb₁
  set s : ℝ := nsq b₁ with hs
  have hspos : 0 < s := nsq_pos_of_ne_zero hD h0
  set k : ℤ := round (dot b₁ (comb v w m₀ n₀) / s) with hk
  refine ⟨m₁, n₁, m₀ - k * m₁, n₀ - k * n₁, by ring_nf; linarith [hbez], hspos, ?_, ?_⟩
  all_goals {
    set b₂ : ℝ × ℝ := comb v w (m₀ - k * m₁) (n₀ - k * n₁) with hb₂
    have hb₂eq : b₂ = ((comb v w m₀ n₀).1 - (k : ℝ) * b₁.1,
        (comb v w m₀ n₀).2 - (k : ℝ) * b₁.2) := comb_sub_smul v w m₀ n₀ k m₁ n₁
    have hdotval : dot b₁ b₂ = dot b₁ (comb v w m₀ n₀) - (k : ℝ) * s := by
      rw [hb₂eq]; exact dot_sub_smul b₁ (comb v w m₀ n₀) (k : ℝ)
    have hdotabs : |dot b₁ b₂| ≤ s / 2 := by
      have : dot b₁ b₂ = s * (dot b₁ (comb v w m₀ n₀) / s - (k : ℝ)) := by
        rw [hdotval]; field_simp
      rw [this, abs_mul, abs_of_pos hspos]
      have hround : |dot b₁ (comb v w m₀ n₀) / s - (k : ℝ)| ≤ 1 / 2 := by
        rw [hk]; exact abs_sub_round _
      nlinarith [hspos, hround]
    have hdotsq : dot b₁ b₂ ^ 2 ≤ s ^ 2 / 4 := by
      nlinarith [abs_nonneg (dot b₁ b₂), sq_abs (dot b₁ b₂), hdotabs, hspos]
    have hne2 : ¬(m₀ - k * m₁ = 0 ∧ n₀ - k * n₁ = 0) := by
      rintro ⟨h1, h2⟩
      have : m₁ * (n₀ - k * n₁) - n₁ * (m₀ - k * m₁) = 1 := by ring_nf; linarith [hbez]
      rw [h1, h2] at this
      simp at this
    have hmin2 : s ≤ nsq b₂ := hmin _ _ hne2
    have hdet : det2 b₁ b₂ = det2 v w := by
      rw [hb₁, hb₂, det2_comb]
      have : m₁ * (n₀ - k * n₁) - n₁ * (m₀ - k * m₁) = 1 := by ring_nf; linarith [hbez]
      rw [this]
      simp
    have hlag : det2 b₁ b₂ ^ 2 + dot b₁ b₂ ^ 2 = s * nsq b₂ := lagrange b₁ b₂
    rw [hdet] at hlag
    nlinarith [hspos, hmin2, hdotsq, hlag]
  }

/-! ### The rescaled form -/

lemma comb_scale (v w : ℝ × ℝ) (U V : ℝ) (m n : ℤ) :
    comb (v.1 / U, v.2 / V) (w.1 / U, w.2 / V) m n
      = ((comb v w m n).1 / U, (comb v w m n).2 / V) := by
  simp only [comb, Prod.mk.injEq]
  constructor <;> ring

lemma det2_scale (v w : ℝ × ℝ) (U V : ℝ) :
    det2 (v.1 / U, v.2 / V) (w.1 / U, w.2 / V) = det2 v w / (U * V) := by
  unfold det2
  simp only
  field_simp

/-- **The balanced-rectangle form of Minkowski's second theorem in the plane.**
For a rectangle of half-widths `U, V` with `U V = 2 |det|`, the lattice has a basis whose first
vector lies in `μ` times the rectangle, and whose second vector's second coordinate is at most
`V / μ`, for some `0 < μ ≤ 1`. -/
theorem exists_balanced_pair (v w : ℝ × ℝ) (hD : det2 v w ≠ 0) (U V : ℝ) (hU : 0 < U)
    (hV : 0 < V) (harea : U * V = 2 * |det2 v w|) :
    ∃ (m₁ n₁ m₂ n₂ : ℤ) (mu : ℝ), 0 < mu ∧ mu ≤ 1 ∧ m₁ * n₂ - n₁ * m₂ = 1 ∧
      |(comb v w m₁ n₁).1| ≤ mu * U ∧ |(comb v w m₁ n₁).2| ≤ mu * V ∧
      |(comb v w m₂ n₂).2| ≤ V / mu := by
  set v' : ℝ × ℝ := (v.1 / U, v.2 / V) with hv'
  set w' : ℝ × ℝ := (w.1 / U, w.2 / V) with hw'
  have hUV : U * V ≠ 0 := by positivity
  have hDabs : 0 < |det2 v w| := abs_pos.mpr hD
  have hD' : det2 v' w' = det2 v w / (U * V) := det2_scale v w U V
  have hD'ne : det2 v' w' ≠ 0 := by
    rw [hD']; exact div_ne_zero hD hUV
  have hD'sq : det2 v' w' ^ 2 = 1 / 4 := by
    rw [hD', div_pow, harea, ← sq_abs (det2 v w)]
    field_simp
    ring
  obtain ⟨m₁, n₁, m₂, n₂, hunim, hpos, hmin1, hmin2⟩ := exists_reduced_basis v' w' hD'ne
  rw [hD'sq] at hmin1 hmin2
  set s : ℝ := nsq (comb v' w' m₁ n₁) with hs
  set t : ℝ := nsq (comb v' w' m₂ n₂) with ht
  have hsle : s ≤ 1 := by nlinarith [hpos, hmin1]
  set mu : ℝ := Real.sqrt s with hmu
  have hmupos : 0 < mu := Real.sqrt_pos.mpr hpos
  have hmule : mu ≤ 1 := by
    rw [hmu, show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hsle
  have e1 : (comb v' w' m₁ n₁).1 = (comb v w m₁ n₁).1 / U := by
    rw [hv', hw', comb_scale]
  have e2 : (comb v' w' m₁ n₁).2 = (comb v w m₁ n₁).2 / V := by
    rw [hv', hw', comb_scale]
  have e4 : (comb v' w' m₂ n₂).2 = (comb v w m₂ n₂).2 / V := by
    rw [hv', hw', comb_scale]
  refine ⟨m₁, n₁, m₂, n₂, mu, hmupos, hmule, hunim, ?_, ?_, ?_⟩
  · have h := abs_fst_le_sqrt_nsq (comb v' w' m₁ n₁)
    rw [← hs, e1, abs_div, abs_of_pos hU, div_le_iff₀ hU] at h
    exact h
  · have h := abs_snd_le_sqrt_nsq (comb v' w' m₁ n₁)
    rw [← hs, e2, abs_div, abs_of_pos hV, div_le_iff₀ hV] at h
    exact h
  · have htle : t ≤ 1 / s := by
      rw [le_div_iff₀ hpos]
      nlinarith [hmin2, nsq_nonneg (comb v' w' m₂ n₂)]
    have h := abs_snd_le_sqrt_nsq (comb v' w' m₂ n₂)
    rw [← ht, e4, abs_div, abs_of_pos hV, div_le_iff₀ hV] at h
    have hst : Real.sqrt t ≤ 1 / mu := by
      have h1 : Real.sqrt t ≤ Real.sqrt (1 / s) := Real.sqrt_le_sqrt htle
      rwa [one_div, Real.sqrt_inv, ← one_div, ← hmu] at h1
    calc |(comb v w m₂ n₂).2| ≤ Real.sqrt t * V := h
      _ ≤ (1 / mu) * V := by nlinarith [hV.le, Real.sqrt_nonneg t]
      _ = V / mu := by ring

end Lattice2

end Catalan
