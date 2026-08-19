import RequestProject.Contiguity
import RequestProject.RivoalQ

/-!
# Rivoal's identification of the Zudilin numerators

Equation (4.9) of the note states

`P_m = Q_m σ_m + (-1)^m p_m(x_m) / 8`,

where `p_n` is Beukers' Padé numerator, `x_m = 1/2 - m` is the moving half-integer point,
`σ_m = ∑_{k<m} (-1)^k/(2k+1)²` and `P_m`, `Q_m` are Zudilin's two sequences.  In the note this is
quoted from Rivoal's Theorem 2; here it is *proved*.

The argument is the numerator analogue of `RivoalQ.lean`, but instead of creative telescoping it
uses the contiguity relations of `Contiguity.lean`.  Write

`Z(m,n) = q_n(x_m) σ_m + (-1)^m p_n(x_m)/8`.

* `Zf_contig`: the two contiguity relations combine into the single clean relation
  `x_{m+1}² Z(m+1,n+1) = c_{n+1}(x_m) Z(m,n+1) - 2(n+1)² Z(m,n)`;
  the `σ`-increment `σ_{m+1} - σ_m = (-1)^m/(2m+1)²` is exactly what is needed to cancel the
  inhomogeneous term `2 q_{n+1}(x_{m+1})` coming from the functional equation.
* `Zf_rec`: `Z(m,·)` satisfies Beukers' recurrence in the second index (it is a fixed linear
  combination of `q` and `p`).
* `Zf_zud_rec`: eliminating the off-diagonal values `Z(m,m+1)`, `Z(m,m+2)` from these relations
  leaves exactly Zudilin's three-term recurrence for the diagonal `m ↦ Z(m,m)`.

Since `Z(0,0) = 0 = P_0` and `Z(1,1) = 7/4 - 1/8 = 13/8 = P_1`, uniqueness of solutions of
Zudilin's recurrence gives `Z(m,m) = P_m`, which is (4.9).
-/

namespace Catalan

/-- The diagonal combination `Z(m,n) = q_n(x_m) σ_m + (-1)^m p_n(x_m)/8`. -/
noncomputable def Zf (m n : ℕ) : ℚ :=
  bq (xpt m) n * sigmaCat m + (-1 : ℚ) ^ m / 8 * bp (xpt m) n

lemma xpt_sub_one (m : ℕ) : xpt m - 1 = xpt (m + 1) := by
  have h := xpt_succ_add_one m
  linarith

/-- The contiguity relation for the combination `Z`.  The inhomogeneous term of `bp_contig`
is cancelled by the increment of `σ`. -/
lemma Zf_contig (m n : ℕ) :
    (xpt (m + 1)) ^ 2 * Zf (m + 1) (n + 1)
      = cCon (n + 1) (xpt m) * Zf m (n + 1) - 2 * ((n : ℚ) + 1) ^ 2 * Zf m n := by
  have hx : xpt m - 1 = xpt (m + 1) := xpt_sub_one m
  have hq := bq_contig (xpt m) n
  have hp := bp_contig (xpt m) n
  rw [hx] at hq hp
  have hx2 : (xpt (m + 1)) ^ 2 = (2 * (m : ℚ) + 1) ^ 2 / 4 := by
    unfold xpt
    push_cast
    ring
  have hdel : (2 * (m : ℚ) + 1) ^ 2 * ((-1 : ℚ) ^ m / (2 * (m : ℚ) + 1) ^ 2) = (-1 : ℚ) ^ m := by
    have hne : ((2 * (m : ℚ) + 1) ^ 2) ≠ 0 := by positivity
    field_simp
  have hsign : (-1 : ℚ) ^ (m + 1) = -((-1 : ℚ) ^ m) := by
    rw [pow_succ]; ring
  simp only [Zf, sigmaCat_succ, hsign]
  rw [hx2] at hq hp ⊢
  linear_combination (sigmaCat m) * hq + ((-1 : ℚ) ^ m / 8) * hp
    + (bq (xpt (m + 1)) (n + 1) / 4) * hdel

/-- `Z(m,·)` satisfies Beukers' recurrence in the second index. -/
lemma Zf_rec (m n : ℕ) :
    bL (n + 1) * Zf m (n + 2) = bC (xpt m) (n + 1) * Zf m (n + 1) + bR (n + 1) * Zf m n := by
  simp only [Zf]
  linear_combination (sigmaCat m) * bq_rec (xpt m) n + ((-1 : ℚ) ^ m / 8) * bp_rec (xpt m) n

/-- The diagonal `m ↦ Z(m,m)` satisfies Zudilin's three-term recurrence.  This is the elimination
of the off-diagonal values `Z(m,m+1)`, `Z(m,m+2)`, `Z(m+1,m+2)` from `Zf_contig` and `Zf_rec`. -/
lemma Zf_zud_rec (m : ℕ) :
    lzQ ((m : ℚ) + 1) * Zf (m + 2) (m + 2)
      = czQ ((m : ℚ) + 1) * Zf (m + 1) (m + 1) + rzQ ((m : ℚ) + 1) * Zf m m := by
  have e1 := Zf_contig m m
  have e2 := Zf_contig m (m + 1)
  have e3 := Zf_rec m m
  have e4 := Zf_contig (m + 1) (m + 1)
  simp only [cCon, xpt, bL, bC, bR, lzQ, czQ, rzQ] at e1 e2 e3 e4 ⊢
  push_cast at e1 e2 e3 e4 ⊢
  have hne : ((2 * (m : ℚ) + 1) ^ 2) ≠ 0 := by positivity
  refine mul_left_cancel₀ hne ?_
  linear_combination
    (-4 * (20 * (m : ℚ) ^ 2 + 72 * m + 65) *
      (208 * (m : ℚ) ^ 4 + 896 * (m : ℚ) ^ 3 + 1448 * (m : ℚ) ^ 2 + 1024 * m + 267)) * e1
    + (16 * ((m : ℚ) + 2) ^ 2 * (20 * (m : ℚ) ^ 2 + 32 * m + 13) *
        (20 * (m : ℚ) ^ 2 + 72 * m + 65)) * e2
    + (4 * (20 * (m : ℚ) ^ 2 + 32 * m + 13) * (20 * (m : ℚ) ^ 2 + 56 * m + 41) *
        (20 * (m : ℚ) ^ 2 + 72 * m + 65)) * e3
    + (16 * ((m : ℚ) + 2) ^ 2 * (20 * (m : ℚ) ^ 2 + 32 * m + 13) * (2 * (m : ℚ) + 1) ^ 2) * e4

@[simp] lemma Zf_zero : Zf 0 0 = 0 := by
  simp [Zf]

@[simp] lemma Zf_one : Zf 1 1 = 13 / 8 := by
  simp only [Zf, sigmaCat, xpt]
  norm_num

/-- The diagonal of `Z` is Zudilin's numerator sequence. -/
theorem Zf_diag_eq_Pz (m : ℕ) : Zf m m = Pz m := by
  refine rec2_unique _ _ _ _ _ (fun k => Zf k k) Zf_zero Zf_one
    (fun k => by exact_mod_cast (Int.cast_ne_zero (α := ℚ)).mpr (LZ_ne_zero (k + 1))) ?_ m
  intro k
  have h := Zf_zud_rec k
  show ((LZ (k + 1) : ℤ) : ℚ) * Zf (k + 2) (k + 2)
      = ((CZ (k + 1) : ℤ) : ℚ) * Zf (k + 1) (k + 1) + ((RZ (k + 1) : ℤ) : ℚ) * Zf k k
  rw [lzQ_cast (k + 1), czQ_cast (k + 1), rzQ_cast (k + 1)]
  push_cast at h ⊢
  linarith [h]

/-- **Rivoal's identification** (equation (4.9) of the note): the Zudilin numerator is
`P_m = Q_m σ_m + (-1)^m p_m(x_m)/8`, where `p_m` is Beukers' Padé numerator and `x_m = 1/2 - m`.

In the note this is quoted from Rivoal's Theorem 2; here it is proved from the contiguity
relations of `Contiguity.lean` together with Rivoal's denominator identity `q_m(x_m) = Q_m`. -/
theorem rivoal_numerator (m : ℕ) :
    Pz m = Qz m * sigmaCat m + (-1 : ℚ) ^ m / 8 * bp (xpt m) m := by
  rw [← Zf_diag_eq_Pz m, Zf, bq_xpt_eq_Qz]

end Catalan
