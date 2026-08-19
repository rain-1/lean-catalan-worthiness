import Mathlib

/-!
# The double-congruence lattice

Sections 19–20 of the base note.  Given two integer rows `(a₁, Y₁)`, `(a₂, Y₂)` and two moduli
`T` and `S T`, the divided quantities

`q(c) = (c₁ a₁ + c₂ a₂) / T`,  `p(c) = (c₁ Y₁ + c₂ Y₂) / (S T)`

are integers exactly when the coefficient vector `c` lies in the lattice

`K = {c ∈ ℤ² : T ∣ a₁c₁ + a₂c₂  and  S T ∣ Y₁c₁ + Y₂c₂}`.

The key arithmetic input is that `T` divides the reduced cross determinant `a₁Y₂ - a₂Y₁`; it
forces the index of `K` in `ℤ²` to be at most `S T` rather than the trivial `S T²`.

We never need the index itself: `exists_congr_basis2` exhibits *explicitly* two vectors of `K`
spanning a sublattice of determinant `δ ≤ S T`, and `exists_thinned_basis` then thins that
sublattice so that its determinant lands in `[S T, 2 S T]`.
-/

namespace Catalan

namespace CongrLattice

/-- Bézout for three integers: `gcd (gcd a b) c` is an integer combination of `a`, `b`, `c`. -/
lemma exists_bezout3 (a b c : ℤ) :
    ∃ x y z : ℤ, ((Int.gcd (Int.gcd a b : ℤ) c : ℕ) : ℤ) = a * x + b * y + c * z := by
  have h1 := Int.gcd_eq_gcd_ab ((Int.gcd a b : ℕ) : ℤ) c
  have h2 := Int.gcd_eq_gcd_ab a b
  refine ⟨Int.gcdA a b * Int.gcdA ((Int.gcd a b : ℕ) : ℤ) c,
    Int.gcdB a b * Int.gcdA ((Int.gcd a b : ℕ) : ℤ) c,
    Int.gcdB ((Int.gcd a b : ℕ) : ℤ) c, ?_⟩
  rw [h1, h2]
  ring

/-- **Basis of a one-congruence lattice.**  For a linear form `(P, Q)` and a modulus `N > 0`,
there are two explicit vectors `e, f` solving `N ∣ P c₁ + Q c₂` whose determinant is `δ = N / g`,
where `g = gcd(P, Q, N)`.  (The lattice they span is in fact the whole solution lattice, but we
only need the stated facts.) -/
lemma exists_congr_basis (P Q N : ℤ) (hN : 0 < N) :
    ∃ (e f : ℤ × ℤ) (g δ : ℤ), 0 < g ∧ 0 < δ ∧ g * δ = N ∧
      (∃ x y z : ℤ, g = P * x + Q * y + N * z) ∧
      e.1 * f.2 - e.2 * f.1 = δ ∧
      N ∣ P * e.1 + Q * e.2 ∧ N ∣ P * f.1 + Q * f.2 := by
  obtain ⟨d, hd⟩ : ∃ d : ℤ, d = ((Int.gcd P Q : ℕ) : ℤ) := ⟨_, rfl⟩
  have hd0 : 0 ≤ d := by rw [hd]; positivity
  rcases eq_or_lt_of_le hd0 with hdz | hdpos
  · -- `P = Q = 0`
    have hz : (Int.gcd P Q : ℕ) = 0 := by
      have : ((Int.gcd P Q : ℕ) : ℤ) = 0 := by rw [← hd, ← hdz]
      exact_mod_cast this
    exact ⟨(1, 0), (0, 1), N, 1, hN, one_pos, by ring, ⟨0, 0, 1, by ring⟩, by norm_num,
      by simp [(Int.gcd_eq_zero_iff.mp hz).1, (Int.gcd_eq_zero_iff.mp hz).2],
      by simp [(Int.gcd_eq_zero_iff.mp hz).1, (Int.gcd_eq_zero_iff.mp hz).2]⟩
  · -- `d = gcd(P,Q) > 0`
    obtain ⟨A1, hA1⟩ : d ∣ P := by rw [hd]; exact Int.gcd_dvd_left P Q
    obtain ⟨A2, hA2⟩ : d ∣ Q := by rw [hd]; exact Int.gcd_dvd_right P Q
    have hcop : Int.gcd A1 A2 = 1 := by
      have hgm : Int.gcd (d * A1) (d * A2) = d.natAbs * Int.gcd A1 A2 := Int.gcd_mul_left d A1 A2
      rw [← hA1, ← hA2] at hgm
      have hnat : d.natAbs = (Int.gcd P Q : ℕ) := by
        rw [hd]; simp
      rw [hnat] at hgm
      have hpos : 0 < (Int.gcd P Q : ℕ) := by
        have : (0 : ℤ) < ((Int.gcd P Q : ℕ) : ℤ) := by rw [← hd]; exact hdpos
        exact_mod_cast this
      nlinarith [hgm, hpos]
    obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, A1 * u + A2 * v = 1 := by
      have hb := Int.gcd_eq_gcd_ab A1 A2
      rw [hcop] at hb
      push_cast at hb
      exact ⟨Int.gcdA A1 A2, Int.gcdB A1 A2, by linarith [hb]⟩
    obtain ⟨g, hg⟩ : ∃ g : ℤ, g = ((Int.gcd d N : ℕ) : ℤ) := ⟨_, rfl⟩
    have hgpos : 0 < g := by
      have hne : (Int.gcd d N : ℕ) ≠ 0 := by
        intro h
        rw [Int.gcd_eq_zero_iff] at h
        exact absurd h.2 (by omega)
      have : 0 < (Int.gcd d N : ℕ) := Nat.pos_of_ne_zero hne
      rw [hg]
      exact_mod_cast this
    obtain ⟨δ, hδ⟩ : g ∣ N := by rw [hg]; exact Int.gcd_dvd_right d N
    obtain ⟨d', hd'⟩ : g ∣ d := by rw [hg]; exact Int.gcd_dvd_left d N
    have hδpos : 0 < δ := by
      rcases lt_trichotomy δ 0 with h | h | h
      · nlinarith [hδ, hN, hgpos]
      · rw [h] at hδ; simp at hδ; omega
      · exact h
    refine ⟨(δ * u, δ * v), (-A2, A1), g, δ, hgpos, hδpos, hδ.symm, ?_, ?_, ?_, ?_⟩
    · obtain ⟨x, y, z, hxyz⟩ := exists_bezout3 P Q N
      exact ⟨x, y, z, by rw [hg, hd]; exact hxyz⟩
    · simp only
      linear_combination δ * huv
    · simp only
      have hval : P * (δ * u) + Q * (δ * v) = d' * N := by
        rw [hδ, hA1, hA2, hd']
        linear_combination (g * d' * δ) * huv
      rw [hval]
      exact Dvd.intro_left d' rfl
    · simp only
      have hval : P * -A2 + Q * A1 = 0 := by rw [hA1, hA2]; ring
      rw [hval]
      exact dvd_zero N

/-- **Basis of the double-congruence lattice.**  Under `T ∣ a₁Y₂ - a₂Y₁`, the lattice `K`
contains an explicit sublattice of determinant `δ ≤ S T`. -/
theorem exists_congr_basis2 (a1 a2 Y1 Y2 S T : ℤ) (hS : 0 < S) (hT : 0 < T)
    (hdvd : T ∣ a1 * Y2 - a2 * Y1) :
    ∃ (w1 w2 : ℤ × ℤ) (δ : ℤ), 0 < δ ∧ δ ≤ S * T ∧
      w1.1 * w2.2 - w1.2 * w2.1 = δ ∧
      T ∣ a1 * w1.1 + a2 * w1.2 ∧ T ∣ a1 * w2.1 + a2 * w2.2 ∧
      S * T ∣ Y1 * w1.1 + Y2 * w1.2 ∧ S * T ∣ Y1 * w2.1 + Y2 * w2.2 := by
  obtain ⟨e, f, g, δ₁, hg, hδ₁, hgδ, ⟨bx, by', bz, hbez⟩, hdet1, hde, hdf⟩ :=
    exists_congr_basis a1 a2 T hT
  -- On the first congruence lattice, `δ₁ = T / g` already divides the second linear form.
  have hL : ∀ c : ℤ × ℤ, T ∣ a1 * c.1 + a2 * c.2 → δ₁ ∣ Y1 * c.1 + Y2 * c.2 := by
    intro c hc
    set A : ℤ := a1 * c.1 + a2 * c.2 with hA
    set L : ℤ := Y1 * c.1 + Y2 * c.2 with hLdef
    have h1 : T ∣ a1 * L := by
      have : a1 * L = Y1 * A + c.2 * (a1 * Y2 - a2 * Y1) := by rw [hA, hLdef]; ring
      rw [this]
      exact dvd_add (Dvd.dvd.mul_left hc Y1) (Dvd.dvd.mul_left hdvd c.2)
    have h2 : T ∣ a2 * L := by
      have : a2 * L = Y2 * A - c.1 * (a1 * Y2 - a2 * Y1) := by rw [hA, hLdef]; ring
      rw [this]
      exact dvd_sub (Dvd.dvd.mul_left hc Y2) (Dvd.dvd.mul_left hdvd c.1)
    have h3 : T ∣ g * L := by
      have : g * L = bx * (a1 * L) + by' * (a2 * L) + (bz * L) * T := by rw [hbez]; ring
      rw [this]
      exact dvd_add (dvd_add (Dvd.dvd.mul_left h1 bx) (Dvd.dvd.mul_left h2 by'))
        (Dvd.intro_left _ rfl)
    have h4 : g * δ₁ ∣ g * L := by rw [hgδ]; exact h3
    exact (mul_dvd_mul_iff_left (by omega : g ≠ 0)).mp h4
  obtain ⟨Pe, hPe⟩ := hL e hde
  obtain ⟨Qf, hQf⟩ := hL f hdf
  have hSg : 0 < S * g := by positivity
  obtain ⟨e', f', g', δ₂, hg', hδ₂, hgδ', -, hdet2, hde', hdf'⟩ :=
    exists_congr_basis Pe Qf (S * g) hSg
  refine ⟨(e'.1 * e.1 + e'.2 * f.1, e'.1 * e.2 + e'.2 * f.2),
    (f'.1 * e.1 + f'.2 * f.1, f'.1 * e.2 + f'.2 * f.2), δ₂ * δ₁,
    by positivity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hδ₂le : δ₂ ≤ S * g := by nlinarith [hgδ', hg', hδ₂]
    calc δ₂ * δ₁ ≤ (S * g) * δ₁ := by nlinarith [hδ₁]
      _ = S * (g * δ₁) := by ring
      _ = S * T := by rw [hgδ]
  · simp only
    have : (e'.1 * e.1 + e'.2 * f.1) * (f'.1 * e.2 + f'.2 * f.2)
        - (e'.1 * e.2 + e'.2 * f.2) * (f'.1 * e.1 + f'.2 * f.1)
        = (e'.1 * f'.2 - e'.2 * f'.1) * (e.1 * f.2 - e.2 * f.1) := by ring
    rw [this, hdet1, hdet2]
  · simp only
    have : a1 * (e'.1 * e.1 + e'.2 * f.1) + a2 * (e'.1 * e.2 + e'.2 * f.2)
        = e'.1 * (a1 * e.1 + a2 * e.2) + e'.2 * (a1 * f.1 + a2 * f.2) := by ring
    rw [this]
    exact dvd_add (Dvd.dvd.mul_left hde _) (Dvd.dvd.mul_left hdf _)
  · simp only
    have : a1 * (f'.1 * e.1 + f'.2 * f.1) + a2 * (f'.1 * e.2 + f'.2 * f.2)
        = f'.1 * (a1 * e.1 + a2 * e.2) + f'.2 * (a1 * f.1 + a2 * f.2) := by ring
    rw [this]
    exact dvd_add (Dvd.dvd.mul_left hde _) (Dvd.dvd.mul_left hdf _)
  · simp only
    have hrw : Y1 * (e'.1 * e.1 + e'.2 * f.1) + Y2 * (e'.1 * e.2 + e'.2 * f.2)
        = δ₁ * (Pe * e'.1 + Qf * e'.2) := by
      have h1 : Y1 * e.1 + Y2 * e.2 = δ₁ * Pe := hPe
      have h2 : Y1 * f.1 + Y2 * f.2 = δ₁ * Qf := hQf
      linear_combination e'.1 * h1 + e'.2 * h2
    rw [hrw]
    obtain ⟨c, hc⟩ := hde'
    refine ⟨c, ?_⟩
    rw [hc]
    calc δ₁ * (S * g * c) = S * (g * δ₁) * c := by ring
      _ = S * T * c := by rw [hgδ]
  · simp only
    have hrw : Y1 * (f'.1 * e.1 + f'.2 * f.1) + Y2 * (f'.1 * e.2 + f'.2 * f.2)
        = δ₁ * (Pe * f'.1 + Qf * f'.2) := by
      have h1 : Y1 * e.1 + Y2 * e.2 = δ₁ * Pe := hPe
      have h2 : Y1 * f.1 + Y2 * f.2 = δ₁ * Qf := hQf
      linear_combination f'.1 * h1 + f'.2 * h2
    rw [hrw]
    obtain ⟨c, hc⟩ := hdf'
    refine ⟨c, ?_⟩
    rw [hc]
    calc δ₁ * (S * g * c) = S * (g * δ₁) * c := by ring
      _ = S * T * c := by rw [hgδ]

/-- **The thinned double-congruence lattice.**  Replacing the first basis vector by a multiple,
the determinant of the sublattice of `K` can be pushed into the window `[S T, 2 S T]`, which is
the covolume normalization of Section 21. -/
theorem exists_thinned_basis (a1 a2 Y1 Y2 S T : ℤ) (hS : 0 < S) (hT : 0 < T)
    (hdvd : T ∣ a1 * Y2 - a2 * Y1) :
    ∃ (w1 w2 : ℤ × ℤ) (δ : ℤ), S * T ≤ δ ∧ δ ≤ 2 * (S * T) ∧
      w1.1 * w2.2 - w1.2 * w2.1 = δ ∧
      T ∣ a1 * w1.1 + a2 * w1.2 ∧ T ∣ a1 * w2.1 + a2 * w2.2 ∧
      S * T ∣ Y1 * w1.1 + Y2 * w1.2 ∧ S * T ∣ Y1 * w2.1 + Y2 * w2.2 := by
  obtain ⟨w1, w2, δ, hδpos, hδle, hdet, h1, h2, h3, h4⟩ :=
    exists_congr_basis2 a1 a2 Y1 Y2 S T hS hT hdvd
  set M : ℤ := S * T with hM
  set k : ℤ := M / δ + 1 with hk
  have hq : δ * (M / δ) + M % δ = M := Int.mul_ediv_add_emod M δ
  have hr0 : 0 ≤ M % δ := Int.emod_nonneg M (by omega)
  have hr1 : M % δ < δ := Int.emod_lt_of_pos M hδpos
  have hkδ : k * δ = δ * (M / δ) + δ := by rw [hk]; ring
  refine ⟨(k * w1.1, k * w1.2), w2, k * δ, by omega, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · simp only
    have : k * w1.1 * w2.2 - k * w1.2 * w2.1 = k * (w1.1 * w2.2 - w1.2 * w2.1) := by ring
    rw [this, hdet]
  · simp only
    have : a1 * (k * w1.1) + a2 * (k * w1.2) = k * (a1 * w1.1 + a2 * w1.2) := by ring
    rw [this]
    exact Dvd.dvd.mul_left h1 k
  · exact h2
  · simp only
    have : Y1 * (k * w1.1) + Y2 * (k * w1.2) = k * (Y1 * w1.1 + Y2 * w1.2) := by ring
    rw [this]
    exact Dvd.dvd.mul_left h3 k
  · exact h4

end CongrLattice

end Catalan
