import RequestProject.Final

/-!
# Comparator challenge

Challenge module for [leanprover/comparator](https://github.com/leanprover/comparator).
The theorem below is the challenge: it is the statement of the main result of this
project (Theorem 10.1, `Catalan.catalan_worthiness_gt_857914` in
`RequestProject/Final.lean`) with the proof left open as a `sorry`.

The accompanying `Solution.lean` discharges it by appealing to the formalized proof.
See `comparator.config.json` for the comparator configuration.
-/

open Catalan

/-- Theorem 10.1 (numerical form): there is an admissible approximation sequence to `α`
of worthiness at least `0.857914`, given the balanced-minima data of the base note at
the rates `H = 6 + (45/2) log φ` and `F = 6 - (15/2) log φ`. -/
theorem catalan_worthiness_gt_857914 {α : ℝ} (d : BalancedMinimaData α Hrate Frate) :
    ∃ q p : ℕ → ℤ, IsAdmissible α q p ∧ ((0.857914 : ℝ) : EReal) ≤ worthiness α q p :=
  sorry
