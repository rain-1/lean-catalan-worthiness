import RequestProject.Final

/-!
# Comparator solution

Solution module for [leanprover/comparator](https://github.com/leanprover/comparator):
this discharges the challenge stated in `Challenge.lean` using the formalized proof
`Catalan.catalan_worthiness_gt_857914` from `RequestProject/Final.lean`.
-/

open Catalan

/-- Theorem 10.1 (numerical form): see `Challenge.lean`. -/
theorem catalan_worthiness_gt_857914 {α : ℝ} (d : BalancedMinimaData α Hrate Frate) :
    ∃ q p : ℕ → ℤ, IsAdmissible α q p ∧ ((0.857914 : ℝ) : EReal) ≤ worthiness α q p :=
  Catalan.catalan_worthiness_gt_857914 d
