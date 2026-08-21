import RequestProject.Unconditional

/-!
# Comparator solution

Solution module for [leanprover/comparator](https://github.com/leanprover/comparator):
this discharges the current WIP challenge stated in `Challenge.lean`. The
underlying theorem is a regression test exposing the known specification gap.
-/

open Catalan

/-- Current WIP comparator form: see `Challenge.lean`. -/
theorem catalan_worthiness_one_sub_eps {ε : ℝ} (hε : 0 < ε) :
    ∃ q p : ℕ → ℤ, IsAdmissible catalanReal q p ∧
      ((1 - ε : ℝ) : EReal) < worthiness catalanReal q p :=
  Catalan.catalan_worthiness_one_sub_eps_unconditional hε
