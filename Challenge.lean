import RequestProject.Unconditional

/-!
# Comparator challenge

Challenge module for [leanprover/comparator](https://github.com/leanprover/comparator).
The theorem below is the current WIP comparator statement, with the proof left
open as a `sorry`. It is a regression test for a known specification gap: it
does not yet constrain the witnesses to the intended Nesterenko construction.

The accompanying `Solution.lean` discharges it by appealing to the formalized proof.
See `comparator.config.json` for the comparator configuration.
-/

open Catalan

/-- Current WIP statement; see the module-level specification warning. -/
theorem catalan_worthiness_one_sub_eps {ε : ℝ} (hε : 0 < ε) :
    ∃ q p : ℕ → ℤ, IsAdmissible catalanReal q p ∧
      ((1 - ε : ℝ) : EReal) < worthiness catalanReal q p :=
  sorry
