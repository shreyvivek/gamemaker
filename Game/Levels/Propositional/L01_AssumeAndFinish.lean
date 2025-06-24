

import GameServer.Commands

namespace Propositional

World "Propositional"
Level 1
Title "Assume and Finish"

Introduction "
Let’s begin with the simplest task. If you're told `P` is true, then you can conclude `P`.

This teaches you how to use assumptions to finish a goal.
"

/--
Closes the current goal using the exact term you provide.

If your goal is `P` and you have a proof of `P` (say `h : P`), then `exact h` completes the proof.

It’s like saying: “Here’s exactly what you asked for.”
-/
TacticDoc exact

/-- If you know `P`, then you can conclude `P`. -/
TheoremDoc Propositional.assume_and_finish as "AssumeAndFinish" in "Propositional"

Statement assume_and_finish (P : Prop) (h : P) : P := by
  Hint "Use the `exact` tactic with `{h}` to directly prove the goal `P`."
  exact h

NewTactic exact
NewTheorem Propositional.assume_and_finish

Conclusion "
You’ve completed your first proof — and yes, it really was that simple!
"

end Propositional
