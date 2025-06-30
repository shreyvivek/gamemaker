

import GameServer.Commands

namespace Propositional

World "Propositional"
Level 1
Title "Assume and Finish"

Introduction "
Welcome!

Let’s begin with the simplest task. If you're told `P` is true, then you can conclude `P`.

Sounds trivial, but this teaches you how to use assumptions to finish a goal.
"

/--
Purpose: Use exact when you already have a proof of exactly what the goal is asking for.

It closes the goal immediately if the term matches the goal’s type.

📌 Think of it as:

“Here's exactly what you're asking for — done!”

If your goal is `P` and you have a proof of `P` (say `h : P`), then `exact h` completes the proof.

To summarize:

You have : `h : P`
Your goal : `P`
`exact h` will complete the proof!
-/
TacticDoc exact

/--
have tactic yay!
-/
TacticDoc «have»

/--
let tactic yay!
-/
TacticDoc «let»

/--
assume tactic yay!
-/
TacticDoc assume

/--
show tactic yay!
-/
TacticDoc «show»


/-- If you know `P`, then you can conclude `P`. -/
TheoremDoc Propositional.assume_and_finish as "AssumeAndFinish" in "Propositional"

Statement assume_and_finish (P : Prop) (h : P) : P := by
  Hint "Use the `exact` tactic with `{h}` to directly prove the goal `P`."
  exact h

NewTactic exact «have» assume «let» «show»


Conclusion "
You’ve completed your first proof — and yes, it really was that simple!
"

end Propositional
