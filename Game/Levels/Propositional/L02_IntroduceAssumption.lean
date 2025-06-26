import GameServer.Commands
import Game.Levels.Propositional.L01_AssumeAndFinish
namespace Propositional

World "Propositional"
Level 2
Title "Introduce Assumption"

Introduction "
Let’s prove an implication: `P → P`. That is, if `P` holds, then `P` holds (trivially).

This level introduces the `intro` tactic.
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
Opens up an implication goal by introducing its assumption.

If your goal is `P → Q`, `intro h` changes the goal to `Q` and gives you `h : P` as a local assumption.

Think of it like: “Let’s suppose `P` is true.”
-/
TacticDoc intro

/-- From the assumption `P`, conclude `P`. -/
TheoremDoc Propositional.intro_self as "IntroSelf" in "Propositional"

Statement intro_self (P : Prop) : P → P := by
  Hint "Use the `intro` tactic to assume `P` is true. Try `intro h`."
  intro h
  Hint "Now you have `{h} : P`, and your goal is `P`. Use `exact` to finish."
  exact h

NewTactic intro
NewTheorem Propositional.assume_and_finish


Conclusion "
That was a basic implication! The `intro` tactic is your go-to tool for these.
"

end Propositional
