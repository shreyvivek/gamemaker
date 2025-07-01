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
Purpose: Use intro to assume something — usually when proving an implication.

If your goal is `P → Q`, `intro h` changes the goal to `Q` and gives you `h : P` as a local assumption.

📌 Think of it as:

“Let me assume `P` is true for now, and see if I can prove `Q`.”
Opens up an implication goal by introducing its assumption.

To summarize:

Your goal : `h : P → P`
After `intro h`,
you get an assumption `h : P` and your goal will just be `P`.
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


Conclusion "
That was a basic implication! The `intro` tactic is your go-to tool for these.
"

end Propositional
