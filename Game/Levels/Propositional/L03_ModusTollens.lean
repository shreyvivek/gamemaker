import GameServer.Commands
import Game.Levels.Propositional.L01_ModusPonens

namespace Propositional

World "Propositional"
Level 3
Title "Modus Tollens"

Introduction "
From `P → Q` and `¬Q`, we can conclude `¬P`.
This classic form of reasoning is called **Modus Tollens**.
"

/--
The `intro` tactic is used when your goal is something like an implication (`P → Q`) or a universal quantifier (`∀ x, P(x)`).

- Use `intro h` to assume `P` when trying to prove `P → Q`.
- Use `intro x` to assume an arbitrary value when trying to prove `∀ x, P(x)`.

It’s like saying “Assume this is true...” and using it in the proof.
-/
TacticDoc intro

/--
Modus Tollens: From `P → Q` and `¬Q`, we can conclude `¬P`.
-/
TheoremDoc Propositional.modus_tollens_statement as "ModusTollens" in "Propositional"

Statement modus_tollens_statement (P Q : Prop) (h₁ : P → Q) (h₂ : ¬Q) : ¬P := by
  Hint "You want to prove `¬P`. That means: assume `P` and show a contradiction. Try `intro`."
  intro hP
  Hint "Now apply the implication `h₁ : P → Q` to your assumption `hP`."
  apply h₂
  Hint "Use `exact` to supply `Q`, which you got from applying the implication."
  exact h₁ hP

NewTactic intro
NewTheorem Propositional.modus_tollens_statement

Conclusion "
You've proven **Modus Tollens**:
Given `P → Q` and `¬Q`, it must follow that `¬P`.
"

end Propositional
