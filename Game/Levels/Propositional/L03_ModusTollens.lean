import GameServer.Commands

namespace Propositional

World "Propositional"
Level 3
Title "Modus Tollens"

Introduction "From P → Q and ¬Q, we can conclude ¬P. This is known as Modus Tollens."

/--
The `intro` tactic is used when your goal is something like "if P then Q" (`P → Q`) or "for all x, P(x)" (`∀ x, P(x)`).

Think of it like this: when you're trying to prove a statement that starts with “Assume that...”, you can use `intro` to take that assumption into your hands.

For example, if your goal is: `P → Q`
then doing: `intro h`
says: “Let’s assume `P` is true, and call this assumption `h`.” Now your goal is just to prove `Q`, using the fact that you have `h : P`.

In the case of a universal quantifier: `∀ x, P(x)`
then doing: `intro x`
means: “Let `x` be an arbitrary value,” and now the goal becomes `P(x)`.

It’s one of the most basic and useful tactics in Lean, especially at the beginning of a proof. Use it to introduce assumptions or variables from the goal into your working context.
-/
TacticDoc intro


/-- Modus Tollens: from P → Q and ¬Q, we can conclude ¬P. -/
TheoremDoc Propositional.modus_tollens_statement as "ModusTollens" in "Propositional"

Statement modus_tollens_statement (P Q : Prop) (h₁ : P → Q) (h₂ : ¬Q) : ¬P := by
  intro hP
  apply h₂
  exact h₁ hP

NewTactic intro
Conclusion "
You've proven Modus Tollens: from P → Q and ¬Q, you can conclude ¬P.
"

end Propositional
