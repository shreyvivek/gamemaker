import GameServer.Commands

namespace Propositional

World "Propositional"
Level 1
Title "Modus Ponens"

Introduction "
From $P \rightarrow Q$ and $P$, we can conclude $Q$.
This rule of inference is known as **Modus Ponens**.
"

/--
Solves the current goal by using a function or theorem.

If your goal is `Q` and you have `P → Q`, then `apply` turns the goal into proving `P`.
It's like saying: “To prove `Q`, it's enough to prove `P`.”
-/
TacticDoc apply

/--
Closes the current goal using the term you provide — the term must exactly match the goal.

For example, if your goal is `P` and you have a proof of `P` (say, `h : P`), then `exact h` solves the goal.
-/
TacticDoc exact

/-- Modus Ponens: from `P → Q` and `P`, we can conclude `Q`. -/
TheoremDoc Propositional.modus_ponens_statement as "ModusPonens" in "Propositional"

Statement modus_ponens_statement (P Q : Prop) (h₁ : P → Q) (h₂ : P) : Q := by
  Hint "Use the `apply` tactic with the implication `{h₁}` to turn your goal `Q` into `P`."
  apply h₁
  Hint "Now you have a goal `P`, and you already have `{h₂} : P` — use `exact` to finish."
  exact h₂

NewTactic apply exact
NewTheorem Propositional.modus_ponens_statement

Conclusion "
You've successfully proven **Modus Ponens**: from $P \rightarrow Q$ and $P$, you can conclude $Q$.
"

end Propositional
