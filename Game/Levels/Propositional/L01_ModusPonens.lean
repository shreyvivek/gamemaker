import GameServer.Commands

namespace Propositional

World "Propositional"
Level 1
Title "Modus Ponens"

Introduction "From P → Q and P, we can conclude Q. This is known as Modus Ponens."


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

/-- Modus Ponens: from P → Q and P, we can conclude Q. -/
TheoremDoc Propositional.modus_ponens_statement as "ModusPonens" in "Propositional"
Statement modus_ponens_statement (P Q : Prop) (h₁ : P → Q) (h₂ : P) : Q := by
  apply h₁
  exact h₂

NewTactic apply exact
Conclusion "
You've proven Modus Ponens: from P → Q and P, you can conclude Q.
"

end Propositional
