import GameServer.Commands
import Game.Levels.Propositional.L07_ModusPonens
namespace Propositional

World "Propositional"
Level 8
Title "Or Elimination"

Introduction "
Suppose you want to prove a proposition `R`.

You’re told that either `P` or `Q` is true (i.e., `P ∨ Q`).
But you don’t know which one — Lean won’t let you just pick one randomly.

You’re also told that:
- If `P` is true, then `R` follows
- If `Q` is true, then `R` follows
_(we ignore the vacuously true cases, which you would have possibly learnt in lectures.)_
This means: no matter *which* side of the disjunction holds, `R` will be true either way.
To prove `R`, you need to split into two cases using the `cases` tactic — one where `P` is true, and one where `Q` is.

Then, in each case, use the appropriate implication to show that `R` follows.
"

/--
Purpose: Use `cases` on a disjunction (e.g. `P ∨ Q`) to split it into two separate cases.

Each case creates a new assumption:
- `inl hp` means `P` is assumed true
- `inr hq` means `Q` is assumed true

📌 Think of it as:

“Let’s examine both possible scenarios and show that the goal works either way.”

To summarize:

Given: `h : P ∨ Q`
After:
- Case 1: `hp : P`
- Case 2: `hq : Q`
-/
TacticDoc cases


/-- From `P ∨ Q`, we can conclude that either `P` or `Q` has to be definitely true. Knowing that both of them imply `R`, we can conclude `R`.-/
TheoremDoc Propositional.or_elim as "OrElim" in "Propositional"

Statement or_elim (P Q R : Prop) (h : P ∨ Q) (h₁ : P → R) (h₂ : Q → R) : R := by
  Hint "Use the `cases` tactic to break the disjunction `{h}` into two possible cases."
  cases h with
  | inl hp =>
    Hint "In this level, you will see how `exact` is used with a **theorem applied to an argument**.

    💡 Consider the `Active Goal`:

    You have:
    - `h₁ : P → R` (an implication)
    - `h_1 : P` (from a case)

    This should strike a bell, as this resembles the structure of Modus Ponens.

    Then `exact modus_ponens h₁ h_1` is a direct proof of `R`. It means: use `exact` on the result of modus ponens applied to h₁ and h_1.

    So you write:

    **exact modus_ponens h₁ h_1**
    _for writing subscript 1, type h, enter a backslash and then enter 1._
    "
    Hint"
    Here, Lean will check that:

    `h₁ : P → R`
    `h_1 : P`

    Therefore `R` is concluded, which correctly matches what we want, `R`!

    Similarly, when `Q` holds, use `{h₂}` to conclude `R`.
    "
    exact h₁ hp
  | inr hq =>
    exact h₂ hq

NewTactic cases

NewTheorem Propositional.modus_ponens
Conclusion "
You’ve completed a textbook disjunction elimination! You can also see how versatile the `exact` tactic is.

By showing the goal holds in **both** branches of the `or`, you’ve logically proven it no matter what.
"

end Propositional
