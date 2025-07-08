import GameServer.Commands
import Game.Levels.Propositional.L07_ModusPonens
namespace Propositional

World "Propositional"
Level 8
Title "Or Elimination"

Introduction "
You might remember one such proof from lectures - Dilemma.
Given:
`
-- P ∨ Q
-- P → R
-- Q → R
`
To prove:
`
R is true
`
Proof:
`
We use disjunction elimination on P ∨ Q — i.e., we consider both cases separately:

Case 1: Assume P is true
From (2): P → R, so R is true.

Case 2: Assume Q is true
From (3): Q → R, so again R is true.

In both cases, R is true.
So regardless of whether P or Q is true, we conclude:

R is true.
`

Now, we do this same proof, but in Lean.
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

Statement (P Q R : Prop) (h : P ∨ Q) (h₁ : P → R) (h₂ : Q → R) : R := by
  Hint "Use the `cases` tactic to break the disjunction `{h}` into two possible cases."
  cases h with
  | inl hp =>
    Hint "In this level, you will see how `exact` is used with a **theorem applied to an argument**.

    💡 Consider the `Active Goal`:

    You have:
    - `h₁ : P → R` (an implication)
    - `h_1 : P` (from a case)

    This should strike a bell, as this resembles the structure of Modus Ponens.

    Then `exact modus_ponens P R h₁ h_1` is a direct proof of `R`. It means: use `exact` on the result of modus ponens applied to h₁ and h_1, with propositions P and R.

    Even if u let P and R be underscores respectively, it would still not be an error.

    So you write:

    **exact modus_ponens P R h₁ h_1**
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
