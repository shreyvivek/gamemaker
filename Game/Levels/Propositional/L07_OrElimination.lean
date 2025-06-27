import GameServer.Commands
import Game.Levels.Propositional.L06_OrIntroductionRight
namespace Propositional

World "Propositional"
Level 7
Title "Or Elimination"

Introduction "
Suppose you want to prove a proposition `R`.

You’re told that either `P` or `Q` is true (i.e., `P ∨ Q`).
But you don’t know which one — Lean won’t let you just pick one randomly.

You’re also told that:
- If `P` is true, then `R` follows
- If `Q` is true, then `R` follows

This means: no matter *which* side of the disjunction holds, `R` will be true either way.
To prove `R`, you need to split into two cases using the `cases` tactic — one where `P` is true, and one where `Q` is.

Then, in each case, use the appropriate implication to show that `R` follows.
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


/--
Purpose: Use constructor when your goal is a conjunction (`P ∧ Q`).

It splits the goal into two subgoals: one for `P`, and one for `Q`.

📌 Think of it as:

“To prove both `P` and `Q`, let’s do them one at a time.”

To summarize:
`constructor` on `P ∧ Q` gives you two sub goals — one for `P` and one for `Q`.
-/
TacticDoc constructor



/--
Purpose: Use `left` when your goal is a disjunction (`P ∨ Q`) and you want to prove the **left** part.

If your goal is `P ∨ Q`, then `left` changes the goal to proving `P`.

📌 Think of it as:

“I’ll prove the first part of the `or`, and that’s good enough.”

To summarize:

Your goal : `P ∨ Q`
After `left`, your new goal is just `P`
-/
TacticDoc left



/--
Purpose: Use `cases` on a disjunction (e.g. `P ∨ Q`) to split it into two separate cases.

Each case creates a new assumption:
- `inl assumed_p` means `P` is assumed true
- `inr assumed_q` means `Q` is assumed true

📌 Think of it as:

“Let’s examine both possible scenarios and show that the goal works either way.”

To summarize:

Given: `h : P ∨ Q`
After:
- Case 1: `assumed_p : P`
- Case 2: `assumed_q : Q`
-/
TacticDoc cases

/-- From `P ∨ Q`, we can conclude that either `P` or `Q` has to be definitely true. Knowing that both of them imply `R`, we can conclude `R`.-/
TheoremDoc Propositional.or_elim as "OrElim" in "Propositional"

Statement or_elim (P Q R : Prop) (h : P ∨ Q) (h₁ : P → R) (h₂ : Q → R) : R := by
  Hint "Use the `cases` tactic to break the disjunction `{h}` into two possible cases."
  cases h with
  | inl hp =>
    Hint "In this level, you will see how `exact` is used with a **function applied to an argument**.

    💡 Example:

    If you have:
    - `h₁ : P → R` (an implication)
    - `assumed_p : P` (from a case)

    Then `h₁ assumed_p` is a proof of `R`.

    So you write:

    **exact h₁ assumed_p**
    "
    Hint"
    Here, Lean will check that:

    `h₁ : P → R`
    `assumed_p : P`

    Therefore `h₁ assumed_p : R` is concluded, which correctly matches what we want, `R`!
    "
    exact h₁ hp
  | inr hq =>
    Hint "Now `Q` holds. Use `{h₂}` to conclude `R`."
    exact h₂ hq

NewTactic cases

NewTheorem Propositional.or_intro_right
Conclusion "
You’ve completed a textbook disjunction elimination!

By showing the goal holds in **both** branches of the `or`, you’ve logically proven it no matter what.

If you observed this level closely, you might see some similarity to Modus Ponens. A level ahead will prove Modus Ponens in another method, with yet another tactic.
"

end Propositional
