import GameServer.Commands
import Game.Levels.Propositional.L06_OrIntroductionRight
namespace Propositional

World "Propositional"
Level 7
Title "Or Elimination"

Introduction "
If you know `P ∨ Q`, and you can show `R` follows from each of them individually, then you can conclude `R`.

This is a form of case analysis — we’ll use the `cases` tactic.
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
The `cases` tactic lets you do case analysis on a disjunction.

If you have `h : P ∨ Q`, then `cases h with | inl hp => ... | inr hq => ...` creates two branches:
- One where `P` is assumed true (`hp`)
- One where `Q` is assumed true (`hq`)

You must prove the goal in both branches.
-/
TacticDoc cases

/-- From `P ∨ Q`, and knowing both imply `R`, conclude `R`. -/
TheoremDoc Propositional.or_elim as "OrElim" in "Propositional"

Statement or_elim (P Q R : Prop) (h : P ∨ Q) (h₁ : P → R) (h₂ : Q → R) : R := by
  Hint "Use the `cases` tactic to break the disjunction `{h}` into two possible cases."
  cases h with
  | inl hp =>
    Hint "You are now in the case where `P` holds. Use `{h₁}` to get `R`. Try using `exact` with a combination of assumptions."
    exact h₁ hp
  | inr hq =>
    Hint "Now `Q` holds. Use `{h₂}` to conclude `R`."
    exact h₂ hq

NewTactic cases

NewTheorem Propositional.or_intro_right
Conclusion "
You've learned **disjunction elimination** — case-by-case reasoning using `∨`.
"

end Propositional
