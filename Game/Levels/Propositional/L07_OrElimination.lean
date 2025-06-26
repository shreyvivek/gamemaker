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
