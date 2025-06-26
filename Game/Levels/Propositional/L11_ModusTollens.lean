import GameServer.Commands
import Game.Levels.Propositional.L10_NegationIntroduction
namespace Propositional

World "Propositional"
Level 11
Title "Modus Tollens"

Introduction "
Suppose:

- If `P` is true, then `Q` is true. (`P → Q`)
- But actually, `Q` is false. (`¬Q`)

Then `P` must also be false. This is known as **Modus Tollens**.
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
Use `intro` to assume `P` and then apply the implication `P → Q`.

Finish by applying the negation `¬Q` to get a contradiction and conclude `¬P`.
-/
TacticDoc intro

/-- Modus Tollens: from `P → Q` and `¬Q`, conclude `¬P`. -/
TheoremDoc Propositional.modus_tollens as "ModusTollens" in "Propositional"

Statement modus_tollens (P Q : Prop) (h₁ : P → Q) (h₂ : ¬Q) : ¬P := by
  Hint "Use `intro` to assume `P` is true."
  intro hp
  Hint "Now finish the level off using `{h₁}` and `{h₂}` to derive a contradiction."
  apply h₂
  apply h₁
  exact hp


NewTheorem Propositional.negation_intro
Conclusion "
Well done! You've applied **Modus Tollens** to conclude that `P` must be false since `Q` is false.
"

end Propositional
