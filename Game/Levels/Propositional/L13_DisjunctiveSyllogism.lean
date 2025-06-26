import GameServer.Commands
import Game.Levels.Propositional.L12_Contrapositive
namespace Propositional

World "Propositional"
Level 13
Title "Disjunctive Syllogism"

Introduction "
Suppose:

- `P ∨ Q` is true (at least one must hold), and
- `P` is false (i.e., `¬P` is true)

Then we can conclude that `Q` must be true.

This form of inference is called **Disjunctive Syllogism**.
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
The `cases` tactic lets you do case analysis on a disjunction (`P ∨ Q`).

It splits the proof into two branches:
- one where `P` holds
- one where `Q` holds

If one branch leads to a contradiction, use `False.elim` to derive your goal.
-/
TacticDoc cases

/--
If you ever reach a contradiction (`False`), you can use the `False.elim` tactic to prove **any** goal.

This is based on the logical principle that "from falsehood, anything follows" (ex falso quodlibet).
-/
TacticDoc False.elim

/-- From `P ∨ Q` and `¬P`, conclude `Q`. -/
TheoremDoc Propositional.disjunctive_syllogism as "DisjunctiveSyllogism" in "Propositional"

Statement disjunctive_syllogism (P Q : Prop) (h : P ∨ Q) (hnp : ¬P) : Q := by
  Hint "Use `cases` on `{h}` to handle both possibilities: `P` or `Q`."
  cases h with
  | inl h₁ =>
    Hint "You now have `P`, but `{hnp}` says `¬P`. Apply `hnp` to get a contradiction."
    apply False.elim
    Hint "`hnp` is a function from `P → False`, and you have `P` as `h₁`. Use `exact h₁` to supply the input."
    apply hnp
    exact h₁
  | inr h₂ =>
    Hint "`Q` holds directly here. Use `exact` to finish the proof."
    exact h₂

NewTactic False.elim

NewTheorem Propositional.contrapositive_equiv
Conclusion "
Nicely done! You've applied **Disjunctive Syllogism** — eliminating one side of a disjunction using negation.
"

end Propositional
