import GameServer.Commands
import Game.Levels.Propositional.L12_Contrapositive
namespace Propositional

World "Propositional"
Level 13
Title "Disjunctive Syllogism"

Introduction "
In this level, you’ll prove a very common logical inference called **Disjunctive Syllogism**.

It works like this:

> If `P ∨ Q` is true, and `P` is false, then `Q` must be true.

This makes sense — `P ∨ Q` tells us that at least one of them is true.
If we know that `P` is *not* true (`¬P`), then `Q` is the only possibility left.

This combines what you did in earlier levels:
- In Level 7, you used `cases` to break apart a disjunction
- In Level 10, you learned that `¬P` means `P → False`
- In Level 11, you used contradiction (`False`) to complete a proof

Now you’ll combine all of those tools into one elegant move.
You also make use of another theorem to achieve this. Read about `False.elim` on the right!
"

/--
Use `False.elim` when you have a contradiction (`False`) but need to prove something else.

If you’ve proven `False`, then `False.elim` lets you derive anything — even `Q`.

You’ll use this in the branch where `P` is true, and `¬P` leads to a contradiction.
-/
TheoremDoc False.elim as "FalseElim" in "Propositional"

/-- From `P ∨ Q` and `¬P`, conclude `Q`. -/
TheoremDoc Propositional.disjunctive_syllogism as "DisjunctiveSyllogism" in "Propositional"

Statement disjunctive_syllogism (P Q : Prop) (h : P ∨ Q) (not_p : ¬P) : Q := by
 Hint "Use `cases h` to consider the two possible cases: `P` or `Q`."
 cases h with
  | inl hp =>
    Hint "You are now in the case where `P` is true. But you also have `not_p : P → False`, so this leads to a contradiction."
    Hint "A compound exact statement enclosed in `()` should help to get a contradiction (`False`)."
    Hint "Then use `False.elim` to derive your goal `Q` from that contradiction using `exact False.elim (whatever you think the compound statement is)."
    exact False.elim (not_p hp)
  | inr hq =>
    Hint "`Q` holds directly here. Use `exact` to finish the proof."
    exact hq


NewTheorem Propositional.contrapositive_equiv False.elim
Conclusion "
Nicely done! You've applied **Disjunctive Syllogism** in this level, showing you how to:
- Split logical cases with `cases`
- Detect contradictions using `¬P`
- Escape contradictions using `False.elim`

You’re now handling classical logic like a pro.
"

end Propositional
