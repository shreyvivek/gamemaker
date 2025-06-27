import GameServer.Commands
import Game.Levels.Propositional.L11_ModusTollens
namespace Propositional

World "Propositional"
Level 12
Title "Contrapositive"

Introduction "
You may remember that every implication `P → Q`
is **logically equivalent** to its contrapositive: `¬Q → ¬P`.

This means:
> If `P → Q`, then `¬Q → ¬P` is also true.

You’ve already seen this idea in Level 11 (Modus Tollens):
- If `P → Q` and `Q` is false, then `P` must be false.

In this level, you’re going to prove the general version:
Given only `P → Q`, show that `¬Q → ¬P`.

Let’s unpack this step by step.
"




/-- From `P → Q`, derive `¬Q → ¬P`. -/
TheoremDoc Propositional.contrapositive_equiv as "Contrapositive" in "Propositional"

Statement contrapositive_equiv (P Q : Prop) (h : P → Q) : ¬Q → ¬P := by
  Hint "To prove `¬Q → ¬P`, first recognize that it's shorthand for `(Q → False) → (P → False)`."
  Hint "That means this is a **nested implication**, so we’ll need to assume both `¬Q` and `P` before we can prove `False`."
  intro not_q
  Hint "`not_q` now holds: you’re assuming `Q → False`. Now to prove `¬P`, we must show `P → False` — so assume `P` next via `intro assumed_p`."
  intro assumed_p
  Hint "Your goal is now `False`. Think: how do you reach a contradiction from `P`?"
  Hint "You have `h : P → Q`, and you also assumed `P` as `assumed_p`. So, from those two, you can get `Q`."
  Hint "But your goal is `False`, and you have `not_q : Q → False`. This gives you a strategy: apply `not_q` to change the goal to a proof of `Q`."
  apply not_q
  Hint "You now need to prove `Q`, and you have `h : P → Q` and `assumed_p : P`. This is a perfect setup for `apply` again."
  apply h
  Hint "Now the goal is `P`, and you already have `assumed_p : P`. Use `exact assumed_p` to finish."
  exact assumed_p


NewTheorem Propositional.modus_tollens
Conclusion "
Awesome! You've just proven the **contrapositive** form of an implication — an essential logical equivalence.

Though this level was heavy on hints, it brought together everything you’ve learned:
- You used `intro` to build nested assumptions
- You used `apply` to break apart implications
- And you combined all the pieces to reach a contradiction

This is real formal logic — and you're solving it in Lean. 🔥
"

end Propositional
