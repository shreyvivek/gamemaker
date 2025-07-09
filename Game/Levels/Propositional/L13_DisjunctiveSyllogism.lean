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

You will combine a lot of lessons from previous levels to clear this one.
You will also make use of another theorem to achieve this. Read about `False.elim` on the Theorems section!
"

/--

---

`False.elim` — From Contradiction, Anything Follows
it is of the type False.elim : False → α

---

**Meaning:**

If you have a contradiction (`False`), you can conclude *any* proposition — even something unrelated.

This is based on a principle in classical logic called “**Explosion**”, which states:

Once you reach False, your system has broken, and anything can be proven.

---

**Intuition:**

Think of False as a logical dead-end or crash.

Once you've proven something impossible, the rules no longer restrict you.

So Lean allows you to conclude any goal using False.elim.

example (P Q : Prop) (h₁ : P) (h₂ : ¬P) : Q :=

  False.elim (h₂ h₁)

---

**Explanation:**

`h₁ : P`

`h₂ : ¬P`, i.e., `P → False`

Applying `h₂ h₁` gives a `contradiction: False`

Then `False.elim` produces a proof of `Q`, finishing the goal

---

**When to use:**

We use `False.elim` when we've reached a contradiction, but our goal is something else — like `Q`.

Suppose you've reached a point in your proof where you have:

`f : False`

That means a contradiction has occurred.

Lean now gives you the power to conclude anything, including your goal `Q`, because from a contradiction, any statement is considered logically valid.

You finish the proof like this:

`exact False.elim f`

It tells Lean: “Since `False` is true here, I can conclude whatever I want — including `Q`.

While it may seem absurd, it follows the principle of *Explosion*, as mentioned earlier”

---

-/
TheoremDoc False.elim as "False.elim" in "Propositional"
Statement (P Q : Prop) (h : P ∨ Q) (not_p : ¬P) : Q := by
  Hint "
You're given a disjunction `P ∨ Q`. To proceed, you must consider both cases separately.

Use the `cases` tactic on `{h}` to split the proof into two branches: one where `P` holds and one where `Q` holds.
"
  cases h with
  | inl hp =>
    Hint "
You're now in the case where `P` is assumed true (`hp : P`), but you also have `not_p : ¬P` — that is, `P → False`.

These two contradict each other!

So you want to derive `False` from this contradiction, and then conclude your goal `Q` using Lean's principle that anything follows from `False`.

Instead of writing a compound term directly inside `exact`, we can also:

1. Use `apply False.elim` to change the goal to `False`
2. Then prove that contradiction directly

This breaks it into more manageable steps and teaches a reusable pattern.
"
    apply False.elim
    Hint "
After using `apply False.elim`, your goal becomes `False`.

You already have:

- `not_p : ¬P`, which is `P → False`
- `hp : P`, which came from the case assumption

Use these together: `not_p hp` gives you `False`.

So simply write:

`exact not_p hp`
"
    exact not_p hp

  | inr hq =>
    Hint "This should be straightforward. You can try it yourself."
    exact hq




NewTheorem False.elim
Conclusion "
Nicely done! You've applied **Disjunctive Syllogism** in this level, showing you how to:
- Split logical cases with `cases`
- Detect contradictions using `¬P`
- Escape contradictions using `False.elim`

You’re now handling propositional logic like a pro.
"

end Propositional
