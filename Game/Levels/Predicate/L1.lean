import GameServer.Commands

namespace Predicate

World "Predicate"
Level 1
Title "What’s a Predicate?"

Introduction "
Welcome to **Predicate Logic**!

In propositional logic, you worked with full statements which were assigned truth values - `True` or `False`.
In predicate logic, we work with **statements that depend on a variable**.

These are called **predicates**.

For instance:
> Let `P(x)` mean “x is a student”.

This is not a full proposition until we plug in a value like `P(Alice)`, where Alice, is a student.

Let’s see how to use one!

*Note: `P x` and `P (x)` mean the same. Lean removes the parantheses by default. It's like a function `f` applied onto a variable `x` (the function here is a proposition).*
"

Statement {α : Type} (P Q : α → Prop) (a : α) (h : ∀ x, P (x) → Q (x)) (hP : P (a)) : Q (a) := by
Hint "You want to prove `Q a`, and you have a rule: `∀ x, P x → Q x`, which reads: For all `x`, `P x → Q x`.

`apply` that rule at the specific value `a`, just like how we did in Propositional Logic."
apply h (a)
Hint "Now Lean wants you to prove `P a`, which you already have from `hP`."
exact hP

Conclusion "
Nice work! 🎉

You just used a predicate rule to prove a specific case.

This is the core idea of predicate logic:
General statements like `∀ x, P (x) → Q (x)` can be instantiated at a specific value.

And Lean handles it just like functions!
"

end Predicate
