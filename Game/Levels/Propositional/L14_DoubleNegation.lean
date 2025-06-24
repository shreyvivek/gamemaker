import GameServer.Commands

namespace Propositional


World "Propositional"
Level 14
Title "Implication Application"

Introduction
"
This level introduces the idea that an implication `P → Q` is just like a function:
if you know `P`, and you have a way to go from `P` to `Q`, then you can apply it.

In Lean, this means using `exact h hp`, where `h : P → Q` and `hp : P`.

Simple and satisfying!
"
/-- If `P → Q` and `P` both hold, then `Q` must also hold. An extension of Modus Ponens -/
TheoremDoc Propositional.swap_implication as "SwapImplication" in "Propositional"
Statement swap_implication (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  Hint "`h` is a function from `P` to `Q`, and `hp` gives you `P`. Just apply the function!"
  exact h hp


NewTheorem Propositional.swap_implication

Conclusion
"
Nice! You just applied a function — that's really all an implication is.

`P → Q` is the same as saying: “If I have `P`, I can give you `Q`.”

You’ll see this pattern come up a lot in proofs.
"
