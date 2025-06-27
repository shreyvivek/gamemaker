import GameServer.Commands
import Game.Levels.Propositional.L13_DisjunctiveSyllogism
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





/-- If `P → Q` and `P` both hold, then `Q` must also hold. An extension of Modus Ponens -/
TheoremDoc Propositional.swap_implication as "SwapImplication" in "Propositional"
Statement swap_implication (P Q : Prop) (h : P → Q) (hp : P) : Q := by
  Hint "`h` is a function from `P` to `Q`, and `hp` gives you `P`. Just apply the function!"
  exact h hp



NewTheorem Propositional.disjunctive_syllogism
Conclusion
"
Nice! You just applied a function — that's really all an implication is.

`P → Q` is the same as saying: “If I have `P`, I can give you `Q`.”

You’ll see this pattern come up a lot in proofs.
"
