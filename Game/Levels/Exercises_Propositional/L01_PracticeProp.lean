import GameServer.Commands
import Game.Levels.Propositional.L07_ModusPonens
import Game.Levels.Propositional.L11_ModusTollens
namespace Exercises_Propositional

World "Exercises_Propositional"

Level 1
Title "From And to Implication"

Introduction "
You’re given a conjunction and an implication.

Your task: extract the right part and trigger the implication.
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

/--
Purpose: Use `right` when your goal is a disjunction (`P ∨ Q`) and you want to prove the **right** part.

If your goal is `P ∨ Q`, then `right` changes the goal to proving `Q`.

📌 Think of it as:

“I’ll prove the second part of the `or`, and that’s good enough.”

To summarize:

Your goal : `P ∨ Q`
After `right`, your new goal is just `Q`
-/
TacticDoc right

/--
Purpose: Use `apply` to reduce your current goal to an earlier implication.

If your goal is `Q`, and you have `implication : P → Q`,
then `apply implication` changes the goal to `P`.

📌 Think of it as:

“To prove `Q`, it’s enough to prove `P` — because I already have `P → Q`.”
-/
TacticDoc apply

/--
Purpose: Use `cases` on a disjunction (e.g. `P ∨ Q`) to split it into two separate cases.

Each case creates a new assumption:
- `inl hp` means `P` is assumed true
- `inr hq` means `Q` is assumed true

📌 Think of it as:

“Let’s examine both possible scenarios and show that the goal works either way.”

To summarize:

Given: `h : P ∨ Q`
After:
- Case 1: `hp : P`
- Case 2: `hq : Q`
-/
TacticDoc cases


/--

`False.elim` — From Contradiction, Anything Follows
it is of the type False.elim : False → α

**Meaning:**

If you have a contradiction (`False`), you can conclude *any* proposition — even something unrelated.

This is based on a principle in classical logic called “**Explosion**”, which states:

Once you reach False, your system has broken, and anything can be proven.

**Intuition:**

Think of False as a logical dead-end or crash.

Once you've proven something impossible, the rules no longer restrict you.

So Lean allows you to conclude any goal using False.elim.

example (P Q : Prop) (h₁ : P) (h₂ : ¬P) : Q :=

  False.elim (h₂ h₁)

**Explanation:**

`h₁ : P`

`h₂ : ¬P`, i.e., `P → False`

Applying `h₂ h₁` gives a `contradiction: False`

Then `False.elim` produces a proof of `Q`, finishing the goal

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



-/
TheoremDoc False.elim as "False.elim" in "Exercises_Propositional"

/--
Purpose: Use `have` to create and name an intermediate result in your proof.

It lets you:
- Break up long reasoning chains
- Improve clarity and structure
- Reuse partial results later

### Example:

If you have `h₁ : P → Q` and `hp : P`, and you want to reach `R`, you can write:

`have hq : Q := modus_ponens _ _ h₁ hp`

Now you have `hq : Q`, which you can use in the next line with `h₂ : Q → R`:

`exact modus_ponens _ _ h₂ hq`

This is useful when proofs grow longer or when you want to give names to intermediate steps to reason about them clearly.
-/
TacticDoc «have»

Statement (P Q R : Prop)
  (h₁ : P ∧ Q)
  (h₂ : P → R) : R := by
  apply h₂
  exact h₁.left

NewTactic apply exact intro constructor left right cases «have»
NewTheorem False.elim

Conclusion "
You extracted `P` from the conjunction and applied the implication to reach `R`. Nicely done!
"

end Exercises_Propositional
