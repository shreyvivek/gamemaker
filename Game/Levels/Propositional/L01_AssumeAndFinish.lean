

import GameServer.Commands

namespace Propositional

World "Propositional"
Level 1
Title "Assume and Finish"

Introduction "
Welcome!

Let’s begin with the simplest task. If you're told `P` is true, then you can conclude `P`.

Sounds trivial, but this teaches you how to use assumptions to finish a goal.
"

/--

---

Purpose: Use exact when you already have a proof of exactly what the goal is asking for.

It closes the goal immediately if the term matches the goal’s type.

📌 Think of it as:

“Here's exactly what you're asking for — done!”

---

### In Propositional Logic:

If your goal is `P` and you have a proof of `P` (say `h : P`), then `exact h` completes the proof.

To summarize:

You have : `h : P`
Your goal : `P`
`exact h` will complete the proof!

---

### In Sets:

You’re given:

- A set `A : Set ℕ`
- An element `x : ℕ`
- A hypothesis `h : x ∈ A`

And your goal is to prove exactly that: `x ∈ A`.

Since your goal *already matches* your assumption, just use:

`exact h`

This is the most basic kind of step in a proof: confirming something you’ve already assumed.

---

-/
TacticDoc exact

/--

### Logic Constants & Operators

|Name       | Symbol | Commands                          |
|-----------|--------|-----------------------------------|
|Not        | ¬      | `\n`, `\not`, `\neg`, `\lnot`     |
|And        | ∧      | `\and`, `\an`, `\wedge`           |
|Or         | ∨      | `\v`, `\or`, `\vee`               |
|Implies    | →      | `\r`, `\imp`, `\to`               |
|Iff        | ↔      | `\iff`, `\lr`                     |
|For All    | ∀      | `\all`, `\forall`                 |
|Exists     | ∃      | `\ex`, `\exists`                  |
|Belongs    | ∈      | `\in`                             |
|Subset     | ⊆      | `\subset`                         |
|Union      | ∪      | `\union`, `\un`                   |
|Intersect  | ∩      | `\intersect`, `\cap`              |

-/
DefinitionDoc UniCode_Table as "UniCode Table"

Statement (P : Prop) (h : P) : P := by
  Hint "Use the `exact` tactic with `{h}` to directly prove the goal `P`."
  exact h

NewTactic exact

NewDefinition UniCode_Table

Conclusion "
You’ve completed your first proof — and yes, it really was that simple!
"

end Propositional
