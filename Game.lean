
import GameServer.Commands

import Game.Levels.Propositional.Propositional
import Game.Levels.Exercises_Propositional.Exercises_Propositional
import Game.Levels.Sets.Sets
import Game.Levels.Predicate.Predicate

-- Here's what we'll put on the title screen
Title "Discrete Mathematics with Lean4"
Introduction
"
Welcome to **Discrete Math with Lean4**, an interactive game that will help you in proving several theorems of **Discrete Mathematics**

**What is Lean?**

Lean is a powerful tool used to write and verify mathematical proofs using code. It’s like a super-charged calculator for logic — you tell Lean the rules and what you want to prove, and it checks every single step for correctness. Unlike doing math on paper (which can be vague), Lean makes sure there are no gaps or mistakes. It’s used by mathematicians, computer scientists, and even students to write formal, checkable proofs.

Lean 4 is the latest version of the Lean theorem prover. It introduces a faster engine, better syntax, and allows users to build interactive proof environments — like this game! Lean 4 also supports general-purpose programming, making it both a proof assistant and a full programming language. You can define logic, prove theorems, and even build applications — all in one system.

**What is this game all about?**

This is a proof-based puzzle game built with Lean 4. Each level is a logic challenge. You solve it by using _tactics_ — special instructions that Lean understands (just like any other programming language understanding its own syntax) — to complete proofs step by step.

Click on the World `Propositional`, to get started!
"

Info "
This is the first iteration of this game. You can find the source code at [GitHub Repository – gamemaker](https://github.com/shreyvivek/gamemaker).

"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "MH1812"
CaptionLong "You can use this game as a template for your own game and add your own levels, if you are keen to learn more about Lean4."
-- Prerequisites "" -- add this if your game depends on other games
CoverImage "images/MH1812 Logo.png"

Dependency Propositional → Predicate
Dependency Predicate → Sets
Dependency Propositional → Exercises_Propositional

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
