
import GameServer.Commands

import Game.Levels.Propositional.Propositional
import Game.Levels.Propositional.L01_AssumeAndFinish
import Game.Levels.Propositional.L02_IntroduceAssumption
import Game.Levels.Propositional.L03_AndIntroduction
import Game.Levels.Propositional.L04_AndEliminationLeft
import Game.Levels.Propositional.L05_OrIntroductionLeft
import Game.Levels.Propositional.L06_OrIntroductionRight


-- Here's what we'll put on the title screen
Title "Discrete Mathematics with Lean4"
Introduction
"
Welcome to **Discrete Math with Lean4**, a fun and interactive game that will help you in proving several theorems **MH1812 - Discrete Mathematics**

There are several levels that you can try out in each world. Each level essentially covers a theorem taught in the lecture. And you have many such levels queued up in a world.
Start by clicking on **Propositional** on the right.
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

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
