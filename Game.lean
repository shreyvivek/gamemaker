
import GameServer.Commands

import Game.Levels.Propositional.Propositional
import Game.Levels.Propositional.L01_ModusPonens
import Game.Levels.Propositional.L02_AndComm
import Game.Levels.Propositional.L03_ModusTollens

-- Here's what we'll put on the title screen
Title "Discrete Math with Lean4"
Introduction
"
Welcome to **Discrete Math with Lean4**, a fun and interactive game that will help you in proving several theorems **MH1812 - Discrete Mathematics**

There are several levels that you can try out. Each level essentially covers the content taught in each topic. For instance,
Level 2 would cover content taught in Topic 2.
"

Info "
Here you can put additional information about the game. It is accessible
from the starting through the drop-down menu.

For example: Game version, Credits, Link to Github and Zulip, etc.

Use markdown.
"

/-! Information to be displayed on the servers landing page. -/
Languages "English"
CaptionShort "Game Template"
CaptionLong "You should use this game as a template for your own game and add your own levels, if you are keen to learn more about Lean4."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
MakeGame
