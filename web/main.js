import './style.css'

// Import the game client from lean4game
import { runGame } from '@leanprover/lean4-game'

// Run the game and attach it to a div with id="app"
runGame(document.getElementById("app"))