# 3D Connect Four README

## Project Objective
The goal of this project is to model a 3D Connect Four game using Forge, expanding traditional Connect Four into three dimensions. This version adds depth as a third axis to the classic 2D grid, introducing new strategies and a more expansive and complex conditions.

## Model Design and Visualization
Our model includes core game play aspects in a 3D environment, focusing on:
- **Signatures**: `Player`, `Board`—representing players and the 3D game board.
- **Predicates**: Including `wellformed`, `initial`, `xturn`, `oturn`, `winning`, and `move`—defining game state checks and actions.

The visualization unfortunately couldn't be made but we'd be more than welcome to continue with that challenge as a final project, incorporating that into our game. Overall showing the game in 3d dimension turned out to be a lot more complicated then we intially anticipated 

## Signatures and Predicates
- **Player**: Two instances `X` and `O`, representing the game players.
- **Board**: Models the game board as a mapping from 3D coordinates to players.
- **wellformed** to **game_trace**: Defines game initialization, turn management, winning condition checks, and game progression.

### Winning Predicate:

The `winning` predicate is central to determining the game's outcome, adapted to a 3D context from traditional Connect Four. It evaluates the following:

- **Horizontal and Vertical (XY Plane)**: Checks each "slice" of the grid for lines of four in a row, adapting 2D win conditions to each layer of the 3D grid.
- **Depth (Z-Axis)**: Introduces win conditions along the board's depth, unique to the 3D variant, requiring alignment across different layers.
- **Diagonal (XY, XZ, YZ Planes)**: Expands diagonal wins to include lines that span across the board's depth and width, or height and depth, utilizing the full 3D space.
- **3D Diagonals**: The most complex, looking for lines of four that run diagonally through the cube in any direction, fully leveraging the three-dimensional gameplay.

**Calculating Winning Conditions**: In the 3D space, the potential for winning alignments increases. The predicate systematically checks all possible winning lines—horizontal, vertical, diagonal across planes.

## Testing Overview

### Tests for Model Integrity
- **allBoardsWellformed**: Confirms board pices are within the 3D grid's boundaries
- **rowX_wellformed**: Validates a board setup with 'X' pieces forming a horizontal line
- **offBoardZ_not_wellformed**: Identifies incorrect board setups 

### Tests for Domain Properties
- **horizontalWinExample** and **zAxisWinExample**: These tests validate the model's capability to recognize horizontal wins within layers and vertical wins through the depth of the board, essential for capturing the essence of 3D gameplay.
- **invalidMoveOccupiedSpace**: Ensures the game logic correctly invalidates moves to occupied spaces, testing a fundamental rule of Connect Four and maintaining game integrity.

