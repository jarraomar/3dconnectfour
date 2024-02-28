# Game Components Overview

## Card Definition

**Attributes:**
- `color`: String (red, green, yellow, blue, and black for special cards)
- `number`: Integer (0-9 for numbered cards, -1 indicates action cards)
- `action`: String (none, skip, +2 for special action cards)

## Player

**Attributes:**
- `hand`: Collection of Card objects (the player's current hand).
- `name`: String (optional, for identification).

## Player Hand

A dynamically managed list/array of Card objects within the Player structure.

## Deck

A collection of all Card objects, initially containing all 54 unique cards, shuffled.

## Discard Pile

A collection of Card objects that have been played, determining the playable color, number, or action.

## Game State

Manages the game, including players, deck, discard pile, and turn order.

# Card Definition and Actions

Cards encapsulate color, value, and actions, identifying card types and applying effects during gameplay.

# Game Flow

Involves turn management, card play, action card effects, and win condition checks.

## Initial Setup

- Shuffle the deck.
- Deal 7 cards to each player.
- Turn over the top card to start the discard pile.
- Determine the first player.

## Turn Logic

- Check for playable cards.
- Play a card or draw from the deck if none are playable.
- Apply special action effects.
- Check win conditions after each turn.

## Winning and Scoring

- Emptying one's hand wins the game.
- If the deck runs out, scores are calculated based on hand values; the highest score wins.
- A tie is declared if scores are equal.
