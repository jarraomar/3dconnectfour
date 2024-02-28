#lang forge/bsl

abstract sig Color {}
one sig blue, yellow, green, red, black extends Color{}

sig Card {
    color: one Color,
    number: one Int,
    action: one Int  // 0 -> no action, 1 -> skip, 2 -> +2 
}

sig Pile {
  cards: pfunc Int -> Card
}

sig Deck, DiscardPile extends Pile {}

abstract sig Player {
    hand: pfunc Int -> Card
}

sig Player1, Player2, Player3 extends Player{}

sig GameState {
    currentPlayer: one Player,
    deck: one Deck,
    discardPile: one DiscardPile,
    topCard: one Card
}
one sig Game {
    initialState: one GameState,
    next: pfunc GameState -> GameState
}

pred wellFormedHand[p: Player] {
    // Ensure the player's hand has exactly 7 cards
    #{all c: Card, i: Int | p.hand[i] = wellFormedCard[c] } = 7
}

pred wellFormedCard[c: Card] {
    ((c.color = red) or (c.color = blue) or (c.color = green) or (c.color = yellow) or (c.color = black)) and 
    ((c.number >= 0) and (c.number <= 9)) and
    ((c.action = 0) or (c.action = 1) or (c.action = 2))
}

pred wellFormedStartingDeck[d: Deck] {
    // Count the total number of cards in the deck by checking the domain of the partial function
    #{i: Int | some d.cards[i]} = 54 and
    // Numbered cards (0-9) for each color, excluding black
    #{c: Card, i: Int | d.cards[i] = c and c.color != black and c.number >= 0 and c.number <= 9} = 40 and
    // Skip Action cards (color = Black, action = 1)
    #{c: Card, i: Int | d.cards[i] = c and c.color = black and c.action = 1} = 7 and
    // Draw Two Action cards (color = Black, action = 2)
    #{c: Card, i: Int | d.cards[i] = c and c.color = black and c.action = 2} = 7
    
    // Ensure for each color (excluding black), there are 10 unique numbered cards from 0 to 9
    all col: Color | {
        col != black implies {
            all num: Int | {
                num >= 0 and num <= 9 implies {
                     #{c: Card, i: Int | d.cards[i] = c and c.color = col and c.number = num} = 1
                }
            }
        }
    }
}

// pred traces {
//     -- The trace starts with an initial state
//     starting[Game.initialState]
//     no sprev: GameState | Game.next[sprev] = Game.initialState
//     -- Every transition is a valid move
//     all s: GameState | some Game.next[s] implies {
//         -- Define valid moves here
//         -- For example:
//         -- move[s row col p Game.next[s]]
//         -- or
//         -- doNothing[s Game.next[s]]
//     }
// }

// Predicates for valid play of card 
// pred playCard[s: GameState, p: Player, c: Card, s_next: GameState]

// Predicates for valid draw of card
// pred drawCard[s: GameState, p: Player, s_next: GameState]

// pred playerTurn

// pred actionCardEffect (helper function)

// pred scoring (helper function for draw/tie)

// pred winningCondition

