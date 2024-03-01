#lang forge

//12 total cards
//6 of each color for none action cards
//2 cards in each hand, 10 on Deck

abstract sig Color {}
one sig Green, Red extends Color {}

sig Card {
    color: one Color,
    number: one Int
}

abstract sig Pile {
  cards: set Card
}

one sig Deck, DiscardPile extends Pile {}

abstract sig Player {
    hand: set Card
}

one sig Player1, Player2, Player3 extends Player{}

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



pred inHandBounds[i1, i2: Int]{
    (i1 = 0) and (i2 = 1)
}
// pred inCardBounds[i1: Int]{
//     (i1 >= 0) and (i2 <= 5)
// }
pred wellFormedHand[p: Player, d: Deck] {
    #p.hand = 2
    

    all c: Card | c in p.hand implies {
    all col: Color, num: Int | (col in (Green + Red) and num >= 3 and num <= 5) implies {
        // There should be exactly one card for each color and number combination
        one c: Card | (c.color = col) and (c.number = num)
    }
    }
    // Ensures the player's hand cards are not in the deck anymore
    d.cards & p.hand = none
}

pred allHandsAreUnique[p1, p2, p3: Player] {
    // Ensures that the cards in each player's hand are unique and not shared
    no (p1.hand & p2.hand)
    no (p1.hand & p3.hand)
    no (p2.hand & p3.hand)
}


pred wellFormedStartingDeck[d: Deck] { 
    no DiscardPile.cards
    #d.cards = 6 

    // Each color has exactly one card for each number from 0 to 5
    all col: Color, num: Int | (col in (Green + Red) and num >= 0 and num <= 2) implies {
        // There should be exactly one card for each color and number combination
        one c: Card | (c.color = col) and (c.number = num) and (c in d.cards)
    }
}

pred playCard[s: GameState, p: Player, c: Card, s_next: GameState] {
  // The card c is in player p's hand
  some i: Int | p.hand[i] = c and
  // The card c matches the top card of the discard pile by color or number
  (c.color = s.topCard.color or c.number = s.topCard.number) and
  // The next state has c as the new top card of the discard pile
  s_next.topCard = c and
  // The card c is removed from player p's hand in the next state
  no s_next.(p.hand)[i] and
  // Update the currentPlayer to the next player
  s_next.currentPlayer = nextPlayer[s.currentPlayer]
  // ... include additional constraints and updates
}
pred nextState[s: GameState, s_next: GameState] {
    -- Determines the next state based on the current state
    nextPlayer[s.currentPlayer, s_next.currentPlayer]
    -- Include conditions to modify the deck, hands, and discard pile
    -- ...
}
pred nextPlayer[current: one Player, next: one Player] {
    -- Assuming a fixed turn order: Player1 -> Player2 -> Player3 -> Player1
    (current = Player1 and next = Player2) or
    (current = Player2 and next = Player3) or
    (current = Player3 and next = Player1)
}
// pred initialGame[s: GameState]{
//     wellFormedStartingDeck
//     wellFormedHand1
//     wellFormedHand
//     some p: Player {
//         s.currentPlayer = p
//         some c: Card, i: Int |   
//            p.hand[i]
//     // }

// }

    // pre nextMove[s:GameState] {
        
    // }
pred init[g: Game] {
    wellFormedStartingDeck[g.initialState.deck]
    wellFormedHand[Player1, g.initialState.deck]
    wellFormedHand[Player2, g.initialState.deck]
    wellFormedHand[Player3, g.initialState.deck]
    allHandsAreUnique[Player1,Player2,Player3]
    // Ensure that the combined hands of all players do not have overlapping cards
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

run {
    init[Game]
    
} 
for  exactly 1 Deck, exactly 1 Game, exactly 3 Player, 12 Card, exactly 5 Int, exactly 1 GameState
// Predicates for valid play of card 
// pred playCard[s: GameState, p: Player, c: Card, s_next: GameState]