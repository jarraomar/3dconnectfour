#lang forge
abstract sig Player {} 
one sig X, O, K extends Player {} 

sig Board {
    //Board state
    board: pfunc Int -> Int -> Int -> Player,
    //Player turn
    turn: one Player,
    //Previous board state
    prev: lone Board
}

one sig Game {
    first: one Board, 
    next: pfunc Board -> Board
}

pred wellformed[b: Board] {
    all x, y, z: Int | {
        (x < 0 or x > 2 or y < 0 or y > 2 or z < 0 or z > 2) implies {
             no b.board[x][y][z]
        }
    }
}

pred initial[b: Board] {
    all x, y, z: Int | no b.board[x][y][z]  
    b.prev = none
    b.turn = X
}



pred winning[b: Board, p: Player] {
    -- Horizontal wins
    (some x, z: Int | {
        (b.board[x][0][z] = p and b.board[x][1][z] = p and b.board[x][2][z] = p)
    })
    or
    -- Vertical wins
    (some y, z: Int | {
        (b.board[0][y][z] = p and b.board[1][y][z] = p and b.board[2][y][z] = p)
    })
    or
    -- Z axis Wins
    (some x, y: Int | {
        (b.board[x][y][0] = p and b.board[x][y][1] = p and b.board[x][y][2] = p)
    })
    or
    -- Diagonal wins across XZ Plane (rows and depth for each column)
    (some y: Int | {
        (b.board[0][y][0] = p and b.board[1][y][1] = p and b.board[2][y][2] = p)
    })
    or
    -- Diagonal wins across YZ Plane (columns and depth for each row)
    (some x: Int | {
        (b.board[x][0][0] = p and b.board[x][1][1] = p and b.board[x][2][2] = p)
    })
    or
    -- 3D Diagonals
    (
        (b.board[0][0][0] = p and b.board[1][1][1] = p and b.board[2][2][2] = p) or
        (b.board[2][0][0] = p and b.board[1][1][1] = p and b.board[0][2][2] = p) or
        (b.board[0][2][0] = p and b.board[1][1][1] = p and b.board[2][0][2] = p) or
        (b.board[2][2][0] = p and b.board[1][1][1] = p and b.board[0][0][2] = p)
    )
}

pred move[pre: Board, x, y, z: Int, post: Board] {
    //Guard
    no pre.board[x][y][z]
    pre.turn = X implies post.turn = O
    pre.turn = O implies post.turn = K
    pre.turn = K implies post.turn = X
    all p: Player | not winning[pre, p]

    x >= 0 and x <= 2 
    y >= 0 and y <= 2
    z >= 0 and z <= 2

    post.board[x][y][z] = pre.turn 

    // Ensure that all other cells remain unchanged between the pre-move and post-move board states, 
    // except for the cell that was targeted by the move.
    all x2, y2, z2: Int | (x != x2 or y != y2 or z != z2) implies {
        post.board[x2][y2][z2] = pre.board[x2][y2][z2]
    }
}

pred doNothing[pre, post: Board] {
  //  some p: Player | winning[pre, p]
    
    all x, y, z: Int | {
        pre.board[x, y, z] = post.board[x, y, z]
    }
    post.prev = pre
}



pred game_trace {
    initial[Game.first]  // Ensure the first board is correctly initialized
    // all b: Board | b != Game.first implies {
    //     wellformed[b]
    //     some b2: Board | wellformed[b2] and Game.next[b] = b2 implies {
    //         some x, y, z: Int, p: Player | 
    //             move[b, x, y, z, b2]  // Validate moves
    //         or
    //             doNothing[b, b2]
    //     }  
    // }
} // Ensure all boards are well-formed
        



run { game_trace } for 3 Board for {next is linear}


/*
    Testing the Move Property
*/

pred moveValidity { some pre: Board, post: Board, x: Int, y: Int, z: Int, turn: Player | move[pre, x, y, z, post] }
// test suite for moveValidity {
//     example invalidMoveOccupiedSpace is {not moveValidity} for {
//     Board = `Board1 + `Board2
//     X = `X0
//     O = `O0
//     K = `K0
//     Player = X + O + K
//     `Board1.board = (2,1,0) -> X
//     `Board2.board = (2,1,0) -> O
//     }

//     example validMoveOccupiedSpace is { moveValidity} for {
//         Board = `Board1 + `Board2
//         X = `X0
//         O = `O0
//         K = `K0
//         Player = X + O + K
//         `Board1.board = (2,1,0) -> X
//         `Board2.board = (2,1,1) -> O + (2,1,0) -> X
//     }

//     example turnSequencingInvalid is { not moveValidity } for {
//         Board = `Board1 + `Board2
//         X = `X0
//         O = `O0
//         K = `K0
//         Player = X + O + K
//         `Board1.turn = X
//         `Board2.turn = X  // Invalid, should be O's turn
//         `Board1.board = (2,2,0) -> X
//         `Board2.board = (2,2,1) -> X
//     }

//     example invalidCoordinatesMove is { not moveValidity } for {
//         Board = `Board1 + `Board2
//         X = `X0
//         O = `O0
//         K = `K0
//         Player = X + O + K
//         `Board1.board = (3,3,3) -> X  // Invalid coordinates
//         `Board2.board = (3,3,3) -> O
//     }
// }




/*
Testing Board Wellformedness
*/
// pred allBoardsWellformed { all b: Board | wellformed[b] }
// example row_wellformed is {allBoardsWellformed} for {
//     Board = `Board0
//     X = `X0
//     O = `O0
//     K = `K0
//     Player = X + O + K
//     `Board0.board = (0,0,0) -> X + 
//                     (0,1,0) -> O + 
//                     (0,2,0) -> K
// }

// example offBoardZ_not_wellformed is {not allBoardsWellformed} for {
//     Board = `Board0
//     X = `X0
//     O = `O0
//     Player = X + O
//     `Board0.board = (0,0,-1) -> X + 
//                     (0,1,0) -> X + 
//                     (1,2,0) -> X +
//                     (2,2,0) -> X
// }

/* Testing Win Conditions*/

// pred isWinner { all b: Board | winning[b,X]}
// example thereIsWinner is {isWinner} for {
//     Board = `Board0
//     X = `X0
//     O = `O0
//     K = `K0
//     Player = X + O + K
//     `Board0.board = (0,0,0) -> X + 
//                     (0,1,0) -> X + 
//                     (0,2,0) -> X +
//                     (1,1,1) -> O + 
//                     (2,2,2) -> K
// }


// example thereIsNoWinner is {not isWinner} for {
//     Board = `Board0
//     X = `X0
//     O = `O0
//     Player = X + O
//         `Board0.board = (0,0,0) -> X + 
//                         (0,1,0) -> X + 
//                         (0,2,0) -> X +
//                         (0,0,0) -> X
// }

// pred allBoardsWinning { all b: Board | winning[b, X] or winning[b, O] }
// example horizontalWinExample is {allBoardsWinning} for {
//     Board = `Board0
//     X = `X0
//     O = `O0
//     Player = X + O
//     `Board0.board = (0,0,0) -> X + 
//                     (1,0,0) -> X + 
//                     (2,0,0) -> X +
//                     (3,0,0) -> X
// }
// example zAxisWinExample is {allBoardsWinning} for {
//     Board = `Board0
//     X = `X0
//     O = `O0
//     Player = X + O
//     `Board0.board = (0,0,0) -> X + 
//                     (0,0,1) -> X + 
//                     (0,0,2) -> X +
//                     (0,0,3) -> X
// }


