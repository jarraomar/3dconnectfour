#lang forge

abstract sig Player {} 
one sig X, O, K extends Player {} 

sig Board {
    board: pfunc Int -> Int -> Int -> Player,  // 3D board
    prev: lone Board // just add this 
}

pred wellformed[b: Board] {
    all x, y, z: Int | {
        (x < 0 or x > 2 or y < 0 or y > 2 or z < 0 or z > 2) implies {
             no b.board[x][y][z]
        }
    }

    b.prev != none implies wellformed[b.prev]
}

pred initial[b: Board] {
    all x, y, z: Int | no b.board[x][y][z]  
    no b.prev  
}


pred xturn[b: Board] {
    #{x, y, z: Int | b.board[x][y][z] = X}
    =
    #{x, y, z: Int | b.board[x][y][z] = K}
    and
    #{x, y, z: Int | b.board[x][y][z] = X}
    =
    add[#{x, y, z: Int | b.board[x][y][z] = O}, 1]
}


pred oturn[b: Board] {
    #{x, y, z: Int | b.board[x][y][z] = O}
    =
    #{x, y, z: Int | b.board[x][y][z] = X}
    and
    #{x, y, z: Int | b.board[x][y][z] = O}
    =
    add[#{x, y, z: Int | b.board[x][y][z] = K}, 1]
}

pred kturn[b: Board] {
    #{x, y, z: Int | b.board[x][y][z] = K}
    =
    #{x, y, z: Int | b.board[x][y][z] = O}
    and
    #{x, y, z: Int | b.board[x][y][z] = K}
    =
    add[#{x, y, z: Int | b.board[x][y][z] = X}, 1]
}

pred balanced[b: Board] {
    xturn[b] or oturn[b] or kturn[b]
}

pred winning[b: Board, p: Player] {
    -- Horizontal wins
    (some x, z: Int | {
        (b.board[x][0][z] = p and b.board[x][1][z] = p and b.board[x][2][z] = p) or
        (b.board[x][2][z] = p and b.board[x][1][z] = p and b.board[x][0][z] = p)
    })
    or
    -- Vertical wins
    (some y, z: Int | {
        (b.board[0][y][z] = p and b.board[1][y][z] = p and b.board[2][y][z] = p) or
        (b.board[2][y][z] = p and b.board[1][y][z] = p and b.board[0][y][z] = p)
    })
    or
    -- Z axis Wins
    (some x, y: Int | {
        (b.board[x][y][0] = p and b.board[x][y][1] = p and b.board[x][y][2] = p) or
        (b.board[x][y][2] = p and b.board[x][y][1] = p and b.board[x][y][0] = p)
    })
    or
    -- Diagonal wins across XZ Plane (rows and depth for each column)
    (some y: Int | {
        (b.board[0][y][0] = p and b.board[1][y][1] = p and b.board[2][y][2] = p) or
        (b.board[2][y][0] = p and b.board[1][y][1] = p and b.board[0][y][2] = p)
    })
    or
    -- Diagonal wins across YZ Plane (columns and depth for each row)
    (some x: Int | {
        (b.board[x][0][0] = p and b.board[x][1][1] = p and b.board[x][2][2] = p) or
        (b.board[x][2][0] = p and b.board[x][1][1] = p and b.board[x][0][2] = p)
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

pred move[pre: Board, x, y, z: Int, turn: Player, post: Board] {
    no pre.board[x, y, z] 
    // Validate turns 
    turn = X implies xturn[pre] 
    turn = O implies oturn[pre] 
    turn = K implies kturn[pre] 
    all p: Player | not winning[pre, p]  // Ensure no player has won before this move

    x >= 0 and x <= 2 
    y >= 0 and y <= 2
    z >= 0 and z <= 2

    post.board[x, y, z] = turn  // Apply the move to the post state

    all x2, y2, z2: Int | (x != x2 or y != y2 or z != z2) implies {
        post.board[x2, y2, z2] = pre.board[x2, y2, z2]
    }

    post.prev = pre  
}

pred doNothing[pre, post: Board] {
    some p: Player | winning[pre, p]
    
    all x, y, z: Int | {
        pre.board[x, y, z] = post.board[x, y, z]
    }

    post.prev = pre
}

one sig Game {
    first: one Board, 
    next: pfunc Board -> Board
}

// pred game_trace {
//     initial[Game.first]  // Ensure the first board is correctly initialized
//     all b: Board | { 
//         some Game.next[b] implies {
//             (some x, y, z: Int, p: Player | 
//                 move[b, x, y, z, p, Game.next[b]])  // Validate moves
//             or
//             doNothing[b, Game.next[b]]  // Handle no action if the game has concluded
//         }
//         // Additionally, ensure proper historical linking and consistency
//         b.next = Game.next[b] implies (b.next.prev = b)
//     }
// }


// run { 
//     game_trace
//     all b: Board | { 
//         some x, y, z: Int | {
//             x >= 0 and x <= 2 
//             y >= 0 and y <= 2
//             z >= 0 and z <= 2
//             no b.board[x][y][z]
//         }
//     }
// } for 10 Board for {next is linear}

pred moveValidity {
    all pre: Board, post: Board, x: Int, y: Int, z: Int, turn: Player | {
        move[pre, x, y, z, turn, post] and
        post.prev = pre 
    }
}
example validMoveOccupiedSpace is { moveValidity} for {
    Board = `Board_pre + `Board_post
    X = `X0
    O = `O0
    K = `K0
    Player = X + O + K

    `Board_pre.board = (2,1,1) -> X
    `Board_post.board = (2,1,0) -> O
    `Board_post.prev = `Board_pre
}

// example validMove is {moveValidity} for {
//     Board = `Board_pre + `Board_post
//     X = `X0
//     O = `O0
//     K = `K0
//     Player = X + O + K

//     // Initial board state setup where the space at (2,1,0) is unoccupied, and it's X's turn
//     `Board_pre.board = (1,1,0) -> O  // Assume O made a move already
//     // X makes a valid move to an unoccupied position
//     `Board_post.board = (1,1,0) -> O +  // Previous move remains
//                         (2,1,0) -> X   // X moves to an unoccupied position
// }

// example validMove is {moveValidity} for {
//     Board = `Board_pre + `Board_post
//     X = `X0
//     O = `O0
//     K = `K0
//     Player = X + O + K

//     // Assume a state where it's now X's turn to move.
//     `Board_pre.board = (1,1,0) -> O + (0,0,0) -> K  // O and K have moved, X has not yet moved
//     // X makes a valid move to an unoccupied position (2,1,0)
//     `Board_post.board = (1,1,0) -> O + (0,0,0) -> K + (2,1,0) -> X
//     `Board_post.prev = `Board_pre  // Linking post to its correct previous state
// }

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



// Update the tests to include a prev state , to check its validity when making moves