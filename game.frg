#lang forge

abstract sig Player {} 
one sig X, O extends Player {} 

sig Board {
    board: pfunc Int -> Int -> Int -> Player // 3D board
}

pred wellformed[b: Board] {
    all row, col, z: Int | {
        (row < 0 or row > 4 or col < 0 or col > 3 or z < 0 or z > 3) implies {
             no b.board[row][col][z]
        }
    }
}

pred initial[b: Board] {
    all row, col, z: Int | no b.board[row][col][z]
}

pred xturn[b: Board] {
    #{row, col, z: Int | b.board[row][col][z] = X} 
    = 
    #{row, col, z: Int | b.board[row][col][z] = O} 
}

pred oturn[b: Board] {
    #{row, col, z: Int | b.board[row][col][z] = X} 
    = 
    add[#{row, col, z: Int | b.board[row][col][z] = O}, 1]
}

pred balanced[b: Board] {
    xturn[b] or oturn[b]
}

pred winning[b: Board, p: Player] {
    -- Horizontal wins
    some r,z: Int | r >= 0 and r <= 4 and (
        (b.board[r][0][z] = p and b.board[r][1][z] = p and b.board[r][2][z] = p and b.board[r][3][z] = p) or
        (b.board[r][1][z] = p and b.board[r][2][z] = p and b.board[r][3][z] = p and b.board[r][4][z] = p)
    )
    or
    -- Vertical wins
    (some c,z: Int | c >= 0 and c <= 3 and (
        (b.board[0][c][z] = p and b.board[1][c][z] = p and b.board[2][c][z] = p and b.board[3][c][z] = p)
    ))
    or
    -- Diagonal wins (ascending)
    (some z: Int | {
        (b.board[3][0][z] = p and b.board[2][1][z] = p and b.board[1][2][z] = p and b.board[0][3][z] = p) or
        (b.board[4][0][z] = p and b.board[3][1][z] = p and b.board[2][2][z] = p and b.board[1][3][z] = p)
    })
    or
    -- Diagonal wins (descending)
    (some z: Int | {
        (b.board[0][0][z] = p and b.board[1][1][z] = p and b.board[2][2][z] = p and b.board[3][3][z] = p) or
        (b.board[1][0][z] = p and b.board[2][1][z] = p and b.board[3][2][z] = p and b.board[4][3][z] = p)
    })
    or
    -- Z axis Wins
    (some r, c: Int | r >= 0 and r <= 4 and c >= 0 and c <= 3 and (
        (b.board[r][c][0] = p and b.board[r][c][1] = p and b.board[r][c][2] = p and b.board[r][c][3] = p)
    ))
    or
    -- XZ Plane Diagonals (across rows and depth for each column)
    (some c: Int | c >= 0 and c <= 3 and (
        (b.board[0][c][0] = p and b.board[1][c][1] = p and b.board[2][c][2] = p and b.board[3][c][3] = p) or
        (b.board[4][c][0] = p and b.board[3][c][1] = p and b.board[2][c][2] = p and b.board[1][c][3] = p)
    ))
    or
    -- YZ Plane Diagonals (across columns and depth for each row)
    (some r: Int | r >= 0 and r <= 4 and (
        (b.board[r][0][0] = p and b.board[r][1][1] = p and b.board[r][2][2] = p and b.board[r][3][3] = p) or
        (b.board[r][3][0] = p and b.board[r][2][1] = p and b.board[r][1][2] = p and b.board[r][0][3] = p)
    ))
    or
    -- 3D Diagonals
    (
        (b.board[0][0][0] = p and b.board[1][1][1] = p and b.board[2][2][2] = p and b.board[3][3][3] = p) or
        (b.board[4][0][0] = p and b.board[3][1][1] = p and b.board[2][2][2] = p and b.board[1][3][3] = p) or
        (b.board[0][3][0] = p and b.board[1][2][1] = p and b.board[2][1][2] = p and b.board[3][0][3] = p) or
        (b.board[4][3][0] = p and b.board[3][2][1] = p and b.board[2][1][2] = p and b.board[1][0][3] = p)
    )
}

pred move[pre: Board, row, col, z: Int, turn: Player, post: Board] {
    no pre.board[row][col][z]
    turn = X implies xturn[pre]
    turn = O implies oturn[pre]
    all p: Player | not winning[pre, p]

    row >= 0 and row <= 4 
    col >= 0 and col <= 3
    z >= 0 and z <= 3

    post.board[row][col][z] = turn 

    // Ensure that all other cells remain unchanged between the pre-move and post-move board states, 
    // except for the cell that was targeted by the move.
    all row2, col2, z2: Int | (row!=row2 or col!=col2 or z!=z2) implies {
        post.board[row2][col2][z2] = pre.board[row2][col2][z2]
    }
}

pred doNothing[pre, post: board] {
    -- guard
    some p: Player | winning[pre, p]
    -- action
    all r, c, z: Int | {
        pre.board[r][c][z] = post.board[r][c][z]
    }
}

one sig Game {
    first: one Board, 
    next: pfunc Board -> Board
}
pred game_trace {
    initial[Game.first]
    all b: Board | { some Game.next[b] implies {
        (some row, col, z: Int, p: Player | 
            move[b, row, col, z, p, Game.next[b]])
        or
        doNothing[b, Game.next[b]]
    }}
}

run { 
    game_trace
    all b: Board | { 
        some r,c,z: Int | {
            r >=0 r <= 4 
            c >=0 c <= 3
            z >=0 z <=3
            no b.board[r][c][z]
        }
    }
} for 10 Board for {next is linear}

// can run for 20-30 boards, but it will take some time. More than 10 boards is needed, mostly due to the fact of the 
// amount of combinations which is possible with a 5x4x3 game board

pred allBoardsWellformed { all b: Board | wellformed[b] }
example rowX_wellformed is {allBoardsWellformed} for {
    Board = `Board0
    X = `X0
    O = `O0
    Player = X + O
    `Board0.board = (0,0,0) -> X + 
                    (0,1,0) -> X + 
                    (0,2,0) -> X +
                    (0,3,0) -> X
}

example offBoardZ_not_wellformed is {not allBoardsWellformed} for {
    Board = `Board0
    X = `X0
    O = `O0
    Player = X + O
    `Board0.board = (0,0,-1) -> X + 
                    (0,1,0) -> X + 
                    (1,2,0) -> X +
                    (2,2,0) -> X
}

pred isWinner { all b: Board | winning[b,X]}
example thereIsWinner is {isWinner} for {
    Board = `Board0
    X = `X0
    O = `O0
    Player = X + O
        `Board0.board = (0,0,0) -> X + 
                    (0,1,0) -> X + 
                    (0,2,0) -> X +
                    (0,3,0) -> X
}

pred allBoardsWinning { all b: Board | winning[b, X] or winning[b, O] }
example horizontalWinExample is {allBoardsWinning} for {
    Board = `Board0
    X = `X0
    O = `O0
    Player = X + O
    `Board0.board = (0,0,0) -> X + 
                    (1,0,0) -> X + 
                    (2,0,0) -> X +
                    (0,0,0) -> X
}
example zAxisWinExample is {allBoardsWinning} for {
    Board = `Board0
    X = `X0
    O = `O0
    Player = X + O
    `Board0.board = (0,0,0) -> X + 
                    (0,0,1) -> X + 
                    (0,0,2) -> X +
                    (0,0,3) -> X
}

pred moveValidity { all pre: Board, post: Board, row: Int, col: Int, z: Int, turn: Player | move[pre, row, col, z, turn, post] }

example invalidMoveOccupiedSpace is {not moveValidity} for {
    Board = `Board1 + `Board2
    X = `X0
    O = `O0
    Player = X + O
    `Board1.board = (2,1,0) -> X 
    `Board2.board = (2,1,0) -> O
}