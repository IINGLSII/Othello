{-  Model Problem: Othello
    To begin game with AI, call playAI with the integer corresponding to the width of the board (must be even) i.e "playAI 8" for a standard Othello game
    Prompt asks for location of tile in (r,c) form, with non zero based indexing. 
    
    ****** WARNING : ALL INTERNAL FUNCTIONS USE ZERO BASED INDEXING ******
    
    Player always makes the first move.
    The game tree is pruned to a depth of 5.
    The scoring heuristic during the game is as follows:
      corner +10
      edge +5
      other tile +1
    At any end leaf of the game tree (the end of the game) the scoring heuristic is just +1 for every tile.
-}
module Othello where

import Data.Maybe
import Data.Ord
import Data.List
import Data.List.Split
import Data.Tree
import Data.Map (Map, empty, fromList, (!), findWithDefault, member, insert, insertWith)
import System.Random
import System.Random.Shuffle
import Control.Concurrent
import Control.Monad.State
import System.IO
import System.Console.ANSI
import GHC.IO


{- Replace with your own game data types  -}

type Loc = (Int, Int)

data Piece = X | O deriving (Eq, Show, Read)

data Board = Board { dim :: Int,
                     grid :: [[Maybe Piece]]}

opponent :: Piece -> Piece
opponent O = X 
opponent X = O

{- Some convenience functions and types -- feel free to replace/modify  -}

prune :: Int -> Tree a -> Tree a
prune 0 (Node x _) = Node x []
prune _ (Node x []) = Node x []
prune n (Node x ns) = Node x $ map (prune (n-1)) ns

printTree :: Board -> Piece -> IO ()
printTree b p = (putStrLn . drawTree . fmap show) (prune 2 (gameTree p b))

data Scored a = Scored { score :: Int, scoredVal :: a }


instance Eq (Scored a) where
  (Scored x _) == (Scored y _) = x == y


instance Ord (Scored a) where
  compare (Scored x _) (Scored y _) = compare x y


instance Show a => Show (Scored a) where
  show (Scored s v) = "Score: " ++ show s ++ "\n\n" ++ show v


-- Minimax function from lecture notes
minimax :: (a -> Scored a) -> Tree a -> Scored a
minimax scorefn (Node _ ns) = maximize ns
  where maximize = maximumBy (comparing score) . map (eval minimize)
        minimize = minimumBy (comparing score) . map (eval maximize)
        eval _ (Node x []) = scorefn x
        eval f (Node x ns) = let Scored s _ = f ns in Scored s x


-- Plays a game with the AI
playAI :: Int -> IO ()
playAI x = do let b = newBoard x
              print b
              play X b
    where play p b | null(getValidMoves p b) && null(getValidMoves (opponent p) b) = case () of
                                                                                          ()  | s > 0 -> putStrLn "Player wins"
                                                                                              | s < 0 -> putStrLn "AI wins"
                                                                                              | s == 0 -> putStrLn "Tie game"
                                                                                              where s = calcScore b
                   | null(getValidMoves p b) = do putStr "\nNo moves available, skipping turn\n"
                                                  play (opponent p) b
          -- Player
          play X b = do putStr "Enter tile location (row, column) : "
                        l <- readLn
                        case checkMove X b (f l) of [] -> do putStrLn "Illegal move"
                                                             play X b
                                                    ls -> do let b' = flipTiles ((f l):ls) b X
                                                             print b'
                                                             play O b'
          -- Bot
          play O b = do let b' = scoredVal $ othelloMinimax b O
                        print b'
                        play X b'
          f (x,y) = (x-1,y-1)

-- Board Setup

-- Print Board
instance Show Board where
  show b@(Board d g) =  topLine ++ (intercalate "\n" . addNums . chunksOf (d*2) . concat $ map showSquare (concat g))
    where showSquare Nothing = "-\t"
          showSquare (Just p) = show p ++ "\t"
          addNums xs = map (intercalate ": \t") (transpose [(map show [1..d]),xs])
          topLine = "\n\t" ++ (intercalate ": \t" (map show [1..d])) ++ ":\n"

-- Completely Empty Board
emptyBoard :: Int -> Board
emptyBoard x = Board x (replicate x (replicate x Nothing)) 

-- Handle Moves (No Valid Move Detection/Flipping)
flipTile :: Loc -> Piece -> Board -> Board
flipTile (r,c) p b = b { grid = f (grid b) r (f (grid b !! (r)) c (Just p)) }
    where f xs i v = let (pre,_:post) = splitAt (i) xs
                     in pre ++ [v] ++ post

-- plays moves from empty board
flipTiles :: [Loc] -> Board -> Piece -> Board
flipTiles moves board p = play moves p board
  where play [] _ b = b
        play (m:ms) p b = play ms p $ flipTile m p b

-- Setup Empty Board For Play
newBoard :: Int -> Board
newBoard d = flipTiles [(x-1,x),(x,x-1)] (flipTiles [(x-1,x-1),(x,x)] (emptyBoard d) X) O  -- Occupy Middle Spaces
             where x = d `div` 2


-- Tile Flipping and Proper Move Handling (tile flipping)
getValidMoves :: Piece -> Board -> [Board]
getValidMoves p b | null ms = []
                  | otherwise = ms
                  where ms = [ flipTiles (l:x) b p | l <- getEmpty b, let x = (checkMove p b l), not (null x)]

-- Returns tiles flipped given a location and piece to place (if any)
checkMove :: Piece -> Board -> Loc -> [Loc]
checkMove p b loc =  concat [f l | dir <- [(1,1),(1,0),(1,-1),(0,-1),(-1,-1),(-1,0),(-1,1),(0,1)],     -- combines flipped locations in all directions
                              let l = (flipDir p b (+++ dir) (dir +++ loc) []), l /= Nothing]
                      where (+++) (r',c') (r,c) = (r'+ r, c' + c)
                            f  (Just x) = x

-- Returns a aggregated list of flipped tiles in a given direction
flipDir :: Piece -> Board -> (Loc -> Loc) -> Loc -> [Loc] -> Maybe [Loc]
flipDir p b dir (r,c) flipped | r < 0 || r >= dim b || c < 0 || c >= dim b = Nothing                               -- Out of bounds **base case
                                | p' == Nothing = Nothing                                                          -- No enemy adj space or no eventual owned space **fail solution state
                                | p' == Just (opponent p) = flipDir p b dir (dir (r,c)) ((r,c):flipped)            -- Opponent adject space **recursive case
                                | not (null flipped) = Just flipped                                                -- Opponent had some adj space and reached owned space **success solution state
                                | otherwise = Nothing                                                 
                                  where p' = idx b (r,c)


-- Utility Board functions
idx :: Board -> Loc -> Maybe Piece
idx b (x,y) = (grid b) !! x !! y

                                                               
getEmpty :: Board -> [Loc]
getEmpty b = [(r,c) | c <- [0..(dim b -1)], r <- [0..(dim b -1)],
                      let x = idx b (r,c),
                      x == Nothing]

-- MinMax dependent functions
gameTree :: Piece -> Board -> Tree Board
gameTree p b = Node b 
             $ map (gameTree (opponent p)) (getValidMoves p b)

calcScore :: Board -> Int
calcScore b | null(getValidMoves X b) && null(getValidMoves O b) = s ts'
            | otherwise = s ts
              where ts p l | p == Just X = h l
                           | p == Just O = - h l
                    ts' p l | p == Just X = 1
                            | p == Just O = -1
                    h  l | corner l = 10
                         | edge l = 5
                         | otherwise = 1
                         where corner (r,c) = (r `mod` (dim b-1)) == 0 && (c `mod` (dim b-1)) == 0
                               edge (r,c) = (r `mod` (dim b-1)) == 0 || (c `mod` (dim b-1)) == 0
                    s f = foldl1 (+) [ f p (r,c) | c <- [0..(dim b -1)], r <- [0..(dim b -1)],
                                     let p = idx b (r,c), p /= Nothing]

scoreBoard :: Piece -> Board -> Scored Board
scoreBoard p b = case p of X -> Scored s b
                           O -> Scored (-s) b
                where s = calcScore b

othelloMinimax b p = minimax (scoreBoard p) (prune 4 (gameTree p b))