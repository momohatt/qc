{-# LANGUAGE Rank2Types #-}

import  Control.Monad
          (liftM2)
import  Control.Monad.ST
          (ST, runST)
import  Data.Maybe
          (isJust)
import  Data.STRef
          (STRef, newSTRef, readSTRef, writeSTRef)
import  Test.QuickCheck
          (arbitrary, forAll, Gen, oneof, Property, quickCheck, (==>))

data Queue s a = Queue (STRef s [a])

empty :: ST s (Queue s a)
empty = do
  r <- newSTRef []
  return (Queue r)

add :: a -> Queue s a -> ST s ()
add v (Queue s) = do
  q <- readSTRef s
  writeSTRef s (q ++ [v])

remove :: Queue s a -> ST s ()
remove (Queue s) = do
  q <- readSTRef s
  case q of
    []  -> writeSTRef s []
    _:x -> writeSTRef s x

front :: Queue s a -> ST s (Maybe a)
front (Queue s) = do
  q <- readSTRef s
  case q of
    []  -> return Nothing
    x:_ -> return $ Just x

data Action
  = Add Int
  | Remove
  | Front
  | Return (Maybe Int)
  deriving (Eq, Show)

-- returns list of operation results
perform :: Queue a Int -> [Action] -> ST a [Maybe Int]
perform q [] = return []
perform q (a:as) =
  case a of
    Add n    -> add n q >> perform q as
    Remove   -> remove q >> perform q as
    Front    -> liftM2 (:) (front q) (perform q as)
    Return x -> (x :) <$> perform q as

actions :: (Eq a, Num a) => a -> Gen [Action]
actions n =
  oneof ([return [],
          liftM2 (:) (Add <$> arbitrary)
                     (actions (n + 1)),
          (Front :) <$> actions n] ++
          if n == 0
             then []
             else [(Remove :) <$> actions (n - 1)])

-- compute then change in the number of queue elements
delta :: [Action] -> Int
delta [] = 0
delta (a:as) =
  case a of
    Add _    -> delta as + 1
    Remove   -> delta as - 1
    Front    -> delta as
    Return _ -> delta as

-- Specification based on abstract model of queues
emptyS = []
addS a q = ((), q ++ [a])
removeS (_:q) = ((), q)
frontS []    = (Nothing, [])
frontS (a:q) = (Just a, a : q)

-- Maps the implementation state to the abstract value that it represents
abstract :: Queue s a -> ST s [a]
abstract (Queue s) =
  readSTRef s

-- An implementation is correct if it commutes with abstract.
commutes :: Eq a => Queue s Int -> (Queue s Int -> ST s a) -> ([Int] -> (a, [Int])) -> ST s Bool
commutes q a f = do
  old <- abstract q
  x <- a q
  new <- abstract q
  return ((x, new) == f old)

implements :: Eq a => (forall s. Queue s Int -> ST s a) -> ([Int] -> (a, [Int])) -> Property
a `implements` f =
  forAll (actions 0) $ \as ->
    runST $ do
      q <- empty
      perform q as
      commutes q a f

prop_Add :: Int -> Property
prop_Add n = add n `implements` addS n

prop_Front :: Property
prop_Front = front `implements` frontS

-- prop_Empty :: Property
prop_Empty =
  runST $ do
    q <- empty
    q' <- abstract q
    return (q' == (emptyS :: [Int]))

-- implements with precondition
implementsIf :: Eq a => (forall s. Queue s Int -> ST s Bool) ->
                        (forall s. Queue s Int -> ST s a) ->
                        ([Int] -> (a, [Int])) -> Property
implementsIf pre a f =
  forAll (actions 0) $ \as ->
    runST (do
      q <- empty
      perform q as
      pre q) ==>
    runST (do
      q <- empty
      perform q as
      commutes q a f)

prop_Remove :: Property
prop_Remove =
  implementsIf (fmap isJust . front) remove removeS

main :: IO ()
main = do
  putStrLn  "prop_Add"
  quickCheck prop_Add

  putStrLn  "prop_Front"
  quickCheck prop_Front

  putStrLn  "prop_Empty"
  quickCheck prop_Empty

  putStrLn  "prop_Remove"
  quickCheck prop_Remove
