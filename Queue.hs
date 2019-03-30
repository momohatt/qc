import  Control.Monad
          (liftM2)
import  Control.Monad.ST
          (ST, runST)
import  Control.Monad.IO.Class
          (liftIO)
import  Data.STRef
          (STRef, newSTRef, readSTRef, writeSTRef)
import  Test.QuickCheck
          (arbitrary, forAll, Gen, oneof, Property, quickCheck)

data Queue s a = Queue (STRef s [a])

empty :: ST s (Queue s a)
empty = do
  r <- newSTRef []
  return (Queue r)

add :: Queue s a -> a -> ST s ()
add (Queue s) v = do
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
    Add n    -> add q n >> perform q as
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

-- operational equivalence
(=~) :: [Action] -> [Action] -> Property
c =~ c' =
  forAll (actions 0) $ \pref ->
    forAll (actions (delta (pref ++ c))) $ \suff ->
      let observe x =
            runST $ do
              q <- empty
              perform q (pref ++ x ++ suff)
       in observe c == observe c'

prop_FrontAdd :: Int -> Int -> Property
prop_FrontAdd m n =
  [Add m, Add n, Front] =~ [Add m, Front, Add n]

prop_AddRemove :: Int -> Int -> Property
prop_AddRemove m n =
  [Add m, Add n, Remove] =~ [Add m, Remove, Add n]

-- operational equivalence, when started from an empty queue
(=~^) :: [Action] -> [Action] -> Property
c =~^ c' =
  forAll (actions (delta c)) $ \suff ->
    let observe x =
          runST $ do
            q <- empty
            perform q (x ++ suff)
     in observe c == observe c'

prop_FrontEmpty :: Property
prop_FrontEmpty =
  [Front] =~^ [Return Nothing]

prop_FrontAddEmpty :: Int -> Property
prop_FrontAddEmpty m =
  [Add m, Front] =~^ [Add m, Return (Just m)]

prop_AddRemoveEmpty :: Int -> Property
prop_AddRemoveEmpty m =
  [Add m, Remove] =~^ []

main :: IO ()
main = do
  putStrLn  "prop_FrontAdd"
  quickCheck prop_FrontAdd

  putStrLn  "prop_AddRemove"
  quickCheck prop_AddRemove

  putStrLn  "prop_FrontEmpty"
  quickCheck prop_FrontEmpty

  putStrLn  "prop_FrontAddEmpty"
  quickCheck prop_FrontAddEmpty

  putStrLn  "prop_AddRemoveEmpty"
  quickCheck prop_AddRemoveEmpty
