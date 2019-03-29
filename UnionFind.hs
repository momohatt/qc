{-# LANGUAGE Rank2Types #-}

import  Data.List
import  Data.STRef
          (STRef, newSTRef, readSTRef, writeSTRef)
import  Test.QuickCheck
import  Test.QuickCheck.Monadic
import  Control.Monad.ST

data Element s a = Element a (STRef s (Link s a))
data Link s a = Weight Int
              | Next (Element s a)

instance Eq (Element s a) where
  Element _ r == Element _ r' = r == r'

newElement :: a -> ST s (Element s a)
newElement a = do
  r <- newSTRef (Weight 1)
  return (Element a r)

findElement :: Element s a -> ST s (Element s a)
findElement (Element a r) = do
  e <- readSTRef r
  case e of
    Weight w -> return (Element a r)
    Next next -> do
      last <- findElement next
      writeSTRef r (Next last)
      return last

unionElements :: Element s a -> Element s a -> ST s ()
unionElements e1 e2 = do
  Element a1 r1 <- findElement e1
  Element a2 r2 <- findElement e2
  Weight w1 <- readSTRef r1
  Weight w2 <- readSTRef r2

  if w1 <= w2
    then do
      writeSTRef r1 (Next (Element a2 r2))
      writeSTRef r2 (Weight (w1 + w2))
    else do
      writeSTRef r2 (Next (Element a1 r1))
      writeSTRef r1 (Weight (w1 + w2))

data Action = New
            | Find Var
            | Union Var Var
            deriving Show

-- We use natural numbers to refer to elements in order of creation.
-- (This should be 0-indexed.)
type Var = Int

-- Semantics of action sequences is defined by:
exec :: [Action] -> [Element a ()] -> ST a [Element a ()]
exec [] es = return es
exec (a:as) es =
  case a of
    New -> do
      e <- newElement ()
      exec as $ es ++ [e]
    Find x -> do
      _ <- findElement $ es !! x
      exec as es
    Union x y -> do
      _ <- unionElements (es !! x) (es !! y)
      exec as es


-- Generator for the set of programs well-formed in the context of k elements
actions :: Int -> Gen [Action]
actions 0 =
  frequency [(25, (New :) <$> actions 1),
             (1, return [])]
actions n =
  frequency [(2, (New :) <$> actions (n + 1)),
             (2, (:) <$> (Find <$> element) <*> actions n),
             (2, (:) <$> (Union <$> element <*> element) <*> actions n),
             (1, return [])]
    where element = choose (0, n - 1)

-- quantifying over all states
-- TODO: what is 'imperative' ?
-- forAllStates :: (forall s. [Element s ()] -> PropertyM (ST s) a) -> Property
-- forAllStates p =
--   forAll (actions 0) $ \as ->
--     imperative (do
--       vars <- run (exec as [])
--       p vars)

pickElement :: Monad m => [a] -> PropertyM m a
pickElement vars = do
  pre (not (null vars))
  i <- pick (choose (0, length vars - 1))
  return (vars !! i)

-- findElement without side effect
representative :: Element a b -> ST a (Element a b)
representative (Element a r) = do
  e <- readSTRef r
  case e of
    Weight w -> return (Element a r)
    Next next -> representative next

two :: Monad m => m a -> m (a, a)
two x = (\x -> (x, x)) <$> x

three :: Monad m => m a -> m (a, a, a)
three x = (\x -> (x, x, x)) <$> x

prop_FindReturnsRep =
  forAllStates $ \vars ->
    do
      v <- pickElement vars
      r <- run (representative v)
      r' <- run (findElement v)
      assert (r == r')

prop_FindPreservesReps =
  forAllStates $ \vars ->
    do
      (v, v') <- two (pickElement vars)
      r0 <- run (representative v)
      r' <- run (findElement v')
      r1 <- run (representative v)
      assert (r0 == r1)

prop_UnionPreservesOtherReps =
  forAllStates $ \vars ->
    do
      (v0, v1, v2) <- three (pickElement vars)
      [r0, r1, r2] <- run (mapM representative [v0, v1, v2])
      pre (r0 /= r1 && r0 /= r2)
      run (unionElements v1 v2)
      r0' <- run (representative v0)
      assert (r0 == r0')

prop_UnionUnites =
  forAllStates $ \vars ->
    do
      (v1, v2) <- two (pickElement vars)
      c1 <- run (equivClass vars v1)
      c2 <- run (equivClass vars v2)
      run (unionElements v1 v2)
      c1' <- run (mapM representative c1)
      c2' <- run (mapM representative c2)
      assert (length (nub (c1' ++ c2')) == 1)


position :: Eq a => [a] -> a -> Int
position [] _ = error "position: not a member of the list"
position (x:xs) a
  | x == a    = 0
  | otherwise = 1 + position xs a

abstract :: [Element a b] -> ST a [Int]
abstract vars = mapM abs vars
  where
    abs v = do
      r <- representative v
      return (position vars r)

prop_Invariant =
  forAllStates $ \vars ->
    do
      repr <- run (abstract vars)
      assert (repr == map (repr !!) repr)

findS x repr y repr' =
  repr == repr' && y == repr !! x

unionS x y repr () repr' =
  let z = repr' !! x in
      (z == repr !! x || z == repr !! y) &&
        repr' == [if z' == repr !! x || z' == repr !! y
                     then z else z' | z' <- repr]

implements vars m s = do
  repr  <- run (abstract vars)
  ans   <- run m
  repr' <- run (abstract vars)
  assert (s repr ans repr')

prop_Find =
  forAllStates $ \vars ->
    do
      v <- pickElement vars
      implements vars
        (position vars <$> findElement v)
        (findS (position vars v))

prop_Union =
  forAllStates $ \vars ->
    do
      (v, v') <- two (pickElement vars)
      implements vars
        (unionElements v v')
        (unionS (position vars v) (position vars v'))
