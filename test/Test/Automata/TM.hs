{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Test.Automata.TM (htf_thisModulesTests) where

import Test.Framework
import Automata.Automaton
import Automata.TM
import Data.Maybe
import qualified Data.Set as Set
import Data.List
import Control.Monad

type State = Integer
type Symbol = Char

instance Arbitrary Decision where
  arbitrary = arbitraryBoundedEnum

instance Arbitrary TapeAction where
  arbitrary = arbitraryBoundedEnum

type DTM' = DTM State Symbol

prop_d_initState :: Symbol -> State -> Bool
prop_d_initState blank start = currentState m == Right start
  where m = dtm blank start []

prop_d_stepContinue_state :: Symbol -> State -> State -> Bool
prop_d_stepContinue_state blank q1 q2 = maybe False ((== Right q2) . currentState) (step () m)
  where m = dtm blank q1 [(q1, [(blank, Right (q2, blank, Stay))])]

prop_d_stepContinue_decision :: Symbol -> State -> State -> Bool
prop_d_stepContinue_decision blank q1 q2 = maybe False ((== Undecided) . partialDecide) (step () m)
  where m = dtm blank q1 [(q1, [(blank, Right (q2, blank, Stay))])]

prop_d_stepDecide_state :: Symbol -> State -> Decision -> Bool
prop_d_stepDecide_state blank q d = maybe False ((== Left d) . currentState) (step () m)
  where m = dtm blank q [(q, [(blank, Left d)])]

prop_d_stepDecide_decision :: Symbol -> State -> Decision -> Bool
prop_d_stepDecide_decision blank q d = maybe False ((== Decided d) . partialDecide) (step () m)
  where m = dtm blank q [(q, [(blank, Left d)])]

prop_d_reject_1 :: Symbol -> State -> Bool
prop_d_reject_1 blank start = Just (Decided Reject) == (partialDecide <$> step () m)
  where m = dtm blank start []

prop_d_reject_2 :: Symbol -> State -> Bool
prop_d_reject_2 blank start = Just (Decided Reject) == (partialDecide <$> step () m)
  where m = dtm blank start [(start, [])]

prop_d_reject_3 :: Symbol -> Symbol -> State -> Property
prop_d_reject_3 blank c start = c /= blank ==> Just (Decided Reject) == (partialDecide <$> step () m)
  where m = dtm blank start [(start, [(c, Left Accept)])]

prop_d_transitions :: Symbol
                   -> [(State, [(Symbol, Either Decision (State, Symbol, TapeAction))])]
                   -> State
                   -> Bool
prop_d_transitions blank trans start = trans' == dtmTransitions m'
  where trans' = dtmTransitions $ dtm blank start trans
        m'     = dtm blank start trans'

prop_d_splice :: Symbol -> State -> [Symbol] -> Int -> Bool
prop_d_splice blank start cs n = and [ currentSymbol tape == fromMaybe blank (listToMaybe cs)
                                     , isPrefixOf blanks $ leftSymbols tape
                                     , isPrefixOf (drop 1 cs ++ blanks) $ rightSymbols tape
                                     ]
  where tape = currentTape $ spliceIntoTape cs $ dtm blank start []
        blanks = replicate n blank

prop_d_move :: Symbol -> Symbol -> Symbol -> Symbol -> Property
prop_d_move blank c1 c2 c3 = c1 /= blank ==>
  and [ isNothing failure
      , currentState m == Right 3
      , currentSymbol tape == c2
      , isPrefixOf [c1] $ leftSymbols tape
      , isPrefixOf [c3] $ rightSymbols tape
      ]
  where tape = currentTape m
        (failure, m) = runSteppable (dtm blank 0 trans) $ replicate 4 ()
        trans = [ (0, [ (blank, Right (1, c1, MoveRight))])
                , (1, [ (blank, Right (1, c1, Stay))
                      , (c1   , Right (2, c2, MoveRight))])
                , (2, [ (blank, Right (3, c3, MoveLeft))])]

propDAccepts :: Gen [Symbol] -> ([Symbol] -> Bool) -> Symbol -> State
             -> [(State, [(Symbol, Either Decision (State, Symbol, TapeAction))])]
             -> Property
propDAccepts gen p blank start trans =
  forAll gen $ \input -> p input == accepts (dtm blank start trans) input

prop_d_accepts_1 = propDAccepts (return "") (const False) '_' 0 []
prop_d_accepts_2 = propDAccepts (return "") (const False) '_' 0 [(0, [('_', Left Reject)])]
prop_d_accepts_3 = propDAccepts (return "") (const True) '_' 0 [(0, [('_', Left Accept)])]
prop_d_accepts_4 = propDAccepts (listOf $ return 'x') null '_' 0 [(0, [('_', Left Accept), ('x', Left Reject)])]
prop_d_accepts_5 = propDAccepts (listOf $ return 'x') null '_' 0 [(0, [('_', Left Accept)])]

prop_d_accepts_even = propDAccepts (listOf $ return 'x') (even . length) '_' 0 trans
  where trans = [ (0, [('_', Left Accept), ('x', Right (1, 'x', MoveRight))])
                , (1, [('_', Left Reject), ('x', Right (0, 'x', MoveRight))])]

prop_d_accepts_unary_multiplication = withMaxSuccess 50 $ propDAccepts gen p '_' 0 trans
  where gen = do a <- arbitrarySizedNatural
                 b <- arbitrarySizedNatural
                 c <- oneof [return $ a * b, choose (0, 2 * a * b)]
                 return $ replicate a 'a' ++ replicate b 'b' ++ replicate c 'c'
        p s = let count c = length $ filter (== c) s
              in count 'a' * count 'b' == count 'c'
        trans = let (start : zeroA : skipA : findB : nextB : findC : killC : clear : reset : _) = iterate succ 0
                in [ (start, [ ('_', Left Accept)
                             , ('b', Right (zeroA, '_', MoveRight))
                             , ('a', Right (skipA, '_', MoveRight))])
                   , (zeroA, [ ('_', Left Accept)
                             , ('b', Right (zeroA, '_', MoveRight))
                             , ('B', Right (zeroA, '_', MoveRight))])
                   , (skipA, [ ('a', Right (skipA, 'a', MoveRight))
                             , ('b', Right (findB, 'b', MoveRight))
                             , ('_', Left Accept)])
                   , (findB, [ ('b', Right (findB, 'b', MoveRight))
                             , ('c', Right (nextB, 'c', MoveLeft))
                             , ('B', Right (nextB, 'B', MoveLeft))])
                   , (nextB, [ ('c', Right (nextB, 'c', MoveLeft))
                             , ('B', Right (nextB, 'B', MoveLeft))
                             , ('b', Right (findC, 'B', MoveRight))
                             , ('a', Right (clear, 'a', MoveRight))
                             , ('_', Right (zeroA, '_', MoveRight))])
                   , (findC, [ ('B', Right (findC, 'B', MoveRight))
                             , ('c', Right (findC, 'c', MoveRight))
                             , ('_', Right (killC, '_', MoveLeft))])
                   , (killC, [ ('c', Right (nextB, '_', MoveLeft))])
                   , (clear, [ ('B', Right (clear, 'b', MoveRight))
                             , ('c', Right (reset, 'c', MoveLeft))])
                   , (reset, [ ('b', Right (reset, 'b', MoveLeft))
                             , ('a', Right (reset, 'a', MoveLeft))
                             , ('_', Right (start, '_', MoveRight))])]

type NTM' = NTM State Symbol

(~~) :: Ord a => [a] -> [a] -> Bool
a ~~ b = sort a == sort b

checkStatesAndDecision :: [Either Decision State] -> PartialDecision -> NTM' -> Bool
checkStatesAndDecision states' decision' m = states ~~ states' && decision == decision'
  where states = map fst $ currentStatesAndTapes m
        decision = partialDecide m

prop_n_init :: Symbol -> State -> Bool
prop_n_init blank start = checkStatesAndDecision [Right start] Undecided m
  where m = ntm blank start []

prop_n_stepContinue :: Symbol -> State -> State -> Bool
prop_n_stepContinue blank q1 q2 = maybe False (checkStatesAndDecision [Right q2] Undecided) (step () m)
  where m = ntm blank q1 [(q1, [(blank, Right [(q2, blank, Stay)])])]

prop_n_stepDecide :: Symbol -> State -> Decision -> Bool
prop_n_stepDecide blank q d = maybe False (checkStatesAndDecision [Left d] (Decided d)) (step () m)
  where m = ntm blank q [(q, [(blank, Left d)])]

prop_n_reject_1 :: Symbol -> State -> Bool
prop_n_reject_1 blank start = Just (Decided Reject) == (partialDecide <$> step () m)
  where m = ntm blank start []

prop_n_reject_2 :: Symbol -> State -> Bool
prop_n_reject_2 blank start = Just (Decided Reject) == (partialDecide <$> step () m)
  where m = ntm blank start [(start, [])]

prop_n_reject_3 :: Symbol -> Symbol -> State -> Property
prop_n_reject_3 blank c start = c /= blank ==> Just (Decided Reject) == (partialDecide <$> step () m)
  where m = ntm blank start [(start, [(c, Left Accept)])]

prop_n_reject_4 :: Symbol -> State -> Bool
prop_n_reject_4 blank start = Just (Decided Reject) == (partialDecide <$> step () m)
  where m = ntm blank start [(start, [(blank, Right [])])]

unique :: Ord a => [a] -> Bool
unique xs = nub xs == xs

prop_n_stepBranchContinueContinue :: Symbol -> State -> State -> State -> State -> State -> Property
prop_n_stepBranchContinueContinue blank q1 q2 q3 q4 q5 = unique [q1, q2, q3, q4, q5] ==>
  maybe False (checkStatesAndDecision [Right q4, Right q5] Undecided) (step () m >>= step ())
  where m = ntm blank q1 [ (q1, [(blank, Right [(q2, blank, Stay), (q3, blank, Stay)])])
                         , (q2, [(blank, Right [(q4, blank, Stay)])])
                         , (q3, [(blank, Right [(q5, blank, Stay)])])]

prop_n_stepBranchContinueAccept :: Symbol -> State -> State -> State -> State -> Property
prop_n_stepBranchContinueAccept blank q1 q2 q3 q4 = unique [q1, q2, q3, q4] ==>
  maybe False (checkStatesAndDecision [Right q4, Left Accept] (Decided Accept)) (step () m >>= step ())
  where m = ntm blank q1 [ (q1, [(blank, Right [(q2, blank, Stay), (q3, blank, Stay)])])
                         , (q2, [(blank, Right [(q4, blank, Stay)])])
                         , (q3, [(blank, Left Accept)])]

prop_n_stepBranchContinueReject :: Symbol -> State -> State -> State -> State -> Property
prop_n_stepBranchContinueReject blank q1 q2 q3 q4 = unique [q1, q2, q3, q4] ==>
  maybe False (checkStatesAndDecision [Right q4, Left Reject] Undecided) (step () m >>= step ())
  where m = ntm blank q1 [ (q1, [(blank, Right [(q2, blank, Stay), (q3, blank, Stay)])])
                         , (q2, [(blank, Right [(q4, blank, Stay)])])]

prop_n_stepBranchAcceptAccept :: Symbol -> State -> State -> State -> Property
prop_n_stepBranchAcceptAccept blank q1 q2 q3 = unique [q1, q2, q3] ==>
  maybe False (checkStatesAndDecision [Left Accept, Left Accept] (Decided Accept)) (step () m >>= step ())
  where m = ntm blank q1 [ (q1, [(blank, Right [(q2, blank, Stay), (q3, blank, Stay)])])
                         , (q2, [(blank, Left Accept)])
                         , (q3, [(blank, Left Accept)])]

prop_n_stepBranchAcceptReject :: Symbol -> State -> State -> State -> Property
prop_n_stepBranchAcceptReject blank q1 q2 q3 = unique [q1, q2, q3] ==>
  maybe False (checkStatesAndDecision [Left Accept, Left Reject] (Decided Accept)) (step () m >>= step ())
  where m = ntm blank q1 [ (q1, [(blank, Right [(q2, blank, Stay), (q3, blank, Stay)])])
                         , (q2, [(blank, Left Accept)])]

prop_n_stepBranchRejectReject :: Symbol -> State -> State -> State -> Property
prop_n_stepBranchRejectReject blank q1 q2 q3 = unique [q1, q2, q3] ==>
  maybe False (checkStatesAndDecision [Left Reject, Left Reject] (Decided Reject)) (step () m >>= step ())
  where m = ntm blank q1 [(q1, [(blank, Right [(q2, blank, Stay), (q3, blank, Stay)])])]

prop_n_transitions :: Symbol
                   -> [(State, [(Symbol, Either Decision [(State, Symbol, TapeAction)])])]
                   -> State
                   -> Bool
prop_n_transitions blank trans start = trans' == ntmTransitions m'
  where trans' = ntmTransitions $ ntm blank start trans
        m'     = ntm blank start trans'

prop_n_splice :: Symbol -> State -> [Symbol] -> Int -> Bool
prop_n_splice blank start cs n = and [ currentSymbol tape == fromMaybe blank (listToMaybe cs)
                                     , isPrefixOf blanks $ leftSymbols tape
                                     , isPrefixOf (drop 1 cs ++ blanks) $ rightSymbols tape
                                     ]
  where tape = snd $ head $ currentStatesAndTapes $ spliceIntoTapes cs $ ntm blank start []
        blanks = replicate n blank

prop_n_move :: Symbol -> Symbol -> Symbol -> Symbol -> Property
prop_n_move blank c1 c2 c3 = c1 /= blank ==>
  and [ isNothing failure
      , state1 == Right 3
      , currentSymbol tape1 == c2
      , isPrefixOf [c1] $ leftSymbols tape1
      , isPrefixOf [c3] $ rightSymbols tape1
      , state2 == Right 4
      , currentSymbol tape2 == c1
      , isPrefixOf [c1] $ leftSymbols tape2
      , isPrefixOf [c3] $ rightSymbols tape2
      ]
  where [(state1, tape1), (state2, tape2)] = currentStatesAndTapes m
        (failure, m) = runSteppable (ntm blank 0 trans) $ replicate 4 ()
        trans = [ (0, [ (blank, Right [(1, c1, MoveRight)])])
                , (1, [ (blank, Right [(1, c1, Stay), (2, c1, MoveRight)])
                      , (c1   , Right [(2, c2, MoveRight)])])
                , (2, [ (blank, Right [(3, c3, MoveLeft)])])
                , (3, [ (c1   , Right [(4, c1, Stay)])])]

propNAccepts :: Gen [Symbol] -> ([Symbol] -> Bool) -> Symbol -> State
             -> [(State, [(Symbol, Either Decision [(State, Symbol, TapeAction)])])]
             -> Property
propNAccepts gen p blank start trans =
  forAll gen $ \input -> p input == accepts (ntm blank start trans) input

prop_n_accepts_1 = propNAccepts (return "") (const False) '_' 0 []
prop_n_accepts_2 = propNAccepts (return "") (const False) '_' 0 [(0, [('_', Left Reject)])]
prop_n_accepts_3 = propNAccepts (return "") (const True) '_' 0 [(0, [('_', Left Accept)])]
prop_n_accepts_4 = propNAccepts (listOf $ return 'x') null '_' 0 [(0, [('_', Left Accept), ('x', Left Reject)])]
prop_n_accepts_5 = propNAccepts (listOf $ return 'x') null '_' 0 [(0, [('_', Left Accept)])]

prop_n_accepts_even = propNAccepts (listOf $ return 'x') (even . length) '_' 0 trans
  where trans = [ (0, [('_', Left Accept), ('x', Right [(1, 'x', MoveRight)])])
                , (1, [('_', Left Reject), ('x', Right [(0, 'x', MoveRight)])])]

prop_n_accepts_composite = withMaxSuccess 50 $ propNAccepts gen p '_' 0 trans
  where gen = listOf $ return 'x'
        p s = let n = length s in any ((== 0) . (mod n)) [2..(floor $ sqrt $ fromIntegral n)]
        trans = let (start : guess : reset : killF : findX : killX : findF : _) = iterate succ 0
                in [ (start, [ ('x', Right [ (guess, 'F', MoveRight)])])
                   , (guess, [ ('x', Right [ (guess, 'F', MoveRight)
                                           , (reset, 'F', Stay)])])
                   , (reset, [ ('F', Right [ (reset, 'f', MoveLeft)])
                             , ('_', Right [ (killF, '_', MoveRight)])])
                   , (killF, [ ('f', Right [ (findX, 'F', MoveRight)])
                             , ('x', Right [ (reset, 'x', MoveLeft)])
                             , ('_', Left Accept)])
                   , (findX, [ ('f', Right [ (findX, 'f', MoveRight)])
                             , ('x', Right [ (findX, 'x', MoveRight)])
                             , ('_', Right [ (killX, '_', MoveLeft)])])
                   , (killX, [ ('x', Right [ (findF, '_', MoveLeft)])])
                   , (findF, [ ('x', Right [ (findF, 'x', MoveLeft)])
                             , ('f', Right [ (findF, 'f', MoveLeft)])
                             , ('F', Right [ (killF, 'F', MoveRight)])])]
