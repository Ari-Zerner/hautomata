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
prop_d_reject_1 blank start = Just Reject == (partialDecide <$> step () m >>= maybeFromPartial)
  where m = dtm blank start []

prop_d_reject_2 :: Symbol -> State -> Bool
prop_d_reject_2 blank start = Just Reject == (partialDecide <$> step () m >>= maybeFromPartial)
  where m = dtm blank start [(start, [])]

prop_d_reject_3 :: Symbol -> Symbol -> State -> Property
prop_d_reject_3 blank c start = c /= blank ==> Just Reject == (partialDecide <$> step () m >>= maybeFromPartial)
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
