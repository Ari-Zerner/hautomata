{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Test.Automata.FSA (htf_thisModulesTests) where

import Test.Framework
import Automata.Automaton
import Automata.FSA
import Data.Maybe
import qualified Data.Set as Set
import Data.List

type DFA' = DFA Integer Char

prop_initState :: Integer -> Bool
prop_initState start = currentState m == start
  where m = dfa start [] [] :: DFA'

prop_stepState :: Integer -> Integer -> Char -> Bool
prop_stepState q1 q2 c = maybe False ((== q2) . currentState) (step c m)
  where m = dfa q1 [] [(q1, [(c, q2)])] :: DFA'

prop_noStep1 :: Integer -> Char -> Bool
prop_noStep1 start c = isNothing $ step c m
  where m = dfa start [] [] :: DFA'

prop_noStep2 :: Integer -> Char -> Bool
prop_noStep2 start c = isNothing $ step c m
  where m = dfa start [] [(start, [])]

prop_noStep3 :: Integer -> Char -> Char -> Property
prop_noStep3 start c1 c2 = c1 /= c2 ==> isNothing $ step c2 m
  where m = dfa start [] [(start, [(c1, start)])]

prop_decide :: Integer -> [Integer] -> Bool
prop_decide start accept = isAccept (decide m) == elem start accept
  where m = dfa start accept [] :: DFA'

prop_total :: Integer -> [Integer] -> [(Integer, [(Char, Integer)])] -> Bool
prop_total start accept trans = partialDecide (dfa start accept trans) /= Undecided

prop_acceptingStates :: Integer -> [Integer] -> Bool
prop_acceptingStates start accept = Set.fromList (acceptingStates m) == Set.fromList accept
  where m = dfa start accept [] :: DFA'

prop_transitions :: Integer -> [Integer] -> [(Integer, [(Char, Integer)])] -> Bool
prop_transitions start accept trans = flatSet (deDup trans) == flatSet trans'
  where trans'    = transitions $ dfa start accept (deDup trans)
        fstEq a b = fst a == fst b
        deDup     = map (fmap (nubBy fstEq)) . nubBy fstEq
        flatSet t = Set.fromList [(q1, s, q2) | (q1, sAndQ2s) <- t, (s, q2) <- sAndQ2s]

propAccepts :: Bool -> Integer -> [Integer] -> [(Integer, [(Char, Integer)])] -> [Char] -> Property
propAccepts expected start accept trans sigma =
  forAll (listOf $ elements sigma) $ \input -> expected == (accepts (dfa start accept trans) input)

prop_accepts_1 = propAccepts False 0 [] [] "ab"
prop_accepts_2 = accepts (dfa 0 [0] []) ""
prop_accepts_3 = propAccepts True 0 [0] [(0, [('a', 0)])] "a"
-- TODO? More properties for `accepts`