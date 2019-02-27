{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Test.Automata.FSA (htf_thisModulesTests) where

import Test.Framework
import Automata.Automaton
import Automata.FSA
import Data.Maybe
import qualified Data.Set as Set
import Data.List

type State = Integer
type Symbol = Char

type DFA' = DFA State Symbol

prop_d_initState :: State -> Bool
prop_d_initState start = currentState m == start
  where m = dfa [] [] start :: DFA'

prop_d_stepState :: State -> State -> Symbol -> Bool
prop_d_stepState q1 q2 c = maybe False ((== q2) . currentState) (step c m)
  where m = dfa [] [(q1, [(c, q2)])] q1 :: DFA'

prop_d_noStep1 :: State -> Symbol -> Bool
prop_d_noStep1 start c = isNothing $ step c m
  where m = dfa [] [] start :: DFA'

prop_d_noStep2 :: State -> Symbol -> Bool
prop_d_noStep2 start c = isNothing $ step c m
  where m = dfa [] [(start, [])] start

prop_d_noStep3 :: State -> Symbol -> Symbol -> Property
prop_d_noStep3 start c1 c2 = c1 /= c2 ==> isNothing $ step c2 m
  where m = dfa [] [(start, [(c1, start)])] start

prop_d_decide :: State -> [State] -> Bool
prop_d_decide start accept = isAccept (decide m) == elem start accept
  where m = dfa accept [] start :: DFA'

prop_d_total :: State -> [State] -> [(State, [(Symbol, State)])] -> Bool
prop_d_total start accept trans = partialDecide (dfa accept trans start) /= Undecided

prop_d_acceptingStates :: State -> [State] -> Bool
prop_d_acceptingStates start accept = Set.fromList (acceptingStates $ liftDfa m) == Set.fromList accept
  where m = dfa accept [] start :: DFA'

prop_d_transitions :: State -> [State] -> [(State, [(Symbol, State)])] -> Bool
prop_d_transitions start accept trans = m == m'
  where m      = dfa accept trans start
        trans' = dfaTransitions m
        m'     = dfa accept trans' start

propDAccepts :: [Symbol] -> ([Symbol] -> Bool) -> State -> [State] -> [(State, [(Symbol, State)])] -> Property
propDAccepts sigma p start accept trans =
  forAll (listOf $ elements sigma) $ \input -> p input == accepts (liftDfa $ dfa accept trans start) input

prop_d_accepts_1 = propDAccepts "ab" (const False) 0 [] []
prop_d_accepts_2 = accepts (liftDfa $ dfa [0] [] 0) ""
prop_d_accepts_3 = propDAccepts "a" (const True) 0 [0] [(0, [('a', 0)])]
-- TODO? More properties for `accepts`

type NFA' = NFA State Symbol

prop_n_initState :: State -> Bool
prop_n_initState start = currentStates m == [start]
  where m = nfa [] [] start :: NFA'

prop_n_symStepState :: State -> State -> Symbol -> Bool
prop_n_symStepState q1 q2 c = maybe False ((== [q2]) . currentStates) (step c m)
  where m = nfa [] [(q1, ([(c, [q2])], []))] q1 :: NFA'

prop_n_eStepState :: State -> State -> Bool
prop_n_eStepState q1 q2 = elem q1 (currentStates m) && elem q2 (currentStates m)
  where m = nfa [] [(q1, ([], [q2]))] q1 :: NFA'

prop_n_noStep1 :: State -> Symbol -> Bool
prop_n_noStep1 start c = isNothing $ step c m
  where m = nfa [] [] start :: NFA'

prop_n_noStep2 :: State -> Symbol -> Bool
prop_n_noStep2 start c = isNothing $ step c m
  where m = nfa [] [(start, ([], []))] start

prop_n_noStep3 :: State -> Symbol -> Symbol -> Property
prop_n_noStep3 start c1 c2 = c1 /= c2 ==> isNothing $ step c2 m
  where m = nfa [] [(start, ([(c1, [start])], []))] start

prop_n_decide :: State -> [State] -> Bool
prop_n_decide start accept = isAccept (decide m) == elem start accept
  where m = nfa accept [] start :: NFA'

prop_n_total :: State -> [State] -> [(State,  ([(Symbol, [State])], [State]))] -> Bool
prop_n_total start accept trans = partialDecide (nfa accept trans start) /= Undecided

prop_n_acceptingStates :: State -> [State] -> Bool
prop_n_acceptingStates start accept = Set.fromList (acceptingStates $ liftNfa m) == Set.fromList accept
  where m = nfa accept [] start :: NFA'

prop_n_transitions :: State -> [State] -> [(State,  ([(Symbol, [State])], [State]))] -> Bool
prop_n_transitions start accept trans = m == m'
  where m      = nfa accept trans start
        trans' = nfaTransitions m
        m'     = nfa accept trans' start

propNAccepts :: [Symbol] -> ([Symbol] -> Bool) -> State -> [State] -> [(State,  ([(Symbol, [State])], [State]))] -> Property
propNAccepts sigma p start accept trans =
  forAll (listOf $ elements sigma) $ \input -> p input == accepts (liftNfa $ nfa accept trans start) input

prop_n_accepts_1 = propNAccepts "ab" (const False) 0 [] []
prop_n_accepts_2 = propNAccepts "ab" ("baa" `isSuffixOf`) 0 [3] trans
  where trans = [ (0, ([('a', [0]), ('b', [0, 1])], []))
                , (1, ([('a', [2])], []))
                , (2, ([('a', [3])], []))
                ]
-- TODO? More properties for `accepts`
