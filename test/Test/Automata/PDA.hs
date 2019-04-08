{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Test.Automata.PDA (htf_thisModulesTests) where

import Test.Framework
import Automata.Automaton
import Automata.PDA
import Data.Maybe
import qualified Data.Set as Set
import Data.List

type State = Integer
type StackSym = Int
type Symbol = Char

instance (Ord q, Arbitrary q) => Arbitrary (AcceptCondition q) where
  arbitrary = do s <- getSize
                 b <- arbitrary
                 if s == 0 && b
                   then return EmptyStack
                   else FinalState . Set.fromList <$> arbitrary

type DPDA' = DPDA State StackSym Symbol

prop_d_initState :: State -> Bool
prop_d_initState q = currentState m == q
  where m = dpda EmptyStack [] q 0 :: DPDA'

prop_d_initStack :: StackSym -> Bool
prop_d_initStack g = currentStack m == [g]
  where m = dpda EmptyStack [] 0 g :: DPDA'

prop_d_step :: State -> StackSym -> State -> Symbol -> [StackSym] -> Bool
prop_d_step q1 g q2 c gs =
  case step c m of
    Nothing -> False
    Just m' -> currentState m' == q2 && currentStack m' == gs
  where m = dpda EmptyStack [(q1, [(g, [(c, (q2, gs))])])] q1 g :: DPDA'

prop_d_noStep1 :: State -> StackSym -> Symbol -> Bool
prop_d_noStep1 q g c = isNothing $ step c m
  where m = dpda EmptyStack [] q g :: DPDA'

prop_d_noStep2 :: State -> StackSym -> Symbol -> Bool
prop_d_noStep2 q g c = isNothing $ step c m
  where m = dpda EmptyStack [(q, [])] q g

prop_d_noStep3 :: State -> StackSym -> Symbol -> Bool
prop_d_noStep3 q g c = isNothing $ step c m
  where m = dpda EmptyStack [(q, [(g, [])])] q g

prop_d_noStep4 :: State -> StackSym -> Symbol -> Symbol -> Property
prop_d_noStep4 q g c1 c2 = c1 /= c2 ==> isNothing $ step c2 m
  where m = dpda EmptyStack [(q, [(g, [(c1, (q, []))])])] q g

prop_d_noStep5 :: State -> StackSym -> Symbol -> StackSym -> Property
prop_d_noStep5 q g1 c g2 = g1 /= g2 ==> isNothing $ step c m
  where m = dpda EmptyStack [(q, [(g1, [(c, (q, []))])])] q g2

prop_d_decideFinalState :: State -> (Set.Set State) -> Bool
prop_d_decideFinalState q accept = isAccept (decide m) == Set.member q accept
  where m = dpda (FinalState accept) [] q 0 :: DPDA'

prop_d_decideEmptyStack :: State -> StackSym -> [StackSym] -> Symbol -> Bool
prop_d_decideEmptyStack q g gs c =
  case step c m of
    Nothing -> False
    Just m' -> isAccept (decide m') == null gs
  where m = dpda EmptyStack [(q, [(g, [(c, (q, gs))])])] q g

prop_d_total :: AcceptCondition State
             -> [(State, [(StackSym, [(Symbol, (State, [StackSym]))])])]
             -> State -> StackSym -> Bool
prop_d_total a trans q g = partialDecide (dpda a trans q g) /= Undecided

prop_d_acceptCondition :: AcceptCondition State -> State -> StackSym -> Bool
prop_d_acceptCondition a q g = acceptCondition (liftDpda m) == a
  where m = dpda a [] q g :: DPDA'

prop_d_transitions :: AcceptCondition State
                   -> [(State, [(StackSym, [(Symbol, (State, [StackSym]))])])]
                   -> State -> StackSym -> Property
prop_d_transitions a trans q g = withMaxSuccess 25 $ m == m' -- slow on large inputs
  where m      = dpda a trans q g
        trans' = dpdaTransitions m
        m'     = dpda a trans' q g

propDAccepts :: [Symbol] -> ([Symbol] -> Bool) -> AcceptCondition State
             -> [(State, [(StackSym, [(Symbol, (State, [StackSym]))])])]
             -> State -> StackSym -> Property
propDAccepts sigma p a trans q g =
  forAll (listOf $ elements sigma) $ \input -> p input == accepts (liftDpda $ dpda a trans q g) input

prop_d_accepts_1 = accepts (liftDpda $ dpda (FinalState $ Set.singleton 0) [] 0 0) ""
prop_d_accepts_2 = propDAccepts "a" (const True) (FinalState $ Set.singleton 0) [(0, [(0, [('a', (0, [0]))])])] 0 0
prop_d_accepts_3 = propDAccepts "a" (const False) EmptyStack [(0, [(0, [('a', (0, [0]))])])] 0 0
prop_d_accepts_4 = propDAccepts "+-" p (FinalState $ Set.singleton 0) trans 0 0
  where trans = [(0, [(0, [('+', (0, [1, 0]))] ),
                      (1, [('+', (0, [1, 1])),
                           ('-', (0, []))     ])])]
        p s = snd $ foldl aux ((0, 0), True) s
        aux ((plus, minus), True)  c =
          let (plus', minus') = case c of
                                '+' -> (succ plus, minus)
                                _   -> (plus, succ minus)
          in ((plus', minus'), plus' >= minus')
        aux x _ = x
-- TODO? More properties for `accepts`

type NPDA' = NPDA State StackSym Symbol
prop_n_initStatesAndStacks :: State -> StackSym -> Bool
prop_n_initStatesAndStacks q g = currentStatesAndStacks m == [(q, [g])]
  where m = npda EmptyStack [] q g :: NPDA'

prop_n_step :: State -> StackSym -> State -> Symbol -> [StackSym] -> Bool
prop_n_step q1 g q2 c gs =
  case step c m of
    Nothing -> False
    Just m' -> currentStatesAndStacks m' == [(q2, gs)]
  where m = npda EmptyStack [(q1, [(g, [(c, [(q2, gs)])])])] q1 g :: NPDA'

prop_n_noStep1 :: State -> StackSym -> Symbol -> Bool
prop_n_noStep1 q g c = isNothing $ step c m
  where m = npda EmptyStack [] q g :: NPDA'

prop_n_noStep2 :: State -> StackSym -> Symbol -> Bool
prop_n_noStep2 q g c = isNothing $ step c m
  where m = npda EmptyStack [(q, [])] q g

prop_n_noStep3 :: State -> StackSym -> Symbol -> Bool
prop_n_noStep3 q g c = isNothing $ step c m
  where m = npda EmptyStack [(q, [(g, [])])] q g

prop_n_noStep4 :: State -> StackSym -> Symbol -> Symbol -> Property
prop_n_noStep4 q g c1 c2 = c1 /= c2 ==> isNothing $ step c2 m
  where m = npda EmptyStack [(q, [(g, [(c1, [(q, [])])])])] q g

prop_n_noStep5 :: State -> StackSym -> Symbol -> StackSym -> Property
prop_n_noStep5 q g1 c g2 = g1 /= g2 ==> isNothing $ step c m
  where m = npda EmptyStack [(q, [(g1, [(c, [(q, [])])])])] q g2

prop_n_decideFinalState :: State -> (Set.Set State) -> Bool
prop_n_decideFinalState q accept = isAccept (decide m) == Set.member q accept
  where m = npda (FinalState accept) [] q 0 :: NPDA'

prop_n_decideEmptyStack :: State -> StackSym -> [StackSym] -> Symbol -> Bool
prop_n_decideEmptyStack q g gs c =
  case step c m of
    Nothing -> False
    Just m' -> isAccept (decide m') == null gs
  where m = npda EmptyStack [(q, [(g, [(c, [(q, gs)])])])] q g

prop_n_total :: AcceptCondition State
             -> [(State, [(StackSym, [(Symbol, [(State, [StackSym])])])])]
             -> State -> StackSym -> Bool
prop_n_total a trans q g = partialDecide (npda a trans q g) /= Undecided

prop_n_acceptCondition :: AcceptCondition State -> State -> StackSym -> Bool
prop_n_acceptCondition a q g = acceptCondition (liftNpda m) == a
  where m = npda a [] q g :: NPDA'

prop_n_transitions :: AcceptCondition State
                   -> [(State, [(StackSym, [(Symbol, [(State, [StackSym])])])])]
                   -> State -> StackSym -> Property
prop_n_transitions a trans q g = withMaxSuccess 25 $ m == m' -- slow on large inputs
  where m      = npda a trans q g
        trans' = npdaTransitions m
        m'     = npda a trans' q g

propNAccepts :: [Symbol] -> ([Symbol] -> Bool) -> AcceptCondition State
             -> [(State, [(StackSym, [(Symbol, [(State, [StackSym])])])])]
             -> State -> StackSym -> Property
propNAccepts sigma p a trans q g =
  forAll (listOf $ elements sigma) $ \input -> p input == accepts (liftNpda $ npda a trans q g) input

prop_n_accepts_1 = accepts (liftNpda $ npda (FinalState $ Set.singleton 0) [] 0 0) ""
prop_n_accepts_2 = propNAccepts "a" (const True) (FinalState $ Set.singleton 0) [(0, [(0, [('a', [(0, [0])])])])] 0 0
prop_n_accepts_3 = propNAccepts "a" (const False) EmptyStack [(0, [(0, [('a', [(0, [0])])])])] 0 0
prop_n_accepts_4 = propNAccepts "+-" p (FinalState $ Set.singleton 0) trans 0 0
  where trans = [(0, [(0, [('+', [(0, [1, 0])])] ),
                      (1, [('+', [(0, [1, 1])]),
                           ('-', [(0, [])])     ])])]
        p s = snd $ foldl aux ((0, 0), True) s
        aux ((plus, minus), True)  c =
          let (plus', minus') = case c of
                                '+' -> (succ plus, minus)
                                _   -> (plus, succ minus)
          in ((plus', minus'), plus' >= minus')
        aux x _ = x
-- TODO? More properties for `accepts`
