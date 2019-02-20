{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module Automata.FSA (
  DFA,
  dfa,
  currentState,
  FSA,
  liftDfa,
  acceptingStates,
  transitions,
  accepts
) where

import Automata.Automaton
import qualified Data.Set.Monad as Set
import qualified Data.Map.Strict as Map
import Data.Maybe
import Control.Monad

-- |The non-state data of a finite state automaton.
data FSADef state symbol =
  FSADef
    (Set.Set state) -- ^accepting states
    (Map.Map (state, symbol) state) -- ^transitions
  deriving (Show) -- TODO: remove in production

--- DFA

-- |A deterministic finite state automaton.
data DFA state symbol = DFA (FSADef state symbol) state
  deriving (Show) -- TODO: remove in production

-- |Create a new DFA.
dfa :: (Ord state, Ord symbol)
    => state -- ^The initial state
    -> [state] -- ^The accepting states
    -> [(state,  [(symbol, state)])] -- ^For each state, the list of transitions from that state
    -> DFA state symbol
dfa initial accepting transitions = DFA (FSADef (Set.fromList accepting) transitionMap) initial
  where transitionMap = Map.fromList [ ((state, symbol), newState)
                                     | (state, stateTransitions) <- transitions
                                     , (symbol, newState) <- stateTransitions
                                     ]

-- |Get the current state of a DFA.
currentState :: DFA state symbol -> state
currentState (DFA _ current) = current

instance (Ord state, Ord symbol) => Steppable symbol (DFA state symbol) where
  step s (DFA (FSADef accepting trans) current) = (DFA $ FSADef accepting trans) <$> trans Map.!? (current, s)

instance (Ord state) => PartialDecider (DFA state symbol) where
  partialDecide = Decided . decide

instance (Ord state) => Decider (DFA state symbol) where
  decide (DFA (FSADef accepting _) current) = if Set.member current accepting then Accept else Reject

--- FSA

-- |A finite state automaton.
data FSA state symbol = D (DFA state symbol)

-- |Lift a DFA to a generic FSA.
liftDfa :: DFA state symbol -> FSA state symbol
liftDfa = D

-- |Get the accepting states of a FSA.
acceptingStates :: Ord state => FSA state symbol -> [state]
acceptingStates (D (DFA (FSADef accepting _) _)) = Set.toList accepting

-- |Get the transitions of a FSA, organized by source state.
transitions :: (Ord state, Ord symbol) => FSA state symbol -> [(state,  [(symbol, state)])]
transitions m = case m of
  D (DFA (FSADef _ trans) _) -> transitions' trans
  where transitions' trans = Map.toList $ Map.toList <$> Map.foldrWithKey aux Map.empty trans
        aux (q1, s) q2 acc = Map.insertWith Map.union q1 (Map.singleton s q2) acc

instance (Ord state, Ord symbol) => Steppable symbol (FSA state symbol) where
  step s (D m) = D <$> step s m

instance (Ord state) => PartialDecider (FSA state symbol) where
  partialDecide (D m) = partialDecide m

instance (Ord state) => Decider (FSA state symbol) where
  decide (D m) = decide m

-- |Determine whether a FSA accepts a list of symbols.
accepts :: (Ord state, Ord symbol) => FSA state symbol -> [symbol] -> Bool
accepts m input = maybe False (isAccept . decide) $ foldM (flip step) m input
