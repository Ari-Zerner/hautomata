{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module Automata.FSA (
  DFA,
  dfa,
  currentState,
  acceptingStates,
  transitions,
  accepts
) where

import Automata.Automaton
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Data.Maybe
import Control.Monad

-- |The non-state data of a finite state automaton.
data FSADef state symbol =
  FSADef
    (Set.Set state) -- ^accepting states
    (Map.Map (state, symbol) state) -- ^transitions
  deriving (Show) -- TODO: remove in production

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

-- |Get the accepting states of a DFA.
acceptingStates :: DFA state symbol -> [state]
acceptingStates (DFA (FSADef accepting _) _) = Set.toList accepting

-- |Get the transitions of a DFA, organized by source state.
transitions :: (Ord state, Ord symbol) => DFA state symbol -> [(state,  [(symbol, state)])]
transitions (DFA (FSADef _ trans) _) = Map.toList $ Map.toList <$> Map.foldrWithKey aux Map.empty trans
  where aux (q1, s) q2 acc = Map.insertWith Map.union q1 (Map.singleton s q2) acc

-- |Determine whether a DFA accepts a given list of symbols.
accepts :: (Ord state, Ord symbol) => DFA state symbol -> [symbol] -> Bool
accepts m input = maybe False (isAccept . decide) $ foldM (flip step) m input

instance (Ord state, Ord symbol) => Steppable symbol (DFA state symbol) where
  step s (DFA (FSADef accepting trans) current) = (DFA $ FSADef accepting trans) <$> trans Map.!? (current, s)

instance (Ord state) => PartialDecider (DFA state symbol) where
  partialDecide = Decided . decide

instance (Ord state) => Decider (DFA state symbol) where
  decide (DFA (FSADef accepting _) current) = if Set.member current accepting then Accept else Reject
