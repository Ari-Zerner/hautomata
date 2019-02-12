{-# LANGUAGE RecordWildCards, MultiParamTypeClasses, FlexibleInstances #-}

module Automata.FSA (
  FSA,
  fsa,
  state,
  acceptingStates,
  transitions,
  accepts
) where

import Automata.Automaton
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Data.Maybe
import Control.Monad

-- |A finite state automaton.
data FSA state symbol =
  FSA { current     :: state
      , accepting   :: Set.Set state
      , transitionMap :: Map.Map (state, symbol) state
      }
  deriving (Show) -- TODO: remove in production

-- |Create a new FSA.
fsa :: (Ord state, Ord symbol)
    => state -- ^The initial state
    -> [state] -- ^The accepting states
    -> [(state,  [(symbol, state)])] -- ^For each state, the list of transitions from that state
    -> FSA state symbol
fsa start accept trans = FSA { current = start
                             , accepting = Set.fromList accept
                             , ..
                             }
  where transitionMap = Map.fromList [ ((state, symbol), newState)
                                | (state, stateTrans) <- trans
                                , (symbol, newState) <- stateTrans
                                ]

-- |Get the current state of a FSA.
state :: FSA state symbol -> state
state = current

-- |Get the accepting states of a FSA.
acceptingStates :: FSA state symbol -> [state]
acceptingStates FSA{..} = Set.toList accepting

-- |Get the transitions of a FSA, organized by source state.
transitions :: (Ord state, Ord symbol) => FSA state symbol -> [(state,  [(symbol, state)])]
transitions FSA{..} = Map.toList $ Map.toList <$> Map.foldrWithKey aux Map.empty transitionMap
  where aux (q1, s) q2 acc = Map.insertWith Map.union q1 (Map.singleton s q2) acc

-- |Determine whether a FSA accepts a given list of symbols.
accepts :: (Ord state, Ord symbol) => FSA state symbol -> [symbol] -> Bool
accepts m input = maybe False (isAccept . decide) $ foldM (flip step) m input

instance (Ord state, Ord symbol) => Steppable symbol (FSA state symbol) where
  step s FSA{..} = (\current -> FSA{..}) <$> transitionMap Map.!? (current, s)

instance (Ord state) => PartialDecider (FSA state symbol) where
  partialDecide = Decided . decide

instance (Ord state) => Decider (FSA state symbol) where
  decide FSA{..} = if Set.member current accepting then Accept else Reject
