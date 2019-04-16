{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module Automata.TM (
  TapeAction(..),
  Tape,
  currentSymbol,
  leftSymbols,
  rightSymbols,
  DTM,
  dtm,
  spliceIntoTape,
  currentState,
  currentTape,
  dtmTransitions,
  NTM,
  ntm,
  spliceIntoTapes,
  currentStatesAndTapes,
  ntmTransitions,
  TM,
  liftDtm,
  liftNtm,
  dtmOrNtm
) where

import Automata.Automaton
import Data.InfList
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set

data TapeAction = MoveLeft | Stay | MoveRight
  deriving (Eq, Ord, Read, Show, Bounded, Enum)

-- |A Turing machine tape. Infinite in both directions.
data Tape symbol = Tape
  (InfList symbol) -- ^left of head
  symbol -- ^head
  (InfList symbol) -- ^right of head

-- |Get the symbol under the tape head.
currentSymbol :: Tape symbol -> symbol
currentSymbol = undefined

-- |Get the symbols to the left of the tape head, closest first.
leftSymbols :: Tape symbol -> [symbol]
leftSymbols = undefined

-- |Get the symbols to the right of the tape head, closest first.
rightSymbols :: Tape symbol -> [symbol]
rightSymbols = undefined

--- DTM

-- |A deterministic Turing machine.
data DTM state symbol = DTM
  (Map.Map (state, symbol) (Either Decision (state, symbol, TapeAction))) -- ^transitions
  (Either Decision state) -- ^state
  (Tape symbol) -- ^tape

-- |Create a new DTM.
dtm :: (Ord state, Ord symbol)
    => symbol -- ^the "blank" symbol
    -> [(state, [(symbol, Either Decision (state, symbol, TapeAction))])] -- ^for each state, the list of transitions from that state
    -> state -- ^the initial state
    -> DTM state symbol
dtm = undefined

-- |Splice a list of symbols into the tape. The first symbol in the list will be
-- under the tape head, with the remainder to the right.
spliceIntoTape :: [symbol] -> DTM state symbol -> DTM state symbol
spliceIntoTape = undefined

-- |Get the current state of a DTM.
currentState :: DTM state symbol -> Either Decision state
currentState = undefined

-- |Get the current tape of a DTM.
currentTape :: DTM state symbol -> Tape symbol
currentTape = undefined

-- |Get the transitions of a DTM.
dtmTransitions :: DTM state symbol
               -> [(state, [(symbol, Either Decision (state, symbol, TapeAction))])]
dtmTransitions = undefined

instance (Ord state, Ord symbol) => Steppable () (DTM state symbol) where
  step = undefined

instance PartialDecider (DTM state symbol) where
  partialDecide = undefined

instance (Ord state, Ord symbol) => Accepter symbol (DTM state symbol) where
  accepts = accepts = accepts . liftNtm

--- NTM

-- |A non-deterministic Turing machine.
data NTM state symbol = NTM
  (Map.Map (state, symbol) (Either Decision (Set.Set (state, symbol, TapeAction)))) -- ^transitions
  (Set.Set (Either Decision state, Tape symbol)) -- ^state/tape pairs

-- |Create a new NTM.
ntm :: (Ord state, Ord symbol)
    => symbol -- ^the "blank" symbol
    -> [(state, [(symbol, Either Decision [(state, symbol, TapeAction)])])] -- ^for each state, the list of transitions from that state
    -> state -- ^the initial state
    -> NTM state symbol
ntm = undefined

-- |As `spliceIntoTape`, but applied to every computation branch.
spliceIntoTapes :: [symbol] -> NTM state symbol -> NTM state symbol
spliceIntoTapes = undefined

-- |Get the current state/tape of every computation branch of an NTM.
currentStatesAndTapes :: NTM state symbol -> [(state, Tape symbol)]
currentStatesAndTapes = undefined

-- |Get the transitions of a NTM.
ntmTransitions :: NTM state symbol
               -> [(state, [(symbol, Either Decision [(state, symbol, TapeAction)])])]
ntmTransitions = undefined

instance (Ord state, Ord symbol) => Steppable () (NTM state symbol) where
  step = undefined

instance PartialDecider (NTM state symbol) where
  partialDecide = undefined

instance (Ord state, Ord symbol) => Accepter symbol (NTM state symbol) where
  accepts = accepts . liftNtm

--- TM

-- |A Turing machine.
data TM state symbol = D (DTM state symbol) | N (NTM state symbol)

-- |Lift a DTM to a generic TM.
liftDtm :: DTM state symbol -> TM state symbol
liftDtm = D

-- |Lift a NTM to a generic TM.
liftNtm :: NTM state symbol -> TM state symbol
liftNtm = N

-- |Get the underlying DTM or NTM from a generic TM.
dtmOrNtm :: TM state symbol -> Either (DTM state symbol) (NTM state symbol)
dtmOrNtm (D m) = Left m
dtmOrNtm (N m) = Right m

instance (Ord state, Ord symbol) => Steppable () (TM state symbol) where
  step s (D m) = D <$> step s m
  step s (N m) = N <$> step s m

instance PartialDecider (TM state symbol) where
  partialDecide (D m) = partialDecide m
  partialDecide (N m) = partialDecide m

instance (Ord state, Ord symbol) => Accepter symbol (TM state symbol) where
  accepts = undefined
