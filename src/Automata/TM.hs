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
import qualified Data.InfList as Inf
import qualified Data.Map.Strict as Map
import qualified Data.Set as Set
import Data.Maybe

data TapeAction = MoveLeft | Stay | MoveRight
  deriving (Eq, Ord, Read, Show, Bounded, Enum)

-- |A Turing machine tape. Infinite in both directions.
data Tape symbol = Tape
  (Inf.InfList symbol) -- ^left of head
  symbol -- ^head
  (Inf.InfList symbol) -- ^right of head

-- |Get the symbol under the tape head.
currentSymbol :: Tape symbol -> symbol
currentSymbol (Tape _ current _) = current

-- |Change the symbol under the tape head.
writeSymbol :: symbol -> Tape symbol -> Tape symbol
writeSymbol s (Tape left current right) = Tape left s right

-- |Get the symbols to the left of the tape head, closest first.
leftSymbols :: Tape symbol -> [symbol]
leftSymbols (Tape left _ _) = Inf.toList left

-- |Get the symbols to the right of the tape head, closest first.
rightSymbols :: Tape symbol -> [symbol]
rightSymbols (Tape _ _ right) = Inf.toList right

-- |Generate a tape wherein every cell is blank.
blankTape :: symbol -> Tape symbol
blankTape s = Tape (Inf.repeat s) s (Inf.repeat s)

-- |Shift the tape head left.
moveLeft :: Tape symbol -> Tape symbol
moveLeft (Tape left current right) = Tape (Inf.tail left) (Inf.head left) (current Inf.::: right)

-- |Shift the tape head right.
moveRight :: Tape symbol -> Tape symbol
moveRight (Tape left current right) = Tape (current Inf.::: left) (Inf.head right) (Inf.tail right)

doTapeAction :: TapeAction -> Tape symbol -> Tape symbol
doTapeAction MoveLeft  = moveLeft
doTapeAction Stay      = id
doTapeAction MoveRight = moveRight

-- |Splice a list of symbols into the tape to the right of the head, then move right.
splice :: [symbol] -> Tape symbol -> Tape symbol
splice ss (Tape left current right) = moveRight $ Tape left current $ ss Inf.+++ right

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
dtm blank transitions start = DTM transitionMap (Right start) (blankTape blank)
  where transitionMap = Map.fromList [ ((state, symbol), action)
                                     | (state, stateTransitions) <- transitions
                                     , (symbol, action) <- stateTransitions
                                     ]

-- |Splice a list of symbols into the tape to the right of the head, then move right.
spliceIntoTape :: [symbol] -> DTM state symbol -> DTM state symbol
spliceIntoTape ss (DTM trans state tape) = DTM trans state $ splice ss tape

-- |Get the current state of a DTM.
currentState :: DTM state symbol -> Either Decision state
currentState (DTM _ state _) = state

-- |Get the current tape of a DTM.
currentTape :: DTM state symbol -> Tape symbol
currentTape (DTM _ _ tape) = tape

-- |Get the transitions of a DTM.
dtmTransitions :: (Ord state, Ord symbol)
               => DTM state symbol
               -> [(state, [(symbol, Either Decision (state, symbol, TapeAction))])]
dtmTransitions (DTM trans _ _) = Map.toList $ Map.toList <$> Map.foldrWithKey aux Map.empty trans
  where aux (q, s) action = Map.insertWith Map.union q (Map.singleton s action)

instance (Ord state, Ord symbol) => Steppable () (DTM state symbol) where
  step _ (DTM trans (Left  _    ) tape) = Nothing -- can't step after deciding
  step _ (DTM trans (Right state) tape) = return $
    let action = fromMaybe (Left Reject) $ trans Map.!? (state, currentSymbol tape)
        rightFst (x, y, z) = (Right x, y, z)
        (state', current', tapeAction) = case action of
          Left  d -> (Left d, currentSymbol tape, Stay)
          Right a -> rightFst a
        tape' = doTapeAction tapeAction $ writeSymbol current' tape
    in DTM trans state' tape'

instance PartialDecider (DTM state symbol) where
  partialDecide (DTM _ (Right _) _) = Undecided
  partialDecide (DTM _ (Left  d) _) = Decided d

instance (Ord state, Ord symbol) => Accepter symbol (DTM state symbol) where
  accepts = accepts . liftDtm

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
  accepts m input = let (failure, m') = runSteppable (spliceInto m input) $ repeat ()
                    in partialDecide m' == Decided Accept
    where spliceInto (D m) = liftDtm . flip spliceIntoTape m
          spliceInto (N m) = liftNtm . flip spliceIntoTapes m
