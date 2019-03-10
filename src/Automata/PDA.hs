{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, RecordWildCards, DuplicateRecordFields #-}

module Automata.PDA (
  AcceptCondition(..),
  DPDA,
  dpda,
  currentState,
  currentStack,
  dpdaTransitions,
  NPDA,
  npda,
  currentStatesAndStacks,
  npdaTransitions,
  PDA,
  liftDpda,
  liftNpda,
  dpdaOrNpda,
  acceptCondition
) where

import Automata.Automaton
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Data.Foldable (foldMap)
import Control.Monad

-- |The condition for a PDA to accept a string.
data AcceptCondition state = EmptyStack
                           | FinalState (Set.Set state)
  deriving (Eq)

meetsCondition :: Ord state => AcceptCondition state -> (state, [stackSymbol]) -> Bool
meetsCondition EmptyStack          = null . snd
meetsCondition (FinalState states) = flip Set.member states . fst

-- DPDA

-- |A deterministic pushdown automaton.
data DPDA state stackSymbol symbol =
  DPDA { condition :: AcceptCondition state
       , transitions :: Map.Map (state, stackSymbol, symbol) (state, [stackSymbol])
       , state :: state
       , stack :: [stackSymbol]
       }
  deriving (Eq)

-- |Create a new PDA.
dpda :: (Ord state, Ord stackSymbol, Ord symbol)
     => AcceptCondition state -- ^The accept condition
     -> [(state, [(stackSymbol, [(symbol, (state, [stackSymbol]))])])] -- ^The transition table
     -> state -- ^The initial state
     -> stackSymbol -- ^The initial stack symbol
     -> DPDA state stackSymbol symbol
dpda condition t state stackStart = DPDA{..}
  where stack = [stackStart]
        transitions = Map.fromList [ ((oldState, pop, input), action)
                                   | (oldState, t') <- t
                                   , (pop, t'') <- t'
                                   , (input, action) <- t''
                                   ]

-- |Get the current state of a DPDA.
currentState :: DPDA state stackSymbol symbol -> state
currentState = state

-- |Get the current stack (top-first) of a DPDA.
currentStack :: DPDA state stackSymbol symbol -> [stackSymbol]
currentStack = stack

-- |Get the transition table of a DPDA.
dpdaTransitions :: DPDA state stackSymbol symbol
                -> [(state, [(stackSymbol, [(symbol, (state, [stackSymbol]))])])]
dpdaTransitions = undefined

instance (Ord state, Ord stackSymbol, Ord symbol)
  => Steppable symbol (DPDA state stackSymbol symbol) where
  step input DPDA{..} =
    case stack of
      []           -> mzero
      (pop:stack') -> case transitions Map.!? (state, pop, input) of
                        Nothing            -> mzero
                        Just (state, push) -> return DPDA{stack = push ++ stack', ..}

instance (Ord state) => PartialDecider (DPDA state stackSymbol symbol) where
  partialDecide = Decided . decide

instance (Ord state) => Decider (DPDA state stackSymbol symbol) where
  decide DPDA{..} = acceptIff $ meetsCondition condition (state, stack)

-- NPDA

-- |A nondeterministic pushdown automaton.
data NPDA state stackSymbol symbol =
  NPDA { condition :: AcceptCondition state
       , transitions :: Map.Map (state, stackSymbol, symbol) (Set.Set (state, [stackSymbol]))
       , statesAndStacks :: Set.Set (state, [stackSymbol])
       }
 deriving (Eq)

-- |Create a new PDA.
npda :: (Ord state, Ord stackSymbol, Ord symbol)
     => AcceptCondition state -- ^The accept condition
     -> [(state, [(stackSymbol, [(symbol, [(state, [stackSymbol])])])])] -- ^The transition table
     -> state -- ^The initial state
     -> stackSymbol -- ^The initial stack symbol
     -> NPDA state stackSymbol symbol
npda condition t state stackStart = NPDA{..}
  where statesAndStacks = Set.singleton (state, [stackStart])
        transitions = Map.fromList [ ((oldState, pop, input), Set.fromList actions)
                                   | (oldState, t') <- t
                                   , (pop, t'') <- t'
                                   , (input, actions) <- t''
                                   ]

-- |Get the current states/stacks (top-first) of a NPDA.
currentStatesAndStacks :: NPDA state stackSymbol symbol -> [(state, [stackSymbol])]
currentStatesAndStacks = Set.toList . statesAndStacks

-- |Get the transition table of a NPDA.
npdaTransitions :: NPDA state stackSymbol symbol
                -> [(state, [(stackSymbol, [(symbol, [(state, [stackSymbol])])])])]
npdaTransitions = undefined

instance (Ord state, Ord stackSymbol, Ord symbol)
  => Steppable symbol (NPDA state stackSymbol symbol) where
  step input NPDA{..} =
    if Set.null newStatesAndStacks
      then mzero
      else return $ NPDA{statesAndStacks = newStatesAndStacks, ..}
    where newStatesAndStacks = foldMap aux statesAndStacks
          aux (state, stack) =
            case stack of
              []           -> Set.empty
              (pop:stack') -> case transitions Map.!? (state, pop, input) of
                                Nothing      -> Set.empty
                                Just actions -> Set.map (fmap (++ stack')) actions

instance (Ord state) => PartialDecider (NPDA state stackSymbol symbol) where
  partialDecide = Decided . decide

instance (Ord state) => Decider (NPDA state stackSymbol symbol) where
  decide NPDA{..} = acceptIff $ any (meetsCondition condition) $ Set.toList statesAndStacks

-- PDA

-- |A pushdown automaton.
data PDA state stackSymbol symbol = D (DPDA state stackSymbol symbol)
                                  | N (NPDA state stackSymbol symbol)

-- |Lift a DPDA to a generic PDA.
liftDpda :: DPDA state stackSymbol symbol -> PDA state stackSymbol symbol
liftDpda = D

-- |Lift a NPDA to a generic PDA.
liftNpda :: NPDA state stackSymbol symbol -> PDA state stackSymbol symbol
liftNpda = N

-- |Get the underlying DPDA or NPDA from a generic PDA.
dpdaOrNpda :: PDA state stackSymbol symbol
           -> Either (DPDA state stackSymbol symbol) (NPDA state stackSymbol symbol)
dpdaOrNpda (D m) = Left m
dpdaOrNpda (N m) = Right m

-- |Get the accept condition of a PDA.
acceptCondition :: PDA state stackSymbol symbol -> AcceptCondition state
acceptCondition (D DPDA{..}) = condition
acceptCondition (N NPDA{..}) = condition

instance (Ord state, Ord stackSymbol, Ord symbol)
  => Steppable symbol (PDA state stackSymbol symbol) where
  step s (D m) = D <$> step s m
  step s (N m) = N <$> step s m

instance (Ord state) => PartialDecider (PDA state stackSymbol symbol) where
  partialDecide (D m) = partialDecide m
  partialDecide (N m) = partialDecide m

instance (Ord state) => Decider (PDA state stackSymbol symbol) where
  decide (D m) = decide m
  decide (N m) = decide m

instance (Ord state, Ord stackSymbol, Ord symbol)
  => Accepter symbol (PDA state stackSymbol symbol) where
  accepts m input = maybe False (isAccept . decide) $ foldM (flip step) m input
