{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances #-}

module Automata.FSA (
  DFA,
  dfa,
  currentState,
  dfaTransitions,
  NFA,
  nfa,
  currentStates,
  nfaTransitions,
  FSA,
  liftDfa,
  liftNfa,
  dfaOrNfa,
  acceptingStates,
  accepts
) where

import Automata.Automaton
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map
import Data.Maybe
import Data.Foldable (fold)
import Control.Monad

--- DFA

-- |A deterministic finite state automaton.
data DFA state symbol = DFA
  (Set.Set state) -- ^accepting states
  (Map.Map (state, symbol) state) -- ^transitions
  state -- ^current state
  deriving (Eq, Show) -- TODO: remove Show in production

-- |Create a new DFA.
dfa :: (Ord state, Ord symbol)
    => [state] -- ^The accepting states
    -> [(state,  [(symbol, state)])] -- ^For each state, the list of transitions from that state
    -> state -- ^The initial state
    -> DFA state symbol
dfa accepting transitions = DFA (Set.fromList accepting) transitionMap
  where transitionMap = Map.fromList [ ((state, symbol), newState)
                                     | (state, stateTransitions) <- transitions
                                     , (symbol, newState) <- stateTransitions
                                     ]

-- |Get the current state of a DFA.
currentState :: DFA state symbol -> state
currentState (DFA _ _ current) = current

-- |Get the transitions of a DFA, grouped by source state.
dfaTransitions :: (Ord state, Ord symbol) => DFA state symbol -> [(state,  [(symbol, state)])]
dfaTransitions (DFA _ trans _) = Map.toList $ Map.toList <$> Map.foldrWithKey aux Map.empty trans
  where aux (q1, s) q2 = Map.insertWith Map.union q1 (Map.singleton s q2)

instance (Ord state, Ord symbol) => Steppable symbol (DFA state symbol) where
  step s (DFA accepting trans current) = DFA accepting trans <$> trans Map.!? (current, s)

instance (Ord state) => PartialDecider (DFA state symbol) where
  partialDecide = Decided . decide

instance (Ord state) => Decider (DFA state symbol) where
  decide (DFA accepting _ current) = acceptIff $ Set.member current accepting

--- NFA

-- |A nondeterministic finite state automaton.
data NFA state symbol = NFA
  (Set.Set state) -- ^accepting states
  (Map.Map (state, symbol) (Set.Set state)) -- ^symbol transitions
  (Map.Map state (Set.Set state)) -- ^epsilon transitions
  (Set.Set state) -- ^current states
  deriving (Eq, Show) -- TODO: remove Show in production

-- |See Data.Maybe.mapMaybe.
setMapMaybe :: (Ord a, Ord b) => (a -> Maybe b) -> Set.Set a -> Set.Set b
setMapMaybe f = foldr aux Set.empty
  where aux x s = maybe s (`Set.insert` s) $ f x

-- |Find all states reachable from current by zero or more epsilon transitions.
epsilonClosure :: Ord state => NFA state symbol -> NFA state symbol
epsilonClosure (NFA accepting symTrans eTrans current) = NFA accepting symTrans eTrans $ bfs current current
  where bfs seen frontier = let frontier' = fold (setMapMaybe (eTrans Map.!?) frontier) Set.\\ seen
                            in if Set.null frontier' then seen else bfs (seen <> frontier') frontier'

-- |Create a new NFA.
nfa :: (Ord state, Ord symbol)
    => [state] -- ^The accepting states
    -> [(state,  ([(symbol, [state])], [state]))] -- ^For each state, the list of symbol transitions and the list of epsilon transitions from that state
    -> state -- ^The initial state
    -> NFA state symbol
nfa accepting transitions initial = epsilonClosure $
  NFA (Set.fromList accepting) symTransitions eTransitions (Set.singleton initial)
  where symTransitions = Map.fromList [ ((state, symbol), Set.fromList newStates)
                                      | (state, stateTransitions) <- transitions
                                      , (symbol, newStates) <- fst stateTransitions
                                      ]
        eTransitions   = Map.fromList [ (state, Set.fromList (snd stateTransitions))
                                      | (state, stateTransitions) <- transitions
                                      ]

-- |Get the current states of a NFA.
currentStates :: Ord state => NFA state symbol -> [state]
currentStates (NFA _ _ _ current) = Set.toList current

-- |Get the symbol and epsilon transitions of a NFA, grouped by source state.
nfaTransitions :: (Ord state, Ord symbol) => NFA state symbol -> [(state,  ([(symbol, [state])], [state]))]
nfaTransitions (NFA _ symTrans eTrans _) = map aux states
  where states        = Set.toList $ Set.map fst (Map.keysSet symTrans) <> Map.keysSet eTrans
        aux state     = (state, (listSym state, listE state))
        listSym state = [ (symbol, Set.toList newStates)
                        | ((state', symbol), newStates) <- Map.toList symTrans
                        , state' == state
                        ]
        listE state   = Set.toList $ Map.findWithDefault Set.empty state eTrans

instance (Ord state, Ord symbol) => Steppable symbol (NFA state symbol) where
  step s (NFA accepting symTrans eTrans current) =
    if Set.null newStates
      then mzero
      else return $ epsilonClosure $ NFA accepting symTrans eTrans newStates
    where newStates = fold [Map.findWithDefault Set.empty (state, s) symTrans | state <- Set.toList current]

instance (Ord state) => PartialDecider (NFA state symbol) where
  partialDecide = Decided . decide

instance (Ord state) => Decider (NFA state symbol) where
  decide (NFA accepting _ _ current) = acceptIff $ not $ current `Set.disjoint` accepting

--- FSA

-- |A finite state automaton.
data FSA state symbol = D (DFA state symbol) | N (NFA state symbol)
  deriving (Eq)

-- |Lift a DFA to a generic FSA.
liftDfa :: DFA state symbol -> FSA state symbol
liftDfa = D

-- |Lift a NFA to a generic FSA.
liftNfa :: NFA state symbol -> FSA state symbol
liftNfa = N

dfaOrNfa :: FSA state symbol -> Either (DFA state symbol) (NFA state symbol)
dfaOrNfa (D m) = Left m
dfaOrNfa (N m) = Right m

-- |Get the accepting states of a FSA.
acceptingStates :: Ord state => FSA state symbol -> [state]
acceptingStates (D (DFA accepting _ _))   = Set.toList accepting
acceptingStates (N (NFA accepting _ _ _)) = Set.toList accepting

instance (Ord state, Ord symbol) => Steppable symbol (FSA state symbol) where
  step s (D m) = D <$> step s m
  step s (N m) = N <$> step s m

instance (Ord state) => PartialDecider (FSA state symbol) where
  partialDecide (D m) = partialDecide m
  partialDecide (N m) = partialDecide m

instance (Ord state) => Decider (FSA state symbol) where
  decide (D m) = decide m
  decide (N m) = decide m

-- |Determine whether a FSA accepts a list of symbols.
accepts :: (Ord state, Ord symbol) => FSA state symbol -> [symbol] -> Bool
accepts m input = maybe False (isAccept . decide) $ foldM (flip step) m input
