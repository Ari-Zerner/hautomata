{-# LANGUAGE MultiParamTypeClasses, FunctionalDependencies #-}

module Automata.Automaton where

class Steppable input a | a -> input where
  -- ^Take a step with the given input if possible.
  step :: input -> a -> Maybe a

data Decision = Reject | Accept
  deriving (Eq, Ord, Read, Show)

-- |Accept if input is True, Reject if input is False.
acceptIff :: Bool -> Decision
acceptIff b = if b then Accept else Reject

isAccept :: Decision -> Bool
isAccept Reject = False
isAccept Accept = True

isReject :: Decision -> Bool
isReject = not . isAccept

data PartialDecision = Undecided | Decided Decision
  deriving (Eq, Ord, Read, Show)

-- |Converts Undecided and Decided to Nothing and Just, respectively.
maybeFromPartial :: PartialDecision -> Maybe Decision
maybeFromPartial Undecided   = Nothing
maybeFromPartial (Decided d) = Just d

class PartialDecider a where
  partialDecide :: a -> PartialDecision

class PartialDecider a => Decider a where
  decide :: a -> Decision

class Accepter input a | a -> input where
  -- ^Determine whether an automaton accepts a list of inputs.
  accepts :: a -> [input] -> Bool
