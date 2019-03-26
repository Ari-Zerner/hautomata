{-# OPTIONS_GHC -F -pgmF htfpp #-}

module Main where

import Test.Framework

import {-@ HTF_TESTS @-} Test.Automata.FSA
import {-@ HTF_TESTS @-} Test.Automata.PDA

main :: IO ()
main = htfMain htf_importedTests
