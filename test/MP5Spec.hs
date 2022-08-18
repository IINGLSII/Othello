{-# LANGUAGE ImplicitParams #-}

module MP5Spec (spec) where

import Test.Hspec
import Test.HUnit
import Test.HUnit.Approx
import Test.QuickCheck
import Control.Exception
import Othello

spec :: Spec
spec = do
  describe "Search" $ do
    it "Works as expected" $ do
      pendingWith "Your tests here!"
  describe "Minimax" $ do
    it "Works as expected" $ do
      pendingWith "Your tests here!"
