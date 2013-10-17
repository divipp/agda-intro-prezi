{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

import Prelude hiding ((+))

import Test.QuickCheck

import Test.SmallCheck
import Test.SmallCheck.Series


----- live coding starts here

data Nat :: * where
  Zero :: Nat
  Suc :: Nat -> Nat
  deriving Show

instance Eq Nat where
   Zero == Zero   = True
   Suc a == Suc b  = a == b
   _ == _ = False


one, two, three, four :: Nat
one = Suc Zero
two = Suc one
three = Suc two
four = Suc three

(+) :: Nat -> Nat -> Nat
Zero + a = a
Suc a + b = Suc (a + b)

assoc_unit :: Bool
assoc_unit =   one + (one + two)  == (one + one) + two

assoc_prop :: Nat -> Nat -> Nat -> Bool
assoc_prop a b c  =   a + (b + c)  == (a + b)   + c

assoc_qc :: IO ()   -- quickCheck
assoc_qc = quickCheck assoc_prop

instance Arbitrary Nat where
    arbitrary = oneof [return Zero, fmap Suc arbitrary]

arbitrary_test :: IO ()
arbitrary_test = sample (arbitrary :: Gen Nat)

assoc_sc :: IO ()   -- smallCheck
assoc_sc = smallCheck 5 assoc_prop

instance Monad m => Serial m Nat where
    series = cons0 Zero \/ cons1 Suc



