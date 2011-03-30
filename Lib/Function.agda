module Lib.Function where

flip : {A B C : Set} → (A → B → C) → B → A → C
flip f b a = f a b
