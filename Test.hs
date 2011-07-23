{-# LANGUAGE TemplateHaskell #-}

module Test where

import Language.Haskell.TH.SCCs



data E a = Nil | ECons a (Odd a)

data O a = OCons a (E a)

type Odd = O

data X = X (E Int)

printQ (Just "E: ") (binding_group ''E)
printQ (Just "O: ") (binding_group ''O)
printQ (Just "O!: ") (scc ''O)
printQ (Just "Odd: ") (binding_group ''Odd)
printQ (Just "X: ") (binding_group ''X)


printQ (Just "E/Xs: ") (binding_groups [''E, ''X])
printQ (Just "E/X: ") (sccs [''E, ''X])

printQ (Just "String: ") (binding_groups [''String])
printQ (Just "String!: ") (scc ''String)
printQ (Just "String!s: ") (sccs [''String])
printQ (Just "String/Char: ") (binding_groups [''String, ''Char])
printQ (Just "String/Char!s: ") (sccs [''String, ''Char])
