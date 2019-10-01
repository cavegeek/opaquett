module Ast (
  Definition(Definition),
  Expression(ExprName,ExprVar,ExprApp,ExprAll,ExprLam,ExprExists,ExprPair,ExprSplit,ExprNat,ExprZero,ExprSucc,ExprInd,ExprUniv,ExprDefn,ExprNotDone),
  Name
  ) where

  data Definition = Definition Name Expression Expression

  data Expression = ExprName Name
                  | ExprVar Int
                  | ExprAll Name Expression Expression
                  | ExprLam Name Expression Expression
                  | ExprApp Expression Expression
                  | ExprExists Name Expression Expression
                  | ExprPair Expression Expression
                  | ExprSplit Name Name Expression Expression
                  | ExprNat
                  | ExprZero
                  | ExprSucc Expression
                  | ExprInd Name Expression Expression Name Name Expression Expression
                  | ExprUniv Int
                  | ExprDefn Name Name Expression Expression
                  | ExprNotDone Name String
                  deriving Show

  type Name = String
