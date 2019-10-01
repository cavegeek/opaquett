import TypeCheck
import Ast
import Parse
import Failable

import System
import List
import Monad
import Control.Monad.Trans

indent
  :: String
  -> String
indent
  str
  = unlines (map ("\t"++) (lines str))

main
  :: IO ()
main
  = do [fname] <- getArgs
       text <- readFile fname
       mightFail
         (putStrLn . showParseError)
         (\prog -> putStrLn $ typeResults prog)
         (parseDefns text)
  where
    typeResults
      :: [Definition]
      -> String
    typeResults
      prog
      = foldr
          (\(Definition n te be) rest cont
            -> let r = typeCheck cont be te
                   newContext = addGlobal cont n te be
               in processType
                    r
                    (\e -> "ERROR: " ++ n ++ "\n" ++ showTypeError e ++ "\n" ++ rest newContext)
                    (\cs _ -> (case cs of
                                 [] -> ""
                                 _ -> n ++ "\n" ++ (unlines $ map showConstraint cs) ++ "\n")
                               ++
                               rest newContext))
          (const "")
          prog
          emptyContext

    showConstraint
      :: (String,Context,Constraint)
      -> String
    showConstraint
      (n,c,constraint)
      = case constraint of
          (CEqual e)
            -> n ++ " = " ++ showExprNames (getLocalNames c) e
          (CSubtype e)
            -> n ++ " < " ++ showExprNames (getLocalNames c) e
          (CSupertype e)
            -> n ++ " > " ++ showExprNames (getLocalNames c) e
          (COfType e)
            -> n ++ " : " ++ showExprNames (getLocalNames c) e
          (CIsUniv)
            -> n ++ " is a universe"
        ++ "\n" ++
        indent (showContext c)

showParseError
  :: ParseError
  -> String
showParseError
  err
  = case err of
      (PEOr es)
        -> concat (intersperse "\nor\n" (map showParseError es))
      (PEExpected name cont)
        -> "expected " ++ name ++ " at\n" ++ take 80 cont ++ "..."
      (PEUnexpected cont)
        -> "unexpected things at\n" ++ take 80 cont ++ "..."

showTypeError
  :: TypeError
  -> String
showTypeError
  err
  = case err of
      (TEExpected c e te te')
        -> showExprNames (getLocalNames c) te ++ " is not a subtype of " ++ showExprNames (getLocalNames c) te' ++ " needed while examining " ++ showExprNames (getLocalNames c) e
           ++ "\n" ++ indent (showContext c)
      (TENotFunction c f t)
        -> showExprNames (getLocalNames c) f ++ " needs to be a function to be applied, but it is of type " ++ showExprNames (getLocalNames c) t
           ++ "\n" ++ indent (showContext c)
      (TENotPair c p t)
        -> showExprNames (getLocalNames c) p ++ " needs to be a pair to be split, but it is of type " ++ showExprNames (getLocalNames c) t
           ++ "\n" ++ indent (showContext c)
      (TENotDefined name)
        -> name ++ " is not defined"
      (TEUnableToType c e)
        -> showExprNames (getLocalNames c) e ++ " can't be given a type"
           ++ "\n" ++ indent (showContext c)
      TENotDone
        -> "not done"
      (TENotType c e)
        -> showExprNames (getLocalNames c) e ++ " is not a type"
           ++ "\n" ++ indent (showContext c)
