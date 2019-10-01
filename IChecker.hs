import TypeCheck
import Ast
import Parse
import Failable

import IO
import List
import Monad

main = repl emptyContext

prompt
  :: String
  -> IO String
prompt
  str
  = do putStr ("\n" ++ str)
       hFlush stdout
       getLine

repl
  :: Context
  -> IO ()
repl
  context
  = do command <- prompt "command>"
       case command of
         "quit"
           -> return ()
         "prove"
           -> getDefn (\c n _ t -> addGlobalType c n t) context >>= repl
         "alias"
           -> getDefn (\c n v t -> addTransparentValue (addGlobalType c n t) n v) context >>= repl
         "type"
           -> do val <- prompt "="
                 mightFail (const $ return ()) (\e -> putStrLn (showExpr e) >> putStrLn (show e)) (parseExpr val)
                 mightFail
                   (\e -> putStrLn (showError e))
                   (\(valExpr,typeExpr)
                     -> putStrLn (showExpr typeExpr))
                   (do valExpr <- failMap Left $ parseExpr val
                       typeExpr <- failMap Right $ typeGet context valExpr
                       return (valExpr,typeExpr))
                 repl context
         "help"
           -> putStrLn "commands are 'quit', 'prove', 'alias', 'type', 'help'"
              >>
              repl context
         _ -> putStrLn "no such command, try 'help'"
              >>
              repl context
  where
    getDefn
      :: (Context -> String -> Expression -> Expression -> Context)
      -> Context
      -> IO Context
    getDefn
      update
      context
      = do name <- prompt "name>"
           typ <- prompt (name ++ ":")
           mightFail (const $ return ()) (\e -> putStrLn (showExpr e) >> putStrLn (show e)) (parseExpr typ)
           mightFail (\e -> putStrLn (showError e) >> return context) (doVal name) (failMap Left $ parseExpr typ)
      where
        doVal
          :: String
          -> Expression
          -> IO Context
        doVal
          name
          typeExpr
          = do val <- prompt (name ++ "=")
               if val == ""
                 then return context
                 else
                   do mightFail (const $ return ()) (\e -> putStrLn (showExpr e) >> putStrLn (show e)) (parseExpr val)
                      mightFail
                        (\e -> putStrLn (showError e) >> doVal name typeExpr)
                        (\(valExpr,fills)
                         -> case fills of 
                              [] -> return $ update context name valExpr typeExpr
                              _ -> putStr (unlines (map (\(n,t) -> "need " ++ n ++ ":" ++ showExpr t) fills))
                                   >>
                                   doVal name typeExpr)
                        (do valExpr <- failMap Left $ parseExpr val
                            fills <- failMap Right $ typeFill context valExpr typeExpr
                            return (valExpr,fills))

    showError
      :: Either ParseError TypeError
      -> String
    showError
      err
      = case err of
          (Left (PEOr es))
            -> concat (intersperse "\nor\n" (map (showError . Left) es))
          (Left (PEExpected name cont))
            -> "expected " ++ name ++ " at\n" ++ take 80 cont ++ "..."
          (Left (PEUnexpected name cont))
            -> "unexpected things after " ++ name ++ " at\n" ++ take 80 cont ++ "..."
          (Right (TEExpected e te))
            -> showExpr e ++ " must be of type " ++ showExpr te
          (Right (TENotFunction f t))
            -> showExpr f ++ " needs to be a function to be applied, but it is of type " ++ showExpr t
          (Right (TENotDefined name))
            -> name ++ " is not defined"
          (Right (TENoTypeForUniv))
            -> "the universe does not have a type"
          (Right (TEUnableToType e))
            -> showExpr e ++ " can't be given a type"
          (Right TENotDone)
            -> "not done"
          (Right (TENotType e))
            -> showExpr e ++ " is not a type"
