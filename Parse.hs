module Parse (
  ParseError(..),
  parseFull,
  parseExpr,
  parseDefns,
  showExpr,
  showExprNames
  ) where

  import List
  import Char

  import Ast
  import Failable

  data ParseError = PEOr [ParseError]
                  | PEUnexpected String
                  | PEExpected String String

  parseFull
    :: (String -> Failable ParseError (a,String))
    -> String
    -> Failable ParseError a
  parseFull
    p
    s
    = do (e,s') <- p s
         case (dropWhile isSpace s') of
           "" -> Succeed e
           _ -> Fail $ PEUnexpected s'

  parseExpr
    :: String
    -> Failable ParseError Expression
  parseExpr
    = parseFull $ pExpr []

  --NOTE the bool is true if the defn is transparent
  parseDefns
    :: String
    -> Failable ParseError [Definition]
  parseDefns
    s
    = sequence
        (map
          (parseFull pDefn . unlines) 
          (breakDefs (dropWhile (all isSpace) (lines s))))
      
  breakDefs
    :: [String]
    -> [[String]]
  breakDefs
    ss
    = case ss of
        []
          -> []
        (s:ss')
          -> let (d,rest) = span notNewDef ss'
             in (s:d) : breakDefs rest
  
  notNewDef
    :: String
    -> Bool
  notNewDef
    s
    = case s of
        [] -> True
        (c:_) -> isSpace c

  --NOTE does not deal with leading spaces, because parseDefns requires it
  --NOTE the bool is true if the defn is transparent
  pDefn
    :: String
    -> Failable ParseError (Definition,String)
  pDefn
    s0
    = do (n,s1) <- pWord s0
         (te,s2) <- pExpr [] s1
         case dropWhile isSpace s2 of
           ('-':'-':'-':'-':s3)
             -> do (be,s4) <- pExpr [] s3
                   Succeed (Definition n te be,s4)
           _ -> Fail $ PEExpected "line of 4 hyphens" (dropWhile isSpace s2)

  pExpr
    :: [String]
    -> String
    -> Failable ParseError (Expression,String)
  pExpr
    vars
    s
    = do (es,s') <- pAtoms vars s
         case es of
           []
             -> Fail $ PEExpected "expression" s
           _ -> Succeed $ (foldl1 ExprApp es,s')

  pAtoms
    :: [String]
    -> String
    -> Failable ParseError ([Expression],String)
  pAtoms
    vars
    s
    = do (e,s') <- failMap PEOr $ oneOf (map (($s).($vars)) [pNameContext,pLam,pParenExpr,pForAll,pExists,pPair,pSplit,const pNat,const pZero,pSucc,pInd,const pUniv,pByDefn,const pNotDone])
         mightFail
           (\err -> Succeed ([e],s'))
           (\(es,s'') -> Succeed ((e:es),s''))
           (pAtoms vars s')

  pNameContext
    :: [String]
    -> String
    -> Failable ParseError (Expression,String)
  pNameContext
    vars
    s
    = do (w,s') <- pWord s
         maybe
           (Succeed $ (ExprName w,s'))
           (\v -> Succeed $ (ExprVar v,s'))
           (elemIndex w vars)

  --NOTE consumes a lexeme, so drops leading spaces
  pWord
    :: String
    -> Failable ParseError (String,String)
  pWord
    s
    = case (span (flip elem (['a'..'z']++['A'..'Z']++['0'..'9']++"'_?")) (dropWhile isSpace s)) of
        ("",_)
          -> Fail $ PEExpected "word" (dropWhile isSpace s)
        (w,s')
          -> Succeed (w,s')

  --NOTE consumes a lexeme, so drops leading spaces
  pLam
    :: [String]
    -> String
    -> Failable ParseError (Expression,String)
  pLam
    vars
    s0
    = case dropWhile isSpace s0 of
        ('\\':'(':s1)
          -> do (v,s2) <- pWord s1
                case dropWhile isSpace s2 of
                  (':':s3)
                    -> do (te,s4) <- pExpr vars s3
                          case dropWhile isSpace s4 of
                            (')':s5)
                              -> do (be,s6) <- pExpr (v:vars) s5
                                    Succeed (ExprLam v te be,s6)
                            _ -> Fail $ PEExpected "right parenthesis" (dropWhile isSpace s4)
                  _ -> Fail $ PEExpected "colon" (dropWhile isSpace s2)
        _ -> Fail $ PEExpected "lambda" (dropWhile isSpace s0)

  --NOTE consumes a lexeme, so drops leading spaces
  pSplit
    :: [String]
    -> String
    -> Failable ParseError (Expression,String)
  pSplit
    vars
    s0
    = case dropWhile isSpace s0 of
        ('\\':s1)
          -> do (se,s2) <- pExpr vars s1
                case dropWhile isSpace s2 of
                  ('(':s3)
                    -> do (vl,s4) <- pWord s3
                          case dropWhile isSpace s4 of
                            (',':s5)
                              -> do (vr,s6) <- pWord s5
                                    case dropWhile isSpace s6 of
                                      (')':s7)
                                        -> do (be,s8) <- pExpr (vl:vr:vars) s7
                                              Succeed (ExprSplit vl vr be se,s8)
                                      _ -> Fail $ PEExpected "right parenthesis" (dropWhile isSpace s6)
                            _ -> Fail $ PEExpected "comma" (dropWhile isSpace s4)
                  _ -> Fail $ PEExpected "left parenthesis" (dropWhile isSpace s2)
        _ -> Fail $ PEExpected "lambda" (dropWhile isSpace s0)

  --NOTE consumes a lexeme, so drops leading spaces
  pPair
    :: [String]
    -> String
    -> Failable ParseError (Expression,String)
  pPair
    vars
    s0
    = case dropWhile isSpace s0 of
        ('(':s1)
          -> do (el,s2) <- pExpr vars s1
                case dropWhile isSpace s2 of
                  (',':s3)
                    -> do (er,s4) <- pExpr vars s3
                          case dropWhile isSpace s4 of
                            (')':s5)
                              -> Succeed (ExprPair el er,s5)
                            _ -> Fail $ PEExpected "right parenthesis" (dropWhile isSpace s4)
                  _ -> Fail $ PEExpected "comma" (dropWhile isSpace s2)
        _ -> Fail $ PEExpected "left parenthesis" (dropWhile isSpace s0)

  --NOTE consumes a lexeme, so drops leading spaces
  pParenExpr
    :: [String]
    -> String
    -> Failable ParseError (Expression,String)
  pParenExpr
    vars
    s
    = case dropWhile isSpace s of
        ('(':s')
          -> do (e,s'') <- pExpr vars s'
                case dropWhile isSpace s'' of
                  (')':s''')
                    -> Succeed (e,s''')
                  _ -> Fail $ PEExpected "right parenthesis" (dropWhile isSpace s'')
        _ -> Fail $ PEExpected "left parenthesis" (dropWhile isSpace s)

  --NOTE consumes a lexeme, so drops leading spaces
  pForAll
    :: [String]
    -> String
    -> Failable ParseError (Expression,String)
  pForAll
    vars
    s0
    = case dropWhile isSpace s0 of
        ('^':'(':s1)
          -> do (v,s2) <- pWord s1
                case dropWhile isSpace s2 of
                  (':':s3)
                    -> do (te,s4) <- pExpr vars s3
                          case dropWhile isSpace s4 of
                            (')':s5)
                              -> do (be,s6) <- pExpr (v:vars) s5
                                    Succeed (ExprAll v te be,s6)
                            _ -> Fail $ PEExpected "right parenthesis" (dropWhile isSpace s4)
                  _ -> Fail $ PEExpected "colon" (dropWhile isSpace s2)
        _ -> Fail $ PEExpected "forall" (dropWhile isSpace s0)

  --NOTE consumes a lexeme, so drops leading spaces
  pExists
    :: [String]
    -> String
    -> Failable ParseError (Expression,String)
  pExists
    vars
    s0
    = case dropWhile isSpace s0 of
        ('%':'(':s1)
          -> do (v,s2) <- pWord s1
                case dropWhile isSpace s2 of
                  (':':s3)
                    -> do (te,s4) <- pExpr vars s3
                          case dropWhile isSpace s4 of
                            (')':s5)
                              -> do (be,s6) <- pExpr (v:vars) s5
                                    Succeed (ExprExists v te be,s6)
                            _ -> Fail $ PEExpected "right parenthesis" (dropWhile isSpace s4)
                  _ -> Fail $ PEExpected "colon" (dropWhile isSpace s2)
        _ -> Fail $ PEExpected "exists" (dropWhile isSpace s0)

  --TODO make the nat things unparseable, and put them in the initial context as transparent definitions
  --TODO still need to be able to showExpr them even in that case, but shouldn't be a problem

  --NOTE consumes a lexeme, so drops leading spaces
  pNat
    :: String
    -> Failable ParseError (Expression,String)
  pNat
    s0
    = case dropWhile isSpace s0 of
        ('#':s1)
          -> Succeed (ExprNat,s1)
        _ -> Fail $ PEExpected "number sign" (dropWhile isSpace s0)

  --NOTE consumes a lexeme, so drops leading spaces
  pZero
    :: String
    -> Failable ParseError (Expression,String)
  pZero
    s0
    = case dropWhile isSpace s0 of
        ('@':s1)
          -> Succeed (ExprZero,s1)
        _ -> Fail $ PEExpected "at sign" (dropWhile isSpace s0)

  --NOTE consumes a lexeme, so drops leading spaces
  pSucc
    :: [String]
    -> String
    -> Failable ParseError (Expression,String)
  pSucc
    vars
    s0
    = case dropWhile isSpace s0 of
        ('`':s1)
          -> do (e,s2) <- pExpr vars s1
                Succeed (ExprSucc e,s2)
        _ -> Fail $ PEExpected "back tick" (dropWhile isSpace s0)

  --NOTE consumes a lexeme, so drops leading spaces
  pInd
    :: [String]
    -> String
    -> Failable ParseError (Expression,String)
  pInd
    vars
    s0
    = case dropWhile isSpace s0 of
        ('\\':'#':'(':s1)
          -> do (en,s2) <- pExpr vars s1
                case dropWhile isSpace s2 of
                  (')':s3)
                    -> do (vm,s4) <- pWord s3
                          case dropWhile isSpace s4 of
                            ('-':s5)
                              -> do (em,s6) <- pExpr (vm:vars) s5
                                    case dropWhile isSpace s6 of
                                      ('-':'-':s7)
                                        -> do (ez,s8) <- pExpr vars s7
                                              case dropWhile isSpace s8 of
                                                ('-':'-':s9)
                                                  -> do (vp,s10) <- pWord s9
                                                        case dropWhile isSpace s10 of
                                                          (',':s11)
                                                            -> do (vr,s12) <- pWord s11
                                                                  case dropWhile isSpace s12 of
                                                                    ('-':s13)
                                                                      -> do (es,s14) <- pExpr (vr:vp:vars) s13
                                                                            Succeed (ExprInd vm em ez vp vr es en,s14)
                                                                    _ -> Fail $ PEExpected "dash" (dropWhile isSpace s12)
                                                          _ -> Fail $ PEExpected "comma" (dropWhile isSpace s10)
                                                _ -> Fail $ PEExpected "double dash" (dropWhile isSpace s8)
                                      _ -> Fail $ PEExpected "double dash" (dropWhile isSpace s6)
                            _ -> Fail $ PEExpected "dash" (dropWhile isSpace s4)
                  _ -> Fail $ PEExpected "right parenthesis" (dropWhile isSpace s2)
        _ -> Fail $ PEExpected "backslash" (dropWhile isSpace s0)

  --NOTE consumes a lexeme, so drops leading spaces
  pUniv
    :: String
    -> Failable ParseError (Expression,String)
  pUniv
    s
    = case dropWhile isSpace s of
        ('*':s')
          -> let (quotes,s'') = span (=='\'') s'
             in Succeed (ExprUniv (length quotes),s'')
        _
          -> Fail $ PEExpected "universe" (dropWhile isSpace s)

  --NOTE consumes a lexeme, so drops leading spaces
  pByDefn
    :: [String]
    -> String
    -> Failable ParseError (Expression,String)
  pByDefn
    vars
    s0
    = case dropWhile isSpace s0 of
        ('!':s1)
          -> do (n,s2) <- pWord s1
                case dropWhile isSpace s2 of
                  ('(':s3)
                    -> do (v,s4) <- pWord s3
                          case dropWhile isSpace s4 of
                            ('-':s5)
                              -> do (m,s6) <- pExpr (v:vars) s5
                                    case dropWhile isSpace s6 of
                                      (')':s7)
                                        -> do (e,s8) <- pExpr vars s7
                                              Succeed (ExprDefn n v m e,s8)
                                      _ -> Fail $ PEExpected "right parenthesis" (dropWhile isSpace s6)
                            _ -> Fail $ PEExpected "dash" (dropWhile isSpace s4)
                  _ -> Fail $ PEExpected "left parenthesis" (dropWhile isSpace s2)
        _ -> Fail $ PEExpected "exclamation mark" (dropWhile isSpace s0)

  --NOTE consumes a lexeme, so drops leading spaces
  pNotDone
    :: String
    -> Failable ParseError (Expression,String)
  pNotDone
    s0
    = case dropWhile isSpace s0 of
        ('[':s1)
          -> do (w,s2) <- pWord s1
                let (str,s3) = span (/=']') s2
                case s3 of
                  (']':s4)
                    -> Succeed (ExprNotDone w str,s4)
                  _ -> Fail $ PEExpected "right bracket" s3
        _ -> Fail $ PEExpected "left bracket" (dropWhile isSpace s0)

  showExpr
    :: Expression
    -> String
  showExpr
    expr
    = showExprNames [] expr

  showExprNames
    :: [String]
    -> Expression
    -> String
  showExprNames
    names
    expr
    = showExpr' (names ++ (map ("_v_"++) (map show [0..]))) expr
    where
      showExpr'
        :: [String]
        -> Expression
        -> String
      showExpr'
        vars
        expr
        = case expr of
            (ExprName n) -> n
            (ExprVar v) -> (vars !! v) ++ "[" ++ show v ++ "]"
            (ExprAll v t b) -> "^(" ++ v ++ ":" ++ showExpr' vars t ++ ") (" ++ showExpr' (v:vars) b ++ ")"
            (ExprLam v t b) -> "\\(" ++ v ++ ":" ++ showExpr' vars t ++ ") (" ++ showExpr' (v:vars) b ++ ")"
            (ExprApp f x) -> "(" ++ showExpr' vars f ++ ") (" ++ showExpr' vars x ++ ")"
            (ExprExists v t b) -> "%(" ++ v ++ ":" ++ showExpr' vars t ++ ") (" ++ showExpr' (v:vars) b ++ ")"
            (ExprPair l r) -> "(" ++ showExpr' vars l ++ "," ++ showExpr' vars r ++ ")"
            (ExprSplit vl vr be se) -> "\\" ++ showExpr' vars se ++ "(" ++ vl ++ "," ++ vr ++ ") (" ++ showExpr' (vr:vl:vars) be ++ ")"
            (ExprNat) -> "#"
            (ExprZero) -> "@"
            (ExprSucc e) -> "`(" ++ showExpr' vars e ++ ")"
            (ExprInd vm em ez vp vr es en)
              -> "\\#(" ++ showExpr' vars en ++ ")"
                 ++ vm ++ "-" ++ showExpr' (vm:vars) em
                 ++ "--(" ++ showExpr' vars ez
                 ++ ")--" ++ vp ++ "," ++ vr ++ "-(" ++ showExpr' (vr:vp:vars) es ++ ")"
            (ExprUniv n) -> "*" ++ take n (repeat '\'')
            (ExprDefn n v m e) -> "!" ++ n ++ "(" ++ v ++ "-" ++ showExpr' (v:vars) m ++ ") (" ++ showExpr' vars e ++ ")"
            (ExprNotDone n s) -> "[" ++ n ++ " " ++ s ++ "]"
