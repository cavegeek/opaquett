module TypeCheck (
  TypeError(..),
  typeGet,
  typeCheck,
  Fill,
  Constraint(..),
  FilledTypeResult,
  processType,
  typeFill,
  Context,
  emptyContext,
  addGlobal,
  getLocalNames,
  showContext
  ) where

  import Monad
  import Control.Monad.Instances
  import Control.Monad.Trans
  import Control.Monad.State
  import List

--  import Failable
  import Ast
  import Parse (showExpr,showExprNames)

  data Context = Context [(String,(Expression,Expression))] [Expression] [String]

  emptyContext
    :: Context
  emptyContext
    = Context [] [] []

  lookupGlobalType
    :: Context
    -> String
    -> Maybe Expression
  lookupGlobalType
    (Context globs locs lnames)
    name
    = liftM fst $ lookup name globs

  lookupGlobalValue
    :: Context
    -> String
    -> Maybe Expression
  lookupGlobalValue
    (Context globs locs lnames)
    name
    = liftM snd $ lookup name globs

  lookupLocalType
    :: Context
    -> Int
    -> Expression
  lookupLocalType
    (Context globs locs lnames)
    n
    = locs !! n

  addGlobal
    :: Context
    -> String
    -> Expression
    -> Expression
    -> Context
  addGlobal
    (Context globs locs lnames)
    name
    texpr
    expr
    = Context ((name,(texpr,expr)):globs) locs lnames

  addLocal
    :: Context
    -> String
    -> Expression
    -> Context
  addLocal
    (Context globs locs lnames)
    name
    expr
    = Context globs (map deeper (expr : locs)) (name:lnames)

  getLocalNames
    :: Context
    -> [String]
  getLocalNames
    (Context globs locs lnames)
    = lnames

  showContext
    :: Context
    -> String
  showContext
    (Context globs locs lnames)
    = unlines (map (\(n,(te,be)) -> n ++ ": " ++ showExpr te ++ " = " ++ showExpr be) globs)
      ++
      unlines (zipWith (\n te -> n ++ ": " ++ showExprNames lnames te) lnames locs)

  data TypeError = TEExpected Context Expression Expression Expression
                 | TENotFunction Context Expression Expression
                 | TENotPair Context Expression Expression
                 | TENotDefined String
                 | TEUnableToType Context Expression
                 | TENotDone
                 | TENotType Context Expression

  simplify
    :: Expression
    -> Expression
  simplify
    expr
    = case expr of
        (ExprName n)
          -> ExprName n
        (ExprVar num)
          -> ExprVar num
        (ExprAll v t b)
          -> ExprAll v (simplify t) (simplify b)
        (ExprLam v t b)
          -> ExprLam v (simplify t) (simplify b)
        (ExprApp f x)
          -> case simplify f of
               (ExprLam _ t b)
                 -> simplify (substitute 0 b x)
               e -> ExprApp e (simplify x)
        (ExprExists v t b)
          -> ExprExists v (simplify t) (simplify b)
        (ExprPair l r)
          -> ExprPair (simplify l) (simplify r)
        (ExprSplit v0 v1 b s)
          -> case simplify s of
               (ExprPair l r)
                 -> simplify (substitute 0 (substitute 0 b l) r)
               e -> ExprSplit v0 v1 (simplify b) e
        (ExprNat)
          -> ExprNat
        (ExprZero)
          -> ExprZero
        (ExprSucc e)
          -> ExprSucc (simplify e)
        (ExprInd vm em ez vp vr es en)
          -> case simplify en of
               (ExprZero)
                 -> simplify ez
               (ExprSucc e)
                 -> simplify (substitute 0 (substitute 0 es (deeper (ExprInd vm em ez vp vr es e))) e) --NOTE the free variables in the interior es get subtracted from, that must not happen, hence the deeper
               e -> ExprInd vm (simplify em) (simplify ez) vp vr (simplify es) e
        (ExprUniv n)
          -> ExprUniv n
        (ExprDefn n v m e)
          -> simplify e
        (ExprNotDone n s)
          -> ExprNotDone n s

  instance Monad (Either e) where
    return = Right
    ea >>= ef = either Left ef ea

  instance MonadPlus (Either e) where
    mzero = Left (error "undefined error in MonadPlus of Either")
    l `mplus` r = either (const l) Right r

  type Fill = (String,Context,Constraint)

  type FillState e = StateT [Fill] (Either e)

  type FilledTypeResult = FillState TypeError

  mapError
    :: (e -> e')
    -> Either e a
    -> Either e' a
  mapError
    f
    = either (Left . f) Right

  addFill
    :: Fill
    -> FillState e ()
  addFill
    c
    = modify (c:) >> return ()

  failAs
    :: e'
    -> FillState e a
    -> FillState e' a
  failAs
    = mapStateT . mapError . const

  failure
    :: e
    -> FillState e a
  failure
    = lift . Left

  processType
    :: FilledTypeResult a
    -> (TypeError -> b)
    -> ([Fill] -> a -> b)
    -> b
  processType
    tr
    ef
    sf
    = either ef (uncurry (flip sf)) $ runStateT tr []

  typeFill
    :: Context
    -> Expression
    -> Maybe Expression
    -> FilledTypeResult Expression
  typeFill
    context
    expr
    mtexpr
    = case expr of
        (ExprName name)
          -> maybe
               (failure $ TENotDefined name)
               (\t -> fillSubtypeExpr context expr t mtexpr)
               (lookupGlobalType context name)
        (ExprVar num)
          -> fillSubtypeExpr context expr (lookupLocalType context num) mtexpr
        (ExprAll v t b)
          -> do tu <- typeGet context t
                bu <- typeGet (addLocal context v t) b
                isUniv context tu
                fillSubtypeExpr context expr (maxUniv tu bu) mtexpr
        (ExprLam v t b)
          -> do tu <- typeGet context t
                isUniv context tu
                case liftM simplify mtexpr of
                  (Just (ExprAll v' t' bt))
                    -> do fillSubtypeExpr context expr t' (Just t) --NOTE this use of fillSubtypeExpr is slightly different, because expr is not of type t'
                          bt' <- typeFill (addLocal context v t) b (Just bt)
                          return (ExprAll v' t' bt)
                  (Just t)
                    -> failure $ TEExpected context expr (ExprAll v t (ExprNotDone "unknown" "1")) t
                  Nothing
                    -> do bt <- typeGet (addLocal context v t) b
                          return (ExprAll v t bt)
        (ExprApp f x)
          -> (do ft <- typeGet context f
                 case simplify ft of
                   (ExprAll _ t b)
                     -> do typeFill context x (Just t)
                           fillSubtypeExpr context expr (substitute 0 b x) mtexpr
                   _ -> failure $ TENotFunction context f ft)
             `mplus`
             (do xt <- typeGet context x
                 ft <- typeFill context f (liftM (ExprAll "_" xt) mtexpr)
                 case simplify ft of
                   (ExprAll _ t b)
                     -> return (substitute 0 b x)
                   _ -> failure $ TENotFunction context f ft)
        (ExprExists v t b)
          -> do tu <- typeGet context t
                bu <- typeGet (addLocal context v t) b
                isUniv context tu
                fillSubtypeExpr context expr (maxUniv tu bu) mtexpr
        (ExprPair l r)
          -> case liftM simplify mtexpr of
               (Just (ExprExists v lt rt))
                 -> do typeFill context l (Just lt)
                       typeFill context r (Just (substitute 0 rt l))
                       return (ExprExists v lt rt)
               (Just t)
                 -> failure $ TEExpected context expr (ExprExists "_" (ExprNotDone "unknown" "2") (ExprNotDone "unknown" "3")) t --TODO come up with a better error, none of this unknown crap
               Nothing
                 -> do lt <- typeGet context l
                       rt <- typeGet context r
                       return (ExprExists "_" lt rt)
        (ExprSplit vl vr b s)
          -> do ts <- typeGet context s
                case simplify ts of
                  (ExprExists _ tl tr)
                    -> typeFill (addLocal (addLocal context vl tl) vr tr) b mtexpr
                  t
                    -> failure $ TENotPair context s ts
        (ExprNat)
          -> fillSubtypeExpr context expr (ExprUniv 0) mtexpr
        (ExprZero)
          -> fillSubtypeExpr context expr ExprNat mtexpr
        (ExprSucc e)
          -> do typeFill context e (Just ExprNat)
                fillSubtypeExpr context expr ExprNat mtexpr
        (ExprInd vm em ez vp vr es en)
          -> do mu <- typeGet (addLocal context vm ExprNat) em
                isUniv context mu
                typeFill context ez (Just $ substitute 0 em ExprZero)
                typeFill (addLocal (addLocal context vp ExprNat) vr (substitute 0 em (ExprVar 0))) es (Just $ substitute 0 em (ExprSucc (ExprVar 1)))
                typeFill context en (Just ExprNat)
                fillSubtypeExpr context expr (substitute 0 em en) mtexpr
        (ExprUniv n)
          -> fillSubtypeExpr context expr (ExprUniv (succ n)) mtexpr
        (ExprDefn n v m e) --TODO call this DefnUnroll and add a DefnRoll
          -> do typeFill context e (Just $ substitute 0 m (ExprName n))
                maybe
                  (failure $ TENotDefined n)
                  (\d -> fillSubtypeExpr context expr (substitute 0 m d) mtexpr)
                  (lookupGlobalValue context n)
        (ExprNotDone n s)
          -> maybe
               (failure $ TENotDone)
               (\texpr -> addFill (n,context,COfType texpr) >> return texpr)
               mtexpr
      
  fillSubtypeExpr
    :: Context
    -> Expression
    -> Expression
    -> Maybe Expression
    -> FilledTypeResult Expression
  fillSubtypeExpr
    context
    exprExamine --NOTE only used for error reporting, TODO can we move this out tidily?
    exprSub
    mExprSup
    = case mExprSup of
        Nothing
          -> return exprSub
        (Just exprSup)
          -> case (simplify exprSub,exprSup) of
               (ExprName name0, ExprName name1)
                 -> if name0 == name1
                      then return exprSup
                      else failure $ TEExpected context exprExamine exprSub exprSup
               (ExprVar num0, ExprVar num1)
                 -> if num0 == num1
                      then return exprSup
                      else failure $ TEExpected context exprExamine exprSub exprSup
               (ExprAll _ t0 b0, ExprAll _ t1 b1)
                 -> do fillSubtypeExpr context exprExamine t1 (Just t0)
                       fillSubtypeExpr context exprExamine b0 (Just b1)
                       return exprSup
               (ExprUniv n0, ExprUniv n1)
                 -> if n0 <= n1
                      then return exprSup
                      else failure $ TEExpected context exprExamine exprSub exprSup
               (ExprNotDone n s, _)
                 -> do addFill (n,context,CSubtype exprSup)
                       return exprSup
               (_, ExprNotDone n s)
                 -> do addFill (n,context,CSupertype exprSub)
                       return exprSub
               _ -> do failAs (TEExpected context exprExamine exprSub exprSup) $ fillEqExpr context exprSub exprSup
                       return exprSub

  fillEqExpr
    :: Context
    -> Expression
    -> Expression
    -> FillState () ()
  fillEqExpr
    context
    expr0
    expr1
    = case (simplify expr0,simplify expr1) of
        (ExprName name0, ExprName name1)
          -> require (name0 == name1)
        (ExprVar num0, ExprVar num1)
          -> require (num0 == num1)
        (ExprAll _ t0 b0, ExprAll _ t1 b1)
          -> do fillEqExpr context t0 t1
                fillEqExpr context b0 b1
        (ExprLam _ t0 b0, ExprLam _ t1 b1)
          -> do fillEqExpr context t0 t1
                fillEqExpr context b0 b1
        (ExprApp f0 x0, ExprApp f1 x1)
          -> do fillEqExpr context f0 f1
                fillEqExpr context x0 x1
        (ExprExists _ t0 b0, ExprExists _ t1 b1)
          -> do fillEqExpr context t0 t1
                fillEqExpr context b0 b1
        (ExprPair l0 r0, ExprPair l1 r1)
          -> do fillEqExpr context l0 l1
                fillEqExpr context r0 r1
        (ExprSplit _ _ b0 s0, ExprSplit _ _ b1 s1)
          -> do fillEqExpr context b0 b1
                fillEqExpr context s0 s1
        (ExprNat,ExprNat)
          -> return ()
        (ExprZero,ExprZero)
          -> return ()
        (ExprSucc e0, ExprSucc e1)
          -> fillEqExpr context e0 e1
        (ExprInd _ em0 ez0 _ _ es0 en0, ExprInd _ em1 ez1 _ _ es1 en1)
          -> do fillEqExpr context em0 em1
                fillEqExpr context ez0 ez1
                fillEqExpr context es0 es1
                fillEqExpr context en0 en1
        (ExprUniv n0, ExprUniv n1)
          -> require (n0 == n1)
        (ExprDefn _ _ m0 e0, ExprDefn _ _ m1 e1)
          -> do fillEqExpr context m0 m1
                fillEqExpr context e0 e1
        (ExprNotDone n s, e)
          -> addFill (n,context,CEqual expr1)
        (e, ExprNotDone n s)
          -> addFill (n,context,CEqual expr0)
        _ -> failure ()
    where
      require
        :: Bool
        -> FillState () ()
      require
        b
        = case b of
            True
              -> return ()
            False
              -> failure ()

  typeGet
    :: Context
    -> Expression
    -> FilledTypeResult Expression
  typeGet
    context
    expr
    = typeFill context expr Nothing

  typeCheck
    :: Context
    -> Expression
    -> Expression
    -> FilledTypeResult ()
  typeCheck
    context
    expr
    texpr
    = typeFill context expr (Just texpr) >> return ()

  substitute
    :: Int
    -> Expression
    -> Expression
    -> Expression
  substitute
    v
    e
    y
    = case e of
        (ExprName name)
          -> (ExprName name)
        (ExprVar v')
          -> if v == v' 
               then y
               else ExprVar (if v' < v then v' else pred v')
        (ExprAll n t b)
          -> ExprAll n (substitute v t y) (substitute (succ v) b (deeper y))
        (ExprLam n t b)
          -> ExprLam n (substitute v t y) (substitute (succ v) b (deeper y))
        (ExprApp f x)
          -> ExprApp (substitute v f y) (substitute v x y)
        (ExprExists n t b)
          -> ExprAll n (substitute v t y) (substitute (succ v) b (deeper y))
        (ExprPair l r)
          -> ExprPair (substitute v l y) (substitute v r y)
        (ExprSplit nl nr b s)
          -> ExprSplit nl nr (substitute (succ (succ v)) b (deeper (deeper y))) (substitute v s y)
        (ExprNat)
          -> ExprNat
        (ExprZero)
          -> ExprZero
        (ExprSucc n)
          -> ExprSucc (substitute v n y)
        (ExprInd vm em ez vp vr es en)
          -> ExprInd vm (substitute (succ v) em (deeper y)) (substitute v ez y) vp vr (substitute (succ (succ v)) es (deeper (deeper y))) (substitute v en y)
        (ExprUniv n)
          -> ExprUniv n
        (ExprDefn n var m e)
          -> ExprDefn n var (substitute (succ v) m y) (substitute v e y)
        (ExprNotDone n s)
          -> ExprNotDone n s

  data Constraint = CEqual Expression
                  | CSubtype Expression
                  | CSupertype Expression
                  | COfType Expression
                  | CIsUniv

  isUniv
    :: Context
    -> Expression
    -> FilledTypeResult ()
  isUniv
    context
    expr
    = case simplify expr of
        (ExprUniv _)
          -> return ()
        (ExprNotDone n s)
          -> do addFill (n,context,CIsUniv)
                return ()
        _ -> failure (TENotType context expr)

  maxUniv
    :: Expression
    -> Expression
    -> Expression
  maxUniv
    e0
    e1
    = case (simplify e0,simplify e1) of
        (ExprUniv n0,ExprUniv n1)
          -> if n0 <= n1 then e0 else e1
        (ExprUniv n0,_)
          -> e0
        (_,ExprUniv n1)
          -> e1
        (ExprNotDone n s,_)
          -> e0
        (_,ExprNotDone n s)
          -> e1
        (_,_)
          -> error "two non-universes passed to maxUniv"

  deeper
    :: Expression
    -> Expression
  deeper
    = chvar succ

  shallower
    :: Expression
    -> Expression
  shallower
    = chvar pred

  chvar
    :: (Int -> Int)
    -> Expression
    -> Expression
  chvar
    f
    expr
    = chvar' f 0 expr
    where
      chvar'
        :: (Int -> Int)
        -> Int
        -> Expression
        -> Expression
      chvar'
        sf
        lim
        expr
        = case expr of
            (ExprName n)
              -> ExprName n
            (ExprVar v)
              -> ExprVar (if v >= lim then sf v else v)
            (ExprAll n t b)
              -> ExprAll n (chvar' sf lim t) (chvar' sf (succ lim) b)
            (ExprLam n t b)
              -> ExprLam n (chvar' sf lim t) (chvar' sf (succ lim) b)
            (ExprApp f x)
              -> ExprApp (chvar' sf lim f) (chvar' sf lim x)
            (ExprExists n t b)
              -> ExprExists n (chvar' sf lim t) (chvar' sf (succ lim) b)
            (ExprPair l r)
              -> ExprPair (chvar' sf lim l) (chvar' sf lim r)
            (ExprSplit vl vr b s)
              -> ExprSplit vl vr (chvar' sf (succ (succ lim)) b) (chvar' sf lim s)
            (ExprNat)
              -> ExprNat
            (ExprZero)
              -> ExprZero
            (ExprSucc e)
              -> ExprSucc (chvar' sf lim e)
            (ExprInd vm em ez vp vr es en)
              -> ExprInd vm (chvar' sf (succ lim) em) (chvar' sf lim ez) vp vr (chvar' sf (succ (succ lim)) es) (chvar' sf lim en)
            (ExprUniv n)
              -> ExprUniv n
            (ExprDefn n v m e)
              -> ExprDefn n v (chvar' sf (succ lim) m) (chvar' sf lim e)
            (ExprNotDone n s)
              -> ExprNotDone n s
