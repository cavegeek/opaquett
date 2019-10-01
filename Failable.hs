module Failable (
  Failable(Fail,Succeed),
  mightFail,
  failMap,
  oneOf
  ) where

  data Failable err val = Fail err
                        | Succeed val

  instance Monad (Failable err) where
    return val = Succeed val
    (Fail e) >>= fy = (Fail e)
    (Succeed v) >>= fy = fy v

  instance Functor (Failable err) where
    fmap f (Fail e) = Fail e
    fmap f (Succeed val) = Succeed (f val)

  mightFail
    :: (err -> a)
    -> (val -> a)
    -> Failable err val
    -> a
  mightFail
    f
    s
    failable
    = case failable of
        (Fail e) -> f e
        (Succeed v) -> s v

  failMap
    :: (err0 -> err1)
    -> Failable err0 val
    -> Failable err1 val
  failMap
    f
    f0
    = case f0 of
        (Fail e) -> Fail (f e)
        (Succeed v) -> Succeed v
  
  oneOf
    :: [Failable err val]
    -> Failable [err] val
  oneOf
    = foldr combine (Fail [])
    where
      combine
        :: Failable err val
        -> Failable [err] val
        -> Failable [err] val
      combine
        f
        f'
        = case f of
            (Fail e)
              -> failMap (e:) f'
            (Succeed v)
              -> Succeed v
