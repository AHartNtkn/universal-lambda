import Data.Bifunctor
import Data.Digits

-- ============ A universal lambda function ============

data Fix f = Fix (f (Fix f))

-- Section 0: Defining building-block isomorphisms.

unDigitsRev :: Integral n => n -> [n] -> n
unDigitsRev b = unDigits b . reverse

-- ℕ ≅ ℕ × ℕ
natToNatTimesNat :: Integer -> (Integer, Integer)
natToNatTimesNat n = case unInterleave $ digitsRev 2 n of
    (ib, jb) -> (unDigitsRev 2 ib, unDigitsRev 2 jb)
  where
  unInterleave :: [a] -> ([a], [a])
  unInterleave (x:y:xs) = case unInterleave xs of
    (b1, b2) -> (x:b1, y:b2)
  unInterleave (x:[]) = ([x], [])
  unInterleave [] = ([], [])

-- ℕ × ℕ ≅ ℕ
natTimesNatToNat :: (Integer, Integer) -> Integer
natTimesNatToNat (i, j) =
  unDigitsRev 2 $ padInterleave (digitsRev 2 i) (digitsRev 2 j)
    where
    padInterleave [] [] = []
    padInterleave (x:xs) [] = x:0:padInterleave xs []
    padInterleave [] (x:xs) = 0:x:padInterleave [] xs
    padInterleave (x:xs) (y:ys) = x:y:padInterleave xs ys

-- ℕ ≅ ℕ + ℕ
natToNatPlusNat :: Integer -> Either Integer Integer
natToNatPlusNat i | mod i 2 == 0 = Left $ i `div` 2
                  | True         = Right $ i `div` 2

-- ℕ + ℕ ≅ ℕ
natPlusNatToNat :: Either Integer Integer -> Integer
natPlusNatToNat (Left i) = 2 * i
natPlusNatToNat (Right i) = 2 * i + 1

-- ℕ ≅ Fin n + ℕ
natToNPlusNat :: Integer -> Integer -> Either Integer Integer
natToNPlusNat n i | i < n = Left i
                  | True  = Right $ i - n

-- Fin n + ℕ ≅ ℕ
nPlusNatToNat :: Integer -> Either Integer Integer -> Integer
nPlusNatToNat n (Left i)  = i
nPlusNatToNat n (Right i) = i + n

-- Section 1: Defining an isomorphism between ℕ and lambda expressions

data LamF r = Var Integer | Lam r | App r r
type Lam = Fix LamF

-- Fibrational functorial map over LamF
lamFMap :: Integer -> (Integer -> a -> b) -> LamF a -> LamF b
lamFMap k f (Var i) = Var i
lamFMap k f (Lam r) = Lam $ f (k+1) r
lamFMap k f (App r1 r2) = App (f k r1) (f k r2)

-- Generate a specialized algebra from a generic one
lamAlg :: (Integer -> Either Integer (Either r (r, r)) -> r)
       -> Integer -> LamF r -> r
lamAlg f k (Var i) = f k (Left i)
lamAlg f k (Lam r) = f k (Right $ Left r)
lamAlg f k (App r1 r2) = f k (Right $ Right (r1, r2))

lamCata :: (Integer -> LamF r -> r) -> Integer -> Lam -> r
lamCata a k (Fix l) = a k $ lamFMap k (lamCata a) l

-- Generate a specialized coalgebra from a generic one
lamCoalg :: (Integer -> r -> Either Integer (Either r (r, r)))
         -> Integer -> r -> LamF r
lamCoalg f k r = case f k r of
  Left i -> Var i
  Right (Left r) -> Lam r
  Right (Right (r1, r2)) -> App r1 r2

lamAna :: (Integer -> r -> LamF r) -> Integer -> r -> Lam
lamAna c k = Fix . lamFMap k (lamAna c) .c k

lamToNat :: Lam -> Integer
lamToNat = lamCata (lamAlg lamToNatAlg) 0 where
  lamToNatAlg :: Integer
              -> Either Integer (Either Integer (Integer, Integer))
              -> Integer
  lamToNatAlg i =
    nPlusNatToNat i
    . bimap id (natPlusNatToNat
                . bimap id natTimesNatToNat)

natToLam :: Integer -> Lam
natToLam = lamAna (lamCoalg natToLamCoalg) 0 where
  natToLamCoalg :: Integer -> Integer
                -> Either Integer (Either Integer (Integer, Integer))
  natToLamCoalg i =
    bimap id (bimap id natToNatTimesNat
              . natToNatPlusNat)
    . natToNPlusNat i

-- Section 2: Defining an isomorphism between ℕ and normalized lambda expressions

-- The type of normalized lambda expressions.
data NLamF r = NVar Integer | NLam r | NApp ALam r
type NLam = Fix NLamF
data ALamF r = AVar Integer | AApp r NLam
type ALam = Fix ALamF


-- Fibrational functorial maps
nLamFMap :: Integer -> (Integer -> a -> b) -> NLamF a -> NLamF b
nLamFMap k f (NVar i) = NVar i
nLamFMap k f (NLam r) = NLam $ f (k+1) r
nLamFMap k f (NApp r1 r2) = NApp r1 (f k r2)

aLamFMap :: Integer -> (Integer -> a -> b) -> ALamF a -> ALamF b
aLamFMap k f (AVar i) = AVar i
aLamFMap k f (AApp r1 r2) = AApp (f k r1) r2

-- Generate a specialized algebra from a generic one
nLamAlg :: (Integer -> Either Integer (Either r (ALam, r)) -> r)
        -> Integer -> NLamF r -> r
nLamAlg f k (NVar i) = f k (Left i)
nLamAlg f k (NLam r) = f k (Right $ Left r)
nLamAlg f k (NApp r1 r2) = f k (Right $ Right (r1, r2))

aLamAlg :: (Integer -> Either Integer (r, NLam) -> r)
        -> Integer -> ALamF r -> r
aLamAlg f k (AVar i) = f k (Left i)
aLamAlg f k (AApp r1 r2) = f k (Right (r1, r2))



nLamCata :: (Integer -> NLamF r -> r) -> Integer -> NLam -> r
nLamCata a k (Fix l) = a k $ nLamFMap k (nLamCata a) l

aLamCata :: (Integer -> ALamF r -> r) -> Integer -> ALam -> r
aLamCata a k (Fix l) = a k $ aLamFMap k (aLamCata a) l



-- Generate a specialized coalgebra from a generic one
nLamCoalg :: (Integer -> r -> Either Integer (Either r (ALam, r)))
          -> Integer -> r -> NLamF r
nLamCoalg f k r = case f k r of
  Left i -> NVar i
  Right (Left r) -> NLam r
  Right (Right (r1, r2)) -> NApp r1 r2

aLamCoalg :: (Integer -> r -> Either Integer (r, NLam)) ->
             Integer -> r -> ALamF r
aLamCoalg f k r = case f k r of
  Left i -> AVar i
  Right (r1, r2) -> AApp r1 r2



nLamAna :: (Integer -> r -> NLamF r) -> Integer -> r -> NLam
nLamAna c k = Fix . nLamFMap k (nLamAna c) . c k

aLamAna :: (Integer -> r -> ALamF r) -> Integer -> r -> ALam
aLamAna c k = Fix . aLamFMap k (aLamAna c) . c k



-- The isomorphism from ℕ
natToNLam :: Integer -> NLam
natToNLam = Fix . NLam . natToNLamP 1 where
  natToNLamCoalg :: Integer -> Integer
                 -> Either Integer (Either Integer (ALam, Integer))
  natToNLamCoalg k =
    bimap id (bimap id (bimap (natToALam k) id
                        . natToNatTimesNat)
              . natToNatPlusNat)
    . natToNPlusNat k

  natToALamCoalg :: Integer -> Integer -> Either Integer (Integer, NLam)
  natToALamCoalg k =
    bimap id (bimap id (natToNLamP k)
              . natToNatTimesNat)
    . natToNPlusNat k

  natToNLamP :: Integer -> Integer -> NLam
  natToNLamP = nLamAna (nLamCoalg natToNLamCoalg)

  natToALam :: Integer -> Integer -> ALam
  natToALam = aLamAna (aLamCoalg natToALamCoalg)



-- The isomorphism to ℕ
nLamToNat :: NLam -> Integer
nLamToNat (Fix (NLam l)) = nLamToNatP 1 l where
  nLamToNatAlg :: Integer
               -> Either Integer (Either Integer (ALam, Integer))
               -> Integer
  nLamToNatAlg k =
    nPlusNatToNat k
    . bimap id (natPlusNatToNat
                . bimap id (natTimesNatToNat
                            . bimap (aLamToNat k) id))

  aLamToNatAlg :: Integer -> Either Integer (Integer, NLam) -> Integer
  aLamToNatAlg k =
    nPlusNatToNat k
    . bimap id (natTimesNatToNat
                . bimap id (nLamToNatP k))

  nLamToNatP :: Integer -> NLam -> Integer
  nLamToNatP = nLamCata (nLamAlg nLamToNatAlg)

  aLamToNat :: Integer -> ALam -> Integer
  aLamToNat = aLamCata (aLamAlg aLamToNatAlg) 



-- Section 3: Defining an evaluation function and completing our universal function.

-- Evaluate to a normal form
eval :: Lam -> NLam
eval a = spine a [] where
  -- Raise bound variables
  quote :: Integer -> Lam -> Lam
  quote = lamCata quoteAlg where
    quoteAlg :: Integer -> LamF Lam -> Lam
    quoteAlg n (Var x) | x >= n = Fix $ Var $ x + 1
                       | True   = Fix $ Var x
    quoteAlg n (Lam r)  = Fix $ Lam r
    quoteAlg n (App r1 r2) = Fix $ App r1 r2

  -- Substitute into an expression, for a variable, some value
  sub :: Integer -> Lam -> Lam -> Lam
  sub = lamCata subAlg where
    subAlg :: Integer -> LamF (Lam -> Lam) -> (Lam -> Lam)
    subAlg n (Var x) | x < n  = const $ Fix $ Var x
                     | x == n = id
                     | x > n  = const $ Fix $ Var $ x - 1
    subAlg n (Lam f) = Fix . Lam . f . quote 0
    subAlg n (App f1 f2) = \e -> Fix $ App (f1 e) (f2 e)

  spine :: Lam -> [Lam] -> NLam
  spine (Fix (Lam e))   []     = Fix $ NLam $ spine e []
  spine (Fix (Lam e))   (e1:x) = spine (sub 0 e e1) x
  spine (Fix (App a b)) x      = spine a (b:x)
  spine (Fix (Var i))   []     = Fix $ NVar i
  spine e@(Fix (Var i)) x@(_:_) =
    Fix $ NApp (afold e (reverse $ init x)) (spine (last x) [])

  afold :: Lam -> [Lam] -> ALam
  afold x (b:y) = Fix $ AApp (afold x y) (spine b [])
  afold (Fix (Var i)) [] = Fix $ AVar i

-- A universal lambda function
u :: Integer -> Integer
u = nLamToNat . eval . natToLam

-- As a function between binary strings
ub = bin . u . unbin where
  unbin b = unDigits 2 (1:b) - 1
  bin n = tail $ digits 2 (n+1)
