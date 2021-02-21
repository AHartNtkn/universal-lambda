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
natToNPlusNat i n | n < i = Left n
                  | True  = Right $ n - i

-- Fin n + ℕ ≅ ℕ
nPlusNatToNat :: Integer -> Either Integer Integer -> Integer
nPlusNatToNat i (Left n)  = n
nPlusNatToNat i (Right n) = n + i

-- Section 1: Defining an isomorphism between ℕ and lambda expressions
data LamF r = Var Integer | Lam r | App r r
type Lam = Fix LamF

showLam :: Lam -> String
showLam (Fix (Var i)) = show i
showLam (Fix (Lam r)) = 'L':showLam r
showLam (Fix (App r1 r2)) = ('(' : showLam r1) ++ (' ' : showLam r2) ++ ")"

-- Fibrational functorial map over LamF
lamFMap :: Integer -> (Integer -> a -> b) -> LamF a -> LamF b
lamFMap k f (Var i) = Var i
lamFMap k f (Lam r) = Lam $ f (k+1) r
lamFMap k f (App r1 r2) = App (f k r1) (f k r2)

-- Generate a specialized algebra from a generic one
lamAlg :: (Integer -> Either Integer (Either r (r, r)) -> r) ->
            Integer -> LamF r -> r
lamAlg f k (Var i) = f k (Left i)
lamAlg f k (Lam r) = f k (Right $ Left r)
lamAlg f k (App r1 r2) = f k (Right $ Right (r1, r2))

lamCata :: (Integer -> LamF r -> r) -> Integer -> Lam -> r
lamCata a k (Fix l) = a k $ lamFMap k (lamCata a) l

-- Generate a specialized coalgebra from a generic one
lamCoalg :: (Integer -> r -> Either Integer (Either r (r, r))) ->
          Integer -> r -> LamF r
lamCoalg f k r = case f k r of
  Left i -> Var i
  Right (Left r) -> Lam r
  Right (Right (r1, r2)) -> App r1 r2

lamAna :: (Integer -> r -> LamF r) -> Integer -> r -> Lam
lamAna c k = Fix . lamFMap k (lamAna c) .c k

lamToNat :: Lam -> Integer
lamToNat = lamCata (lamAlg lamToNatAlg) 0 where
  lamToNatAlg i =
    nPlusNatToNat i
    . bimap id (natPlusNatToNat
                . bimap id natTimesNatToNat)

natToLam :: Integer -> Lam
natToLam = lamAna (lamCoalg natToLamCoalg) 0 where
  natToLamCoalg i =
    bimap id (bimap id natToNatTimesNat
              . natToNatPlusNat)
    . natToNPlusNat i

-- Section 2: Defining an isomorphism between ℕ and normalized lambda expressions

-- The type of normalized lambda expressions.
data LamNF r = NVar Integer | NLam r | NApp LamA r
type LamN = Fix LamNF
data LamAF r = AVar Integer | AApp r LamN
type LamA = Fix LamAF



showLamN :: LamN -> String
showLamN (Fix (NVar i)) = show i
showLamN (Fix (NLam r)) = 'L':showLamN r
showLamN (Fix (NApp r1 r2)) = ('(' : showLamA r1) ++ (' ' : showLamN r2) ++ ")"

showLamA :: LamA -> String
showLamA (Fix (AVar i)) = show i
showLamA (Fix (AApp r1 r2)) = ('(' : showLamA r1) ++ (' ' : showLamN r2) ++ ")"



-- Fibrational functorial maps
lamNFMap :: Integer -> (Integer -> a -> b) -> LamNF a -> LamNF b
lamNFMap k f (NVar i) = NVar i
lamNFMap k f (NLam r) = NLam $ f (k+1) r
lamNFMap k f (NApp r1 r2) = NApp r1 (f k r2)

lamAFMap :: Integer -> (Integer -> a -> b) -> LamAF a -> LamAF b
lamAFMap k f (AVar i) = AVar i
lamAFMap k f (AApp r1 r2) = AApp (f k r1) r2

-- Generate a specialized algebra from a generic one
lamNAlg :: (Integer -> Either Integer (Either r (LamA, r)) -> r) ->
            Integer -> LamNF r -> r
lamNAlg f k (NVar i) = f k (Left i)
lamNAlg f k (NLam r) = f k (Right $ Left r)
lamNAlg f k (NApp r1 r2) = f k (Right $ Right (r1, r2))

lamAAlg :: (Integer -> Either Integer (r, LamN) -> r) ->
            Integer -> LamAF r -> r
lamAAlg f k (AVar i) = f k (Left i)
lamAAlg f k (AApp r1 r2) = f k (Right (r1, r2))



lamNCata :: (Integer -> LamNF r -> r) -> Integer -> LamN -> r
lamNCata a k (Fix l) = a k $ lamNFMap k (lamNCata a) l

lamACata :: (Integer -> LamAF r -> r) -> Integer -> LamA -> r
lamACata a k (Fix l) = a k $ lamAFMap k (lamACata a) l



-- Generate a specialized coalgebra from a generic one
lamNCoalg :: (Integer -> r -> Either Integer (Either r (LamA, r))) ->
          Integer -> r -> LamNF r
lamNCoalg f k r = case f k r of
  Left i -> NVar i
  Right (Left r) -> NLam r
  Right (Right (r1, r2)) -> NApp r1 r2

lamACoalg :: (Integer -> r -> Either Integer (r, LamN)) ->
             Integer -> r -> LamAF r
lamACoalg f k r = case f k r of
  Left i -> AVar i
  Right (r1, r2) -> AApp r1 r2



lamNAna :: (Integer -> r -> LamNF r) -> Integer -> r -> LamN
lamNAna c k = Fix . lamNFMap k (lamNAna c) . c k

lamAAna :: (Integer -> r -> LamAF r) -> Integer -> r -> LamA
lamAAna c k = Fix . lamAFMap k (lamAAna c) . c k



-- The isomorphism from ℕ
natToLamN :: Integer -> LamN
natToLamN = Fix . NLam . natToLamNP 1 where
  natToLamNCoalg :: Integer -> Integer ->
                    Either Integer (Either Integer (LamA, Integer))
  natToLamNCoalg k =
    bimap id (bimap id (bimap (natToLamA k) id
                        . natToNatTimesNat)
              . natToNatPlusNat)
    . natToNPlusNat k

  natToLamACoalg :: Integer -> Integer -> Either Integer (Integer, LamN)
  natToLamACoalg k =
    bimap id (bimap id (natToLamNP k)
              . natToNatTimesNat)
    . natToNPlusNat k

  natToLamNP :: Integer -> Integer -> LamN
  natToLamNP = lamNAna (lamNCoalg natToLamNCoalg)

  natToLamA :: Integer -> Integer -> LamA
  natToLamA = lamAAna (lamACoalg natToLamACoalg)



-- The isomorphism to ℕ
lamNToNat :: LamN -> Integer
lamNToNat (Fix (NLam l)) = lamNToNatP 1 l where
  lamNToNatAlg :: Integer ->
                  Either Integer (Either Integer (LamA, Integer)) -> Integer
  lamNToNatAlg k =
    nPlusNatToNat k
    . bimap id (natPlusNatToNat
                . bimap id (natTimesNatToNat
                            . bimap (lamAToNat k) id))

  lamAToNatAlg :: Integer -> Either Integer (Integer, LamN) -> Integer
  lamAToNatAlg k =
    nPlusNatToNat k
    . bimap id (natTimesNatToNat
                . bimap id (lamNToNatP k))

  lamNToNatP :: Integer -> LamN -> Integer
  lamNToNatP = lamNCata (lamNAlg lamNToNatAlg)

  lamAToNat :: Integer -> LamA -> Integer
  lamAToNat = lamACata (lamAAlg lamAToNatAlg) 




-- Section 3: Defining an evaluation function and completing our universal function.

-- Evaluate to a normal form
eval :: Lam -> LamN
eval a = spine a [] where
  -- Raise bound variables
  quote :: Integer -> Lam -> Lam
  quote = lamCata quoteAlg where
    quoteAlg :: Integer -> LamF Lam -> Lam
    quoteAlg n (Var x) | x >= n = Fix $ Var $ x + 1
                       | True   = Fix $ Var x
    quoteAlg n (Lam r)  = Fix $ Lam r
    quoteAlg n (App r1 r2) = Fix $ App r1 r2

  -- Substitute e into l for variable n
  sub :: Lam -> Integer -> Lam -> Lam
  sub e n l = lamCata subAlg n l e where
    subAlg :: Integer -> LamF (Lam -> Lam) -> (Lam -> Lam)
    subAlg n (Var x) | x < n  = const $ Fix $ Var x
                     | x == n = id
                     | x > n  = const $ Fix $ Var $ x - 1
    subAlg n (Lam f) = Fix . Lam . f . quote 0
    subAlg n (App f1 f2) = \e -> Fix $ App (f1 e) (f2 e)

  spine :: Lam -> [Lam] -> LamN
  spine (Fix (Lam e))   []     = Fix $ NLam $ eval e
  spine (Fix (Lam e))   (e1:x) = spine (sub e1 0 e) x
  spine (Fix (App a b)) x      = spine a (b:x)
  spine (Fix (Var i))   []     = Fix $ NVar i
  spine e@(Fix (Var i)) x@(_:_) =
    Fix $ NApp (afold e (reverse $ init x)) (eval (last x))

  afold :: Lam -> [Lam] -> LamA
  afold x (b:y) = Fix $ AApp (afold x y) (eval b)
  afold (Fix (Var i)) [] = Fix $ AVar i

-- A universal lambda function
u :: Integer -> Integer
u = lamNToNat . eval . natToLam

-- Universal function as a function between binary strings
ub = bin . u . unbin where
  unbin b = unDigits 2 (1:b) - 1
  bin n = tail $ digits 2 (n+1)

-- fana :: Corecursive t => (a -> Base t a) -> a -> t

{-
NatTimesNatToNat[{0, 0}] := 0
NatTimesNatToNat[{x1_, x2_}] :=
 Block[{l, b1, b2},
  l = IntegerLength[Max[x1, x2], 2];
  b1 = IntegerDigits[x1, 2, l];
  b2 = IntegerDigits[x2, 2, l];
  
  FromDigits[Riffle[b1, b2], 2]
  ]
-}

{-
-- Pad binary string to appropriate length
pad :: Int -> Bin -> Bin
pad 0 x = x
pad i x = x ++ True : take (i-length x-1) (repeat False)

fuse :: (Bin, Bin) -> Bin
fuse (b1, b2) = case compare (length b2) (length b1) of
  GT -> interleave (pad (length b2) b1) b2 
  LT -> interleave b1 (pad (length b1) b2)
  EQ -> interleave b1 (b2 ++ [True])

unpad :: Bin -> Bin
unpad [] = []
unpad (False:xs) = False:unpad xs
unpad (True:xs) = go (Z.Zip [] xs) where
  go (Z.Zip r []) = []
  go (Z.Zip r (True:xs)) = True : (r ++ go (Z.Zip [] xs))
  go (Z.Zip r (False:xs)) = go $ Z.Zip (False:r) xs

uninterleave :: Bin -> (Bin, Bin)
uninterleave (x:y:xs) = case uninterleave xs of
  (b1, b2) -> (x:b1, y:b2)
uninterleave (x:[]) = ([x], [])
uninterleave [] = ([], [])

unfuse :: Bin -> (Bin, Bin)
unfuse b = case (mod (length b) 2 == 0, uninterleave b) of
  (True,  (b1, b2)) -> (b1, unpad b2)
  (False, (b1, b2)) -> (unpad b1, b2)

testListp :: Int -> [Bin]
testListp 0 = [[]]
testListp i = testListp (i-1) >>= \x -> [True:x, False:x]

testList :: Int -> [Bin]
testList i = concat $ map testListp [0..i+1]

-}



