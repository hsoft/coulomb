import Text.Printf

data Term = Term Double Int String deriving (Eq)

instance Show Term where
    show (Term mult exp id) =
        let isint = isInt mult 3
            prefix = case (isint, round mult) of
                (True, 1) -> ""
                (True, (-1)) -> "-"
                (True, _) -> printf "%0.0f" mult
                (False, _) -> printf "%0.2e" mult
            suffix = if exp /= 1 then "^" ++ (show exp) else ""
        in prefix ++ id ++ suffix

data BinaryOperator = Add | Subtract | Mult | Div | Equal deriving (Eq)

instance Show BinaryOperator where
    show Add = "+"
    show Subtract = "+"
    show Mult = "*"
    show Div = "/"
    show Equal = "="

data Expr =
    BinOp BinaryOperator Expr Expr |
    Var Term |
    Const Double
    deriving (Eq)

showBinOp fmt (BinOp op x y) = printf fmt (show x) (show op) (show y)

instance Show Expr where
    show (Var x) = show x
    show (Const x) = show x
    show all@(BinOp Equal _ _) = showBinOp "%s %s %s" all
    show all@(BinOp op (BinOp op1 _ _) (BinOp op2 _ _))
        | (op1 == op) && (op2 == op) = showBinOp "%s %s %s" all
        | op1 == op = showBinOp "%s %s (%s)" all
        | op2 == op = showBinOp "(%s) %s %s" all
        | otherwise = showBinOp "(%s) %s (%s)" all
    show all@(BinOp op (BinOp op1 _ _) _)
        | op1 == op = showBinOp "%s %s %s" all
        | otherwise = showBinOp "(%s) %s %s" all
    show all@(BinOp op _ (BinOp op2 _ _))
        | op2 == op = showBinOp "%s %s %s" all
        | otherwise = showBinOp "(%s) %s %s" all
    show all@(BinOp op _ _) = showBinOp "%s %s %s" all

c x = (Const x)
var t = if isTermZero t then c 0 else (Var t)
vs x = vi 1 x
vi mx x = (var (Term mx 1 x))
add x y = (BinOp Add x y)
sub x y = (BinOp Subtract x y)
mult x y = (BinOp Mult x y)
div_ x y = (BinOp Div x y)
equal x y = (BinOp Equal x y)

-- https://stackoverflow.com/a/12868743
-- Returns if x is an int to n decimal places
isInt :: (Integral a, RealFrac b) => b -> a -> Bool
isInt x n = (round $ 10^(fromIntegral n)*(x-(fromIntegral $ round x)))==0

negateTerm (Term mx exp x) = (Term (-mx) exp x)

negateExpr (Const val) = (c (val * (-1)))
negateExpr (Var term) = (var (negateTerm term))
negateExpr (BinOp op x y) = (BinOp op (negateExpr x) (negateExpr y))

invertTerm (Term mx exp x) = (Term mx (-exp) x)

invertExpr (Const val) = (c (val ** (-1)))
invertExpr (Var term) = (var (invertTerm term))
invertExpr (BinOp op x y) = (BinOp op (invertExpr x) (invertExpr y))


isTermZero (Term m _ _) = m <= 0.001 && m >= -0.001

addTerm (Term mx expx x) (Term my expy y)
    | x == y && expx == expy = (Just (Term (mx + my) expy y))
    | otherwise = Nothing

multTerm (Term mx expx x) (Term my expy y)
    | x == y = (Just (Term (mx * my) (expx + expy) y))
    | otherwise = Nothing

-- areOpsEqual: Returns whether our children expressions are either Const, Var or of the same
-- op as `opRef`
areOpsEqual _ (Const _) = True
areOpsEqual _ (Var _) = True
areOpsEqual opRef (BinOp op x y)
    | opRef == op = (areOpsEqual opRef x) && (areOpsEqual opRef y)
    | otherwise = False

applyBinOp_ op (x:[]) current = BinOp op current (Var x)
applyBinOp_ op (x:xs) current = BinOp op (applyBinOp_ op xs current) (Var x)

applyBinOp _ (x:[]) = (Var x)
applyBinOp op (x:xs) = applyBinOp_ op xs (Var x)

extractConsts :: Expr -> [Double]
extractConsts (Const x) = [x]
extractConsts (BinOp _ x y) = extractConsts y ++ extractConsts x
extractConsts _ = []

extractVars all@(Var _) = all:[]
extractVars (BinOp _ x y) = extractVars x ++ extractVars y
extractVars _ = []

mergeVars :: (Term -> Term -> Maybe Term) -> [Expr] -> [Expr]
mergeVars _ (x:[]) = [x]
mergeVars mergeFunc all@(vx@(Var x):vy@(Var y):[]) = case mergeFunc x y of
    Just merged -> [(Var merged)]
    Nothing -> all

mergeVars mergeFunc (vx@(Var x):vy@(Var y):xs) = case mergeFunc x y of
    Just merged -> mergeVars mergeFunc ((Var merged):xs)
    Nothing ->
        let (newX:newXS1) = mergeVars mergeFunc (vx:xs)
            (newY:newXS2) = mergeVars mergeFunc (vy:newXS1)
        in  (newX:newY:newXS2)

mapToBinOp f (BinOp op x y) = BinOp op (f x) (f y)
mapToBinOp f expr = f expr

-- Normalize
goesLeftOf (Var _) (Const _) = True
goesLeftOf (BinOp _ _ _) (Const _) = True
goesLeftOf (BinOp _ _ _) (Var _) = True
goesLeftOf (BinOp Mult _ _) (BinOp Add _ _) = True
goesLeftOf _ _ = False

normalizeSquash all@(BinOp Add x y)
    | areOpsEqual Add all =
        let consts = extractConsts all
            constsVal = sum consts
            constsValIsNeutral = constsVal == 0
            vars = mergeVars addTerm (extractVars all)
            terms = [t | (Var t) <- vars]
            filteredTerms = filter (\x -> not (isTermZero x)) terms
            appliedVars = applyBinOp Add terms
        in  case constsValIsNeutral of
            True -> appliedVars
            False -> (add appliedVars (c (sum consts)))
    | otherwise = mapToBinOp normalizeSquash all

normalizeSquash all@(BinOp Mult x y)
    | areOpsEqual Mult all =
        let consts = extractConsts all
            constsVal = foldl (*) 1 consts
            constsValIsNeutral = constsVal == 1
            vars = mergeVars multTerm (extractVars all)
            terms = [t | (Var t) <- vars]
            exprNullified = constsVal == 0 || (not (null (filter isTermZero terms)))
            appliedVars = applyBinOp Mult terms
        in  case (exprNullified, constsValIsNeutral) of
            (True, _) -> c 0
            (False, True) -> appliedVars
            (False, False) -> (BinOp Mult appliedVars (c (sum consts)))
    | otherwise = mapToBinOp normalizeSquash all

-- We normalize subtraction by transforming it into an addition of negative terms
normalizeSquash all@(BinOp Subtract left right) = normalize (BinOp Add left (negateExpr right))

-- We normalize division by transforming it into a multiplication of negative exponents
normalizeSquash all@(BinOp Div left right) = normalize (BinOp Mult left (invertExpr right))

-- We want to squash single 0-mult terms with minimal code duplication
normalizeSquash all@(Var _) = normalizeSquash (mult all (c 1))

normalizeSquash x = x

normalizeSendLeft all@(BinOp op x y)
    | goesLeftOf y x = normalizeSendLeft (BinOp op y x)
    | otherwise = mapToBinOp normalizeSendLeft all

normalizeSendLeft x = x

-- sendVarsLeftOfEqual: We send all variables to the left and all consts to the right

sendVarsLeftOfEqual left right@(Var x) =
    let toadd = (var (negateTerm x))
        newleft = solve (add left toadd)
        newright = solve (add right toadd)
    in  equal newleft newright

sendVarsLeftOfEqual left@(Const lx) right@(Const rx)
    | lx == rx = equal left right
    | otherwise = error "impossible equality!"

sendVarsLeftOfEqual left right = equal left right

-- Equal is normalized differently
normalize all@(BinOp Equal x y) = 
    let left = normalize x
        right = normalize y
    in sendVarsLeftOfEqual left right

normalize x
    | x == normalized = x
    | otherwise = normalize normalized
    where normalized = normalizeSendLeft (normalizeSquash x)

multToDiv all@(BinOp Mult x y)
    | areOpsEqual Mult all =
        let vars = extractVars all
            terms = [t | (Var t) <- vars]
            dividend = [t | t@(Term _ exp _) <- terms, exp >= 0] 
            divisors = [(Term mult (-exp) id) | t@(Term mult exp id) <- terms, exp < 0] 
            result =
                if null divisors then all
                else (BinOp Div (applyBinOp Mult dividend) (applyBinOp Mult divisors))
        in  result
    | otherwise = all

multToDiv (BinOp op x y) = (BinOp op (multToDiv x) (multToDiv y))
multToDiv x = x

solve = multToDiv . normalize

-- tests

assertEq a b
    | a == b = ()
    | otherwise = error (printf "%s != %s" a b)

testPairs = [
    (add (add (vs "x") (vs "y")) (vs "x"), "2x + y"),
    (add (vs "x") (mult (vs "x") (vs "y")), "(x * y) + x"),
    (mult (vs "x") (vs "x"), "x^2"),
    (mult (vs "x") (c 0), "0.0"),
    (div_ (mult (vs "x") (vs "x")) (vs "x"), "x"),
    (add (vs "x") (div_ (vs "x") (vs "y")), "(x / y) + x"),
    (sub (vs "x") (vs "y"), "x + -y"),
    (equal (vs "x") (vi 2 "y"), "x + -2y = 0.0")]

testAll = [assertEq (show (solve expr)) expected | (expr, expected) <- testPairs]
