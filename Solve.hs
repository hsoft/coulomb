import Text.Printf

data Term = Term Double Int String deriving (Eq)

instance Show Term where
    show (Term mult exp id) =
        let isint = isInt mult 3
            isone = isint && (round mult) == 1
            prefix = case (isint, isone) of
                (True, True) -> ""
                (True, False) -> printf "%0.0f" mult
                (False, False) -> printf "%0.2e" mult
            suffix = if exp /= 1 then "^" ++ (show exp) else ""
        in prefix ++ id ++ suffix

data BinaryOperator = Add | Mult | Div | Equal deriving (Eq)

instance Show BinaryOperator where
    show Add = "+"
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
mult x y = (BinOp Mult x y)
div_ x y = (BinOp Div x y)
equal x y = (BinOp Equal x y)

-- https://stackoverflow.com/a/12868743
-- Returns if x is an int to n decimal places
isInt :: (Integral a, RealFrac b) => b -> a -> Bool
isInt x n = (round $ 10^(fromIntegral n)*(x-(fromIntegral $ round x)))==0

negateTerm (Term mx exp x) = (Term (-mx) exp x)
invertTerm (Term mx exp x) = (Term mx (-exp) x)

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

applyBinOp _ (x:[]) = (Var x)
applyBinOp op (x:xs) = BinOp op (applyBinOp op xs) (Var x)

extractConsts :: Expr -> [Double]
extractConsts (Const x) = [x]
extractConsts (BinOp _ x y) = extractConsts y ++ extractConsts x
extractConsts _ = []

extractVars all@(Var _) = all:[]
extractVars (BinOp _ x y) = extractVars y ++ extractVars x
extractVars _ = []

mergeVars :: (Term -> Term -> Maybe Term) -> [Expr] -> [Expr]
mergeVars _ (x:[]) = [x]
mergeVars mergeFunc all@(vx@(Var x):vy@(Var y):[]) = case mergeFunc x y of
    Just merged -> [(Var merged)]
    Nothing -> all

mergeVars mergeFunc (vx@(Var x):vy@(Var y):xs) = case mergeFunc x y of
    Just merged -> mergeVars mergeFunc ((Var merged):xs)
    Nothing ->
        let (newY:newXS1) = mergeVars mergeFunc (vy:xs)
            (newX:newXS2) = mergeVars mergeFunc (vx:newXS1)
        in  (newX:newY:newXS2)

invertExpr (Const val) = (c (val ** (-1)))
invertExpr (Var term) = (var (invertTerm term))
invertExpr (BinOp op x y) = (BinOp op (invertExpr x) (invertExpr y))

-- Normalize
goesLeftOf (Var _) (Const _) = True
goesLeftOf (BinOp _ _ _) (Const _) = True
goesLeftOf (BinOp _ _ _) (Var _) = True
goesLeftOf (BinOp Mult _ _) (BinOp Add _ _) = True
goesLeftOf (BinOp Div _ _) (BinOp Add _ _) = True
goesLeftOf (Var (Term _ _ x)) (Var (Term _ _ y)) = y > x
goesLeftOf _ _ = False

solveNormalizeSquash all@(BinOp Add x y)
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
    | otherwise = all

solveNormalizeSquash all@(BinOp Mult x y)
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
    | otherwise = all

-- We normalize division by transforming it into a multiplication of negative exponents
solveNormalizeSquash all@(BinOp Div left right) = solveNormalize (BinOp Mult left (invertExpr right))

-- We want to squash single 0-mult terms with minimal code duplication
solveNormalizeSquash all@(Var _) = solveNormalizeSquash (mult all (c 1))

solveNormalizeSquash x = x

solveNormalizeSendLeft (BinOp op x y)
    | goesLeftOf y x = solveNormalizeSendLeft (BinOp op y x)
    | otherwise = (BinOp op (solveNormalizeSendLeft x) (solveNormalizeSendLeft y))

solveNormalizeSendLeft x = x

-- We never normalize Equal
solveNormalize (BinOp Equal x y) = (BinOp Equal (solveNormalize x) (solveNormalize y))

solveNormalize x
    | x == normalized = x
    | otherwise = solveNormalize normalized
    where normalized = solveNormalizeSendLeft (solveNormalizeSquash x)

-- solveReduceEqual: We send all variables to the left and all consts to the right

solveReduceEqualSendLeft left right (Var x) =
    let toadd = (var (negateTerm x))
        newleft = solve (add left toadd)
        newright = solve (add right toadd)
    in  equal newleft newright

solveReduceEqualSendLeft left right _ = equal left right

solveReduceEqual left right = solveReduceEqualSendLeft left right right


solveReduce (BinOp Equal left@(Const lx) right@(Const rx))
    | lx == rx = equal left right
    | otherwise = error "impossible equality!"

solveReduce (BinOp Equal x y) = solveReduceEqual (solveReduce x) (solveReduce y)
solveReduce (BinOp op x y) = BinOp op (solveReduce x) (solveReduce y)
solveReduce x = x

-- Solve
-- On commence par normaliser (mettre les termes et expression dans un ordre défini),
-- puis on réduit (fusionner des termes qui vont ensemble)

solve x = solveReduce (solveNormalize x)

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
    (equal (vs "x") (vi 2 "y"), "x + -2y = 0.0")]

testAll = [assertEq (show (solve expr)) expected | (expr, expected) <- testPairs]
