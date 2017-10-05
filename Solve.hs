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
            suffix = if exp > 1 then "^" ++ (show exp) else ""
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

data MergeResult = Merged Expr | NotMerged

c x = (Const x)
var t = if isTermNull t then c 0 else (Var t)
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

canMergeTerm (Term _ expx x) (Term _ expy y) = x == y && expx == expy

isTermNull (Term m _ _) = m <= 0.001 && m >= -0.001

addTerm (Term mx expx x) (Term my expy y)
    | x == y && expx == expy = (Term (mx + my) expy y)
    | otherwise = error "Can't merge term!"

multTerm (Term mx expx x) (Term my expy y)
    | x == y = (Term (mx * my) (expx + expy) y)
    | otherwise = error "Can't merge term!"

exprDepth (BinOp _ x y) = (max (exprDepth x) (exprDepth y)) + 1
exprDepth _ = 1

-- areOpsEqual: Returns whether our children expressions are either Const, Var or of the same
-- op as `opRef`
areOpsEqual _ (Const _) = True
areOpsEqual _ (Var _) = True
areOpsEqual opRef (BinOp op x y)
    | opRef == op = (areOpsEqual opRef x) && (areOpsEqual opRef y)
    | otherwise = False

applyBinOp _ (vx@(Var x):[])
    | isTermNull x = c 0
    | otherwise = vx
applyBinOp op (vx@(Var x):xs)
    | isTermNull x = expr
    | otherwise = BinOp op expr vx
    where expr = applyBinOp op xs

sumConsts :: Expr -> Double
sumConsts (Const x) = x
sumConsts (BinOp _ x y) = sumConsts y + sumConsts x
sumConsts _ = 0.0

extractVars all@(Var _) = all:[]
extractVars (BinOp _ x y) = extractVars y ++ extractVars x
extractVars _ = []

mergeVars :: (Term -> Term -> Term) -> [Expr] -> [Expr]
mergeVars _ (x:[]) = [x]
mergeVars mergeFunc all@(vx:vy:[])
    | canMergeTerm x y = [(Var (mergeFunc x y))]
    | otherwise = all
    where ((Var x), (Var y)) = (vx, vy)

mergeVars mergeFunc (vx:vy:xs)
    | canMergeTerm x y = mergeVars mergeFunc ((Var (mergeFunc x y)):xs)
    | otherwise =
        let (newY:newXS1) = mergeVars mergeFunc (vy:xs)
            (newX:newXS2) = mergeVars mergeFunc (vx:newXS1)
        in  (newX:newY:newXS2)
    where ((Var x), (Var y)) = (vx, vy)

-- Normalize
goesLeftOf (Var _) (Const _) = True
goesLeftOf (BinOp _ _ _) (Const _) = True
goesLeftOf (BinOp _ _ _) (Var _) = True
goesLeftOf (BinOp Mult _ _) (BinOp Add _ _) = True
goesLeftOf (BinOp Div _ _) (BinOp Add _ _) = True
goesLeftOf (Var (Term _ _ x)) (Var (Term _ _ y)) = y > x
goesLeftOf _ _ = False

solveNormalizeSquash all@(BinOp op x y)
    | (op == Add || op == Mult) && exprDepth all > 1 && areOpsEqual op all =
        let consts = sumConsts all
            mergeFunc = case op of
                Add -> addTerm
                Mult -> multTerm
            vars = mergeVars mergeFunc (extractVars all)
            appliedVars = applyBinOp op vars
        in  if consts /= 0.0 then (BinOp op appliedVars (c consts)) else appliedVars
    | otherwise = all

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
    (add (vs "x") (div_ (vs "x") (vs "y")), "(x / y) + x"),
    (equal (vs "x") (vi 2 "y"), "x + -2y = 0.0")]

testAll = [assertEq (show (solve expr)) expected | (expr, expected) <- testPairs]
