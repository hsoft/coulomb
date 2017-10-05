import Text.Printf

data Term = Term Double String

instance Show Term where
    show (Term mult id)
        | isint && isone = id
        | isint = printf "%0.0f%s" mult id
        | otherwise = printf "%0.2e%s" mult id
        where isint = isInt mult 3
              isone = isint && (round mult) == 1

instance Eq Term where
    Term mx x == Term my y = (x == y) && (mx == my)

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
vi mx x = (var (Term mx x))
add x y = (BinOp Add x y)
mult x y = (BinOp Mult x y)
div_ x y = (BinOp Div x y)
equal x y = (BinOp Equal x y)

-- https://stackoverflow.com/a/12868743
-- Returns if x is an int to n decimal places
isInt :: (Integral a, RealFrac b) => b -> a -> Bool
isInt x n = (round $ 10^(fromIntegral n)*(x-(fromIntegral $ round x)))==0

negateTerm (Term mx x) = (Term (-mx) x)

canMergeTerm x y = termIdent x == termIdent y

termIdent (Term _ x) = x

isTermNull (Term m _) = m <= 0.001 && m >= -0.001

addTerm (Term mx x) (Term my y) = (Term (mx + my) y)

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

mergeVars :: [Expr] -> [Expr]
mergeVars (x:[]) = [x]
mergeVars all@(vx:vy:[])
    | canMergeTerm x y = [(Var (addTerm x y))]
    | otherwise = all
    where ((Var x), (Var y)) = (vx, vy)

mergeVars (vx:vy:xs)
    | canMergeTerm x y = mergeVars ((Var (addTerm x y)):xs)
    | otherwise =
        let (newY:newXS1) = mergeVars (vy:xs)
            (newX:newXS2) = mergeVars (vx:newXS1)
        in  (newX:newY:newXS2)
    where ((Var x), (Var y)) = (vx, vy)

-- Normalize
goesLeftOf (Var _) (Const _) = True
goesLeftOf (BinOp _ _ _) (Const _) = True
goesLeftOf (BinOp _ _ _) (Var _) = True
goesLeftOf (BinOp Mult _ _) (BinOp Add _ _) = True
goesLeftOf (BinOp Div _ _) (BinOp Add _ _) = True
goesLeftOf (Var x) (Var y) = termIdent y > termIdent x
goesLeftOf _ _ = False

solveNormalizeSquash all@(BinOp Add x y)
    | exprDepth all > 1 && areOpsEqual Add all =
        let consts = sumConsts all
            vars = mergeVars (extractVars all)
            appliedVars = applyBinOp Add vars
        in  if consts /= 0.0 then (BinOp Add appliedVars (c consts)) else appliedVars
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
    (add (vs "x") (div_ (vs "x") (vs "y")), "(x / y) + x"),
    (equal (vs "x") (vi 2 "y"), "x + -2y = 0.0")]

testAll = [assertEq (show (solve expr)) expected | (expr, expected) <- testPairs]
