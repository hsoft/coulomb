import Text.Printf

data Term = TermS String | TermI Int String | TermF Float String

instance Show Term where
    show (TermS id) = id
    show (TermI mult id) = printf "%d%s" mult id
    show (TermF mult id) = printf "%0.2e%s" mult id

instance Eq Term where
    TermS x == TermS y = x == y
    TermI mx x == TermI my y = (x == y) && (mx == my)
    TermF mx x == TermF my y = (x == y) && (mx == my)
    TermS x == TermI my y = (x == y) && (my == 1)
    _ == _ = False

instance Ord Term where
    TermS x < TermS y = x < y
    TermI _ x < TermI _ y = x < y
    TermF _ x < TermF _ y = x < y
    x <= y = (x == y) || (x < y)

data BinaryOperator = Add | Mult

instance Show BinaryOperator where
    show Add = "+"
    show Mult = "*"

instance Eq BinaryOperator where
    Add == Add = True
    Mult == Mult = True
    _ == _ = False

instance Ord BinaryOperator where
    Add < Mult = True
    _ < _ = False
    x <= y = (x == y) || (x < y)

data Expr =
    BinOp BinaryOperator Expr Expr |
    Var Term |
    Const Float
    deriving (Eq)

instance Show Expr where
    show (Var x) = show x
    show (Const x) = show x
    show (BinOp op x y) = printf "(%s %s %s)" (show x) (show op) (show y)

instance Ord Expr where
    Const x < Const y = x < y
    Var x < Var y = x < y
    BinOp xOp x1 x2 < BinOp yOp y1 y2 = (xOp <= yOp) && (x1 <= y1) && (x2 < y2)

    Const _ < Var _ = True
    Const _ < BinOp _ _ _ = True

    Var _ < BinOp _ _ _ = True

    x <= y = (x == y) || (x < y)

vs x = (Var (TermS x))
vi mx x = (Var (TermI mx x))
add x y = (BinOp Add x y)

canMergeTerm (TermS x) (TermS y) = x == y
canMergeTerm (TermS x) (TermI _ y) = x == y
canMergeTerm (TermS x) (TermF _ y) = x == y
canMergeTerm (TermI _ x) (TermI _ y) = x == y
canMergeTerm (TermI _ x) (TermF _ y) = x == y
canMergeTerm (TermF _ x) (TermF _ y) = x == y
canMergeTerm x y = canMergeTerm y x

addTerm (TermS x) (TermS y) = (TermI 2 y)
addTerm (TermS x) (TermI my y) = (TermI (my + 1) y)
addTerm (TermS x) (TermF my y) = (TermF (my + 1) y)
addTerm (TermI mx x) (TermI my y) = (TermI (mx + my) y)
addTerm (TermI mx x) (TermF my y) = (TermF ((fromIntegral mx) + my) y)
addTerm (TermF mx x) (TermF my y) = (TermF (mx + my) y)
addTerm x y = addTerm y x

-- Norm1: normalize "horizontally"
solveNorm1 (BinOp Add (Const x) (Const y)) = Const (x+y)
solveNorm1 (BinOp Mult (Const x) (Const y)) = Const (x*y)

solveNorm1 (BinOp op x y)
    | y > x = solveNorm1 (BinOp op y x)
    | otherwise = (BinOp op (solveNorm1 x) (solveNorm1 y))

solveNorm1 x = x

-- Norm2: normalize "vertically"

solveNorm2 all@(BinOp opOuter (BinOp opInner inner1 inner2) outer)
    | (opInner == opOuter) && (inner1 > outer) =
        (BinOp opOuter (BinOp opInner outer inner2) inner1)
    | otherwise = all

solveNorm2 x = x

solveNormalize x
    | x == normalized = x
    | otherwise = solveNormalize normalized
    where normalized = solveNorm2 (solveNorm1 x)

solveReduceAdd all@(BinOp Add (Var x) (Var y))
    | canMergeTerm x y = (Var (addTerm x y))
    | otherwise = all

solveReduceAdd x = x

solveReduce (BinOp Add x y) = solveReduceAdd (BinOp Add (solveReduce x) (solveReduce y))
solveReduce x = x

solve x = solveReduce (solveNormalize x)

-- tests

assertEq a b
    | a == b = ()
    | otherwise = error (printf "%s != %s" a b)

testPairs = [
    ((show (solve (add (add (vs "x") (vs "y")) (vs "x")))), "(2x + y)")]

testAll = map (uncurry assertEq) testPairs
