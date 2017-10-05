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

data Expr =
    Mult Expr Expr |
    Add Expr Expr |
    Var Term |
    Const Float
    deriving (Eq)

instance Show Expr where
    show (Var x) = show x
    show (Const x) = show x
    show (Add x y) = printf "(%s + %s)" (show x) (show y)
    show (Mult x y) = printf "(%s * %s)" (show x) (show y)

instance Ord Expr where
    Const x < Const y = x < y
    Var x < Var y = x < y
    Add x1 x2 < Add y1 y2 = (x1 <= y1) && (x2 < y2)
    Mult x1 x2 < Mult y1 y2 = (x1 <= y1) && (x2 < y2)

    Const _ < Var _ = True
    Const _ < Add _ _ = True
    Const _ < Mult _ _ = True

    Var _ < Add _ _ = True
    Var _ < Mult _ _ = True

    Add _ _ < Mult _ _ = True

    x <= y = (x == y) || (x < y)

vs x = (Var (TermS x))
vi mx x = (Var (TermI mx x))

canMergeTerm (TermS x) (TermS y) = x == y
canMergeTerm (TermS x) (TermI _ y) = x == y
canMergeTerm (TermS x) (TermF _ y) = x == y
canMergeTerm (TermI _ x) (TermI _ y) = x == y
canMergeTerm (TermI _ x) (TermF _ y) = x == y
canMergeTerm (TermF _ x) (TermF _ y) = x == y
canMergeTerm x y = canMergeTerm y x

mergeTerm (TermS x) (TermS y) = (TermI 2 y)
mergeTerm (TermS x) (TermI my y) = (TermI (my + 1) y)
mergeTerm (TermS x) (TermF my y) = (TermF (my + 1) y)
mergeTerm (TermI mx x) (TermI my y) = (TermI (mx + my) y)
mergeTerm (TermI mx x) (TermF my y) = (TermF ((fromIntegral mx) + my) y)
mergeTerm (TermF mx x) (TermF my y) = (TermF (mx + my) y)
mergeTerm x y = mergeTerm y x

-- Norm1: normalize "horizontally"
solveNorm1 (Add (Const x) (Const y)) = Const (x+y)

solveNorm1 (Add x y)
    | y > x = solveNorm1 (Add y x)
    | otherwise = (Add (solveNorm1 x) (solveNorm1 y))

solveNorm1 x = x

-- Norm2: normalize "vertically"

solveNorm2 all@(Add (Add inner1 inner2) outer)
    | inner1 > outer = (Add (Add outer inner2) inner1)
    | otherwise = all

solveNorm2 x = x

solveNormalize x
    | x == normalized = x
    | otherwise = solveNormalize normalized
    where normalized = solveNorm2 (solveNorm1 x)

solveReduceAdd all@(Add (Var x) (Var y))
    | canMergeTerm x y = (Var (mergeTerm x y))
    | otherwise = all

solveReduceAdd x = x

solveReduce (Add x y) = solveReduceAdd (Add (solveReduce x) (solveReduce y))
solveReduce x = x

solve x = solveReduce (solveNormalize x)

-- tests

assertEq a b
    | a == b = ()
    | otherwise = error (printf "%s != %s" a b)

testPairs = [
    ((show (solve (Add (Add (vs "x") (vs "y")) (vs "x")))), "(2x + y)")]

testAll = map (uncurry assertEq) testPairs
