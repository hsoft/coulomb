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
    x < y = termMult x < termMult y
    x <= y = (termMult x == termMult y) || (termMult x < termMult y)

data BinaryOperator = Add | Mult | Equal

instance Show BinaryOperator where
    show Add = "+"
    show Mult = "*"
    show Equal = "="

instance Eq BinaryOperator where
    Add == Add = True
    Mult == Mult = True
    Equal == Equal = True
    _ == _ = False

instance Ord BinaryOperator where
    Add < Mult = True
    Add < Equal = True
    Mult < Equal = True
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
    show (BinOp Equal x y) = printf "%s %s %s" (show x) (show Equal) (show y)
    show (BinOp op x@(BinOp op1 _ _) y@(BinOp op2 _ _))
        | (op1 == op) && (op2 == op) = printf "%s %s %s" (show x) (show op) (show y)
        | op1 == op = printf "%s %s (%s)" (show x) (show op) (show y)
        | op2 == op = printf "(%s) %s %s" (show x) (show op) (show y)
        | otherwise = printf "(%s) %s (%s)" (show x) (show op) (show y)
    show (BinOp op x@(BinOp op1 _ _) y)
        | op1 == op = printf "%s %s %s" (show x) (show op) (show y)
        | otherwise = printf "(%s) %s %s" (show x) (show op) (show y)
    show (BinOp op x y@(BinOp op2 _ _))
        | op2 == op = printf "%s %s %s" (show x) (show op) (show y)
        | otherwise = printf "(%s) %s %s" (show x) (show op) (show y)
    show (BinOp op x y) = printf "%s %s %s" (show x) (show op) (show y)

data MergeResult = Merged Expr | NotMerged

c x = (Const x)
var t = if isTermNull t then c 0 else (Var t)
vs x = (var (TermS x))
vi mx x = (var (TermI mx x))
add x y = (BinOp Add x y)
equal x y = (BinOp Equal x y)

negateTerm (TermS x) = (TermI (-1) x)
negateTerm (TermI mx x) = (TermI (-mx) x)
negateTerm (TermF mx x) = (TermF (-mx) x)

canMergeTerm (TermS x) (TermS y) = x == y
canMergeTerm (TermS x) (TermI _ y) = x == y
canMergeTerm (TermS x) (TermF _ y) = x == y
canMergeTerm (TermI _ x) (TermI _ y) = x == y
canMergeTerm (TermI _ x) (TermF _ y) = x == y
canMergeTerm (TermF _ x) (TermF _ y) = x == y
canMergeTerm x y = canMergeTerm y x

termIdent (TermS x) = x
termIdent (TermI _ x) = x
termIdent (TermF _ x) = x

termMult (TermS _) = 1
termMult (TermI m _) = fromIntegral m
termMult (TermF m _) = m

isTermNull (TermI m _) = m == 0
isTermNull (TermF m _) = m == 0.0
isTermNull _ = False

addTerm (TermS x) (TermS y) = (TermI 2 y)
addTerm (TermS x) (TermI my y) = (TermI (my + 1) y)
addTerm (TermS x) (TermF my y) = (TermF (my + 1) y)
addTerm (TermI mx x) (TermI my y) = (TermI (mx + my) y)
addTerm (TermI mx x) (TermF my y) = (TermF ((fromIntegral mx) + my) y)
addTerm (TermF mx x) (TermF my y) = (TermF (mx + my) y)
addTerm x y = addTerm y x

-- Normalize
goesLeftOf (Var _) (Const _) = True
goesLeftOf (BinOp _ _ _) (Const _) = True
goesLeftOf (BinOp _ _ _) (Var _) = True
goesLeftOf (BinOp Mult _ _) (BinOp Add _ _) = True
goesLeftOf (Var x) (Var y) = termIdent y > termIdent x
goesLeftOf _ _ = False

solveNormalizeSendLeft (BinOp Add (Const x) (Const y)) = Const (x+y)
solveNormalizeSendLeft (BinOp Mult (Const x) (Const y)) = Const (x*y)

solveNormalizeSendLeft (BinOp op x y)
    | goesLeftOf y x = solveNormalizeSendLeft (BinOp op y x)
    | otherwise = (BinOp op (solveNormalizeSendLeft x) (solveNormalizeSendLeft y))

solveNormalizeSendLeft x = x

-- We never normalize Equal
solveNormalize (BinOp Equal x y) = (BinOp Equal (solveNormalize x) (solveNormalize y))

solveNormalize x
    | x == normalized = x
    | otherwise = solveNormalize normalized
    where normalized = solveNormalizeSendLeft x

-- Reduce

solveAddMerge tofind (Var x)
    | canMergeTerm tofind x = Merged (var (addTerm tofind x))
    | otherwise = NotMerged

solveAddMerge tofind (BinOp Add x y) =
    case solveAddMerge tofind x of
        Merged newx -> Merged (BinOp Add newx y)
        NotMerged ->
            case solveAddMerge tofind y of
                Merged newy -> Merged (BinOp Add x newy)
                NotMerged -> NotMerged

solveReduceAdd all@(BinOp Add (Var x) (Var y))
    | canMergeTerm x y = (var (addTerm x y))
    | otherwise = all

solveReduceAdd all@(BinOp Add addExpr@(BinOp Add _ _) (Var x)) =
    case solveAddMerge x addExpr of
        Merged newExpr -> solveReduceAdd newExpr
        NotMerged -> all

solveReduceAdd x = x

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

solveReduce (BinOp Add x y) = solveReduceAdd (BinOp Add (solveReduce x) (solveReduce y))
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
    ((show (solve (add (add (vs "x") (vs "y")) (vs "x")))), "2x + y"),
    ((show (solve (equal (vs "x") (vi 2 "y")))), "x + -2y = 0.0")]

testAll = map (uncurry assertEq) testPairs
