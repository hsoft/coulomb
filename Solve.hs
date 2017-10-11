import Data.List
import Text.Printf

data Term = Term Double Int String deriving (Eq)

instance Show Term where
    show (Term mult exp id) =
        let isint = isInt mult 3
            higherThanMilli = mult > (1 / 1000)
            prefix = case (isint, higherThanMilli, round mult) of
                (True, _, 1) -> ""
                (True, _, (-1)) -> "-"
                (True, _, _) -> printf "%0.0f" mult
                (False, True, _) -> printf "%1.2f" mult
                (False, False, _) -> printf "%0.2e" mult
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
    show (Const x) = if isInt x 3 then show (round x) else show x

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

termName (Term _ _ termid) = termid

negateTerm (Term mx exp x) = (Term (-mx) exp x)

negateExpr (Const val) = (c (val * (-1)))
negateExpr (Var term) = (var (negateTerm term))
negateExpr (BinOp op x y) = (BinOp op (negateExpr x) (negateExpr y))

invertTerm (Term mx exp x) = (Term mx (-exp) x)

invertExpr (Const val) = (c (val ** (-1)))
invertExpr (Var term) = (var (invertTerm term))
invertExpr (BinOp op x y) = (BinOp op (invertExpr x) (invertExpr y))


isTermZero (Term m _ _) = m <= 0.001 && m >= -0.001
isTermOne (Term _ exp _) = exp == 0

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

applyBinOp _ ([]) = (c 0)
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
            appliedVars = applyBinOp Add filteredTerms
        in  case constsValIsNeutral of
            True -> appliedVars
            False -> (add appliedVars (c (sum consts)))
    | otherwise = mapToBinOp normalizeSquash all

normalizeSquash (BinOp Mult (Var (Term m exp tn)) (Const cval))
    | cval == 0 = (c 0)
    | otherwise = (Var (Term (m * cval) exp tn))

normalizeSquash all@(BinOp Mult x y)
    | areOpsEqual Mult all =
        let consts = extractConsts all
            constsVal = foldl (*) 1 consts
            constsValIsNeutral = constsVal == 1
            vars = mergeVars multTerm (extractVars all)
            terms = [t | (Var t) <- vars]
            filteredTerms = filter (\x -> not (isTermOne x)) terms
            exprNullified = constsVal == 0 || (not (null (filter isTermZero terms)))
            appliedVars = applyBinOp Mult filteredTerms
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

-- purgeOfVar expr into varname: for each occurrence of "varname" in expr, add a negating binop
--                                 in both "expr" and "into" and returns (newexpr, newinto)
--                                 we expect expr to be normalized
purgeAddOfVar expr@(Var t) into varname
    | (termName t) == varname =
        let toadd = (var (negateTerm t))
            newexpr = (c 0)
            newinto = add into toadd
        in  (newexpr, newinto)
    | otherwise = (expr, into)

purgeAddOfVar expr into varname = purgeOfVar expr into varname

purgeMultOfVar expr@(Var t) into varname
    | (termName t) == varname =
        let tomult = (var (invertTerm t))
            newexpr = (c 1)
            newinto = mult into tomult
        in  (newexpr, newinto)
    | otherwise = (expr, into)

purgeMultOfVar expr into varname = purgeOfVar expr into varname

purgeOfVar expr@(BinOp Add left right) into varname =
    let (exprLeft, intoLeft) = purgeAddOfVar left into varname
        (exprRight, intoRight) = purgeAddOfVar right intoLeft varname
    in ((add exprLeft exprRight), intoRight)

purgeOfVar expr@(BinOp Mult left right) into varname =
    let (exprLeft, intoLeft) = purgeMultOfVar left into varname
        (exprRight, intoRight) = purgeMultOfVar right intoLeft varname
    in ((mult exprLeft exprRight), intoRight)

purgeOfVar expr@(Var t) into varname = 
    let (Term _ exp _) = t
    in  if exp > 0 then purgeAddOfVar expr into varname
        else purgeMultOfVar expr into varname

purgeOfVar expr into varname = (expr, into)
    
-- sendVarsLeftOfEqual: We send all variables to the left and all consts to the right

sendVarsLeftOfEqual all@(BinOp Equal (Const lx) (Const rx))
    | lx == rx = all
    | otherwise = error "impossible equality!"

-- About vars sorting: we want to process variables with negative exponent first because we prefer
--                     ending up with a "= 0" equality than a "= 1" one. For example, "x = y / x"
--                     can end up either as "x^2 - y = 0" or as "x^2 / y = 1". We prefer the
--                     former.

sendVarsLeftOfEqual all@(BinOp Equal left right) = 
    let cmp (Var (Term _ exp1 _)) (Var (Term _ exp2 _)) = compare exp1 exp2
        vars = sortBy cmp (extractVars right)
        acc = (\(r, l) (Var t) -> purgeOfVar (normalize r) l (termName t))
        (newright, newleft) = foldl acc (right, left) vars
    in  equal (normalize newleft) (normalize newright)

sendVarsLeftOfEqual x = x

-- Equal is normalized differently
normalize all@(BinOp Equal x y) = 
    let left = normalize x
        right = normalize y
    in sendVarsLeftOfEqual (equal left right)

normalize x
    | x == normalized = x
    | otherwise = normalize normalized
    where normalized = normalizeSendLeft (normalizeSquash x)


-- Prettify

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

multToDiv all@(Var (Term m exp tn))
    | m >= 1 || m <= (-1) = all
    | isInt (m ** (-1)) 3 = (div_ (Var (Term 1 exp tn)) (c (m ** (-1))))
    | otherwise = all

multToDiv x = x

prettify = multToDiv


isolateDecompose left@(Var (Term m _ _)) right
    | m == 1 = (left, right)
    | otherwise =
        let inverter = (c (m ** (-1)))
            newleft = mult left inverter
            newright = mult right inverter
        in  (newleft, newright)

isolate (BinOp Equal left right) varname =
    let (newright1, newleft1) = purgeOfVar left right varname
        (newleft2, newright2) = isolateDecompose (normalize newleft1) newright1
    in  (equal (normalize newleft2) (normalize newright2))

-- tests

assertEq a b
    | a == b = ()
    | otherwise = error (printf "%s != %s" a b)

testPairsNormalize = [
    (add (add (vs "x") (vs "y")) (vs "x"), "2x + y"),
    (add (vs "x") (mult (vs "x") (vs "y")), "(x * y) + x"),
    (mult (vs "x") (vs "x"), "x^2"),
    (mult (vs "x") (c 0), "0"),
    (div_ (mult (vs "x") (vs "x")) (vs "x"), "x"),
    (add (vs "x") (div_ (vs "x") (vs "y")), "(x / y) + x"),
    (sub (vs "x") (vs "y"), "x + -y"),
    (equal (vs "x") (vi 2 "y"), "x + -2y = 0"),
    (equal (vs "x") (div_ (vi 2 "y") (vs "x")), "x^2 + -2y = 0")]

testNormalize = [assertEq (show ((prettify . normalize) expr)) expected | (expr, expected) <- testPairsNormalize]

testTriplesIsolate = [
    (equal (vs "x") (div_ (vi 2 "y") (vs "x")), "y", "y = x^2 / 2")]

testIsolate = [assertEq (show (prettify (isolate (normalize expr) varname))) expected | (expr, varname, expected) <- testTriplesIsolate]
