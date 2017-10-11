import Data.List
import Text.Printf

data BinaryOperator = Add | Subtract | Mult | Div | Equal deriving (Eq)

instance Show BinaryOperator where
    show Add = "+"
    show Subtract = "+"
    show Mult = "*"
    show Div = "/"
    show Equal = "="

data Expr =
    BinOp BinaryOperator Expr Expr |
    Var Double Int String
    deriving (Eq)

showBinOp fmt (BinOp op x y) = printf fmt (show x) (show op) (show y)

instance Show Expr where
    show (Var mult exp id) =
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

c x = (Var x 1 "")
vs x = vi 1 x
vi mx x = (Var mx 1 x)
add x y = (BinOp Add x y)
sub x y = (BinOp Subtract x y)
mult x y = (BinOp Mult x y)
div_ x y = (BinOp Div x y)
equal x y = (BinOp Equal x y)

-- https://stackoverflow.com/a/12868743
-- Returns if x is an int to n decimal places
isInt :: (Integral a, RealFrac b) => b -> a -> Bool
isInt x n = (round $ 10^(fromIntegral n)*(x-(fromIntegral $ round x)))==0

termName (Var _ _ termid) = termid

negateTerm (Var mx exp x) = (Var (-mx) exp x)

negateExpr v@(Var _ _ _) = (negateTerm v)
negateExpr (BinOp op x y) = (BinOp op (negateExpr x) (negateExpr y))

invertTerm (Var mx exp x) = (Var mx (-exp) x)

invertExpr v@(Var _ _ _) = (invertTerm v)
invertExpr (BinOp op x y) = (BinOp op (invertExpr x) (invertExpr y))


termConstVal (Var m exp tn)
    | m == 0 = Just 0
    | exp == 0 = Just 1
    | tn == "" = Just (m ** (fromIntegral exp))
    | otherwise = Nothing

isTermZero t = (termConstVal t) == Just 0
isTermOne t = (termConstVal t) == Just 1

addTerm t1@(Var mx expx x) t2@(Var my expy y) =
    case (termConstVal t1, termConstVal t2) of
        (Just val, _) -> (Just (Var (my + val) expy y))
        (_, Just val) -> (Just (Var (mx + val) expx x))
        _ -> if x == y && expx == expy then (Just (Var (mx + my) expy y))
            else Nothing

multTerm t1@(Var mx expx x) t2@(Var my expy y) =
    case (termConstVal t1, termConstVal t2) of
        (Just val, _) -> (Just (Var (my * val) expy y))
        (_, Just val) -> (Just (Var (mx * val) expx x))
        _ -> if x == y then (Just (Var (mx * my) (expx + expy) y))
            else Nothing

-- areOpsEqual: Returns whether our children expressions are either Var or of the same
-- op as `opRef`
areOpsEqual _ (Var _ _ _) = True
areOpsEqual opRef (BinOp op x y)
    | opRef == op = (areOpsEqual opRef x) && (areOpsEqual opRef y)
    | otherwise = False

applyBinOp_ op (x@(Var _ _ _):[]) current = BinOp op current x
applyBinOp_ op (x@(Var _ _ _):xs) current = BinOp op (applyBinOp_ op xs current) x

applyBinOp _ ([]) = (c 0)
applyBinOp _ (x@(Var _ _ _):[]) = x
applyBinOp op (x@(Var _ _ _):xs) = applyBinOp_ op xs x

extractVars all@(Var _ _ _) = all:[]
extractVars (BinOp _ x y) = extractVars x ++ extractVars y

mergeVars :: (Expr -> Expr -> Maybe Expr) -> [Expr] -> [Expr]
mergeVars _ (x:[]) = [x]
mergeVars mergeFunc all@(vx@(Var _ _ _):vy@(Var _ _ _):[]) = case mergeFunc vx vy of
    Just merged -> [merged]
    Nothing -> all

mergeVars mergeFunc (vx@(Var _ _ _):vy@(Var _ _ _):xs) = case mergeFunc vx vy of
    Just merged -> mergeVars mergeFunc (merged:xs)
    Nothing ->
        let (newX:newXS1) = mergeVars mergeFunc (vx:xs)
            (newY:newXS2) = mergeVars mergeFunc (vy:newXS1)
        in  (newX:newY:newXS2)

mapToBinOp f (BinOp op x y) = BinOp op (f x) (f y)
mapToBinOp f expr = f expr

-- Normalize
goesLeftOf (BinOp _ _ _) (Var _ _ _) = True
goesLeftOf (BinOp Mult _ _) (BinOp Add _ _) = True
goesLeftOf _ _ = False

normalizeSquash all@(BinOp Add x y)
    | areOpsEqual Add all =
        let vars = mergeVars addTerm (extractVars all)
            appliedVars = applyBinOp Add vars
        in  appliedVars
    | otherwise = mapToBinOp normalizeSquash all

normalizeSquash all@(BinOp Mult x y)
    | areOpsEqual Mult all =
        let vars = mergeVars multTerm (extractVars all)
            appliedVars = applyBinOp Mult vars
        in appliedVars
    | otherwise = mapToBinOp normalizeSquash all

-- We normalize subtraction by transforming it into an addition of negative terms
normalizeSquash all@(BinOp Subtract left right) = normalize (BinOp Add left (negateExpr right))

-- We normalize division by transforming it into a multiplication of negative exponents
normalizeSquash all@(BinOp Div left right) = normalize (BinOp Mult left (invertExpr right))

-- We want to squash single 0-mult terms with minimal code duplication
normalizeSquash all@(Var _ _ _) = normalizeSquash (mult all (c 1))

normalizeSquash x = x

normalizeSendLeft all@(BinOp op x y)
    | goesLeftOf y x = normalizeSendLeft (BinOp op y x)
    | otherwise = mapToBinOp normalizeSendLeft all

normalizeSendLeft x = x

-- purgeOfVar expr into varname: for each occurrence of "varname" in expr, add a negating binop
--                                 in both "expr" and "into" and returns (newexpr, newinto)
--                                 we expect expr to be normalized
purgeAddOfVar expr@(Var _ _ _) into varname
    | (termName expr) == varname =
        let toadd = (negateTerm expr)
            newexpr = (c 0)
            newinto = add into toadd
        in  (newexpr, newinto)
    | otherwise = (expr, into)

purgeAddOfVar expr into varname = purgeOfVar expr into varname

purgeMultOfVar expr@(Var _ _ _) into varname
    | (termName expr) == varname =
        let tomult = (invertTerm expr)
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

purgeOfVar expr@(Var _ exp _) into varname = 
    if exp > 0 then purgeAddOfVar expr into varname
    else purgeMultOfVar expr into varname

purgeOfVar expr into varname = (expr, into)
    
-- sendVarsLeftOfEqual: We send all variables to the left and all consts to the right

-- About vars sorting: we want to process variables with negative exponent first because we prefer
--                     ending up with a "= 0" equality than a "= 1" one. For example, "x = y / x"
--                     can end up either as "x^2 - y = 0" or as "x^2 / y = 1". We prefer the
--                     former.

sendVarsLeftOfEqual all@(BinOp Equal left right) = 
    let cmp (Var _ exp1 _) (Var _ exp2 _) = compare exp1 exp2
        vars = sortBy cmp (extractVars right)
        acc = (\(r, l) v@(Var _ _ _) -> purgeOfVar (normalize r) l (termName v))
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
            dividend = [v | v@(Var _ exp _) <- vars, exp >= 0] 
            divisors = [(Var mult (-exp) id) | (Var mult exp id) <- vars, exp < 0] 
            result =
                if null divisors then all
                else (BinOp Div (applyBinOp Mult dividend) (applyBinOp Mult divisors))
        in  result
    | otherwise = all

multToDiv (BinOp op x y) = (BinOp op (multToDiv x) (multToDiv y))

multToDiv all@(Var m exp tn)
    | m >= 1 || m <= (-1) = all
    | isInt (m ** (-1)) 3 = (div_ (Var 1 exp tn) (c (m ** (-1))))
    | otherwise = all

prettify = multToDiv


isolateDecompose left@(Var m _ _) right
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
