module Interpreter (reduce) where

import Data.List (nub)

type Id = String

data Term
  = Var Id -- Variables
  | Abs Id Term -- Abstractions
  | App Term Term -- Applications
  deriving (Eq)

instance Show Term where
  show (Var varName) = varName
  show (Abs varName term) = "(%" ++ varName ++ ". " ++ show term ++ ")"
  show (App term1 term2) = show term1 ++ " " ++ show term2

-- ----- Test Values -----
testLambda1 = App (Abs "x" (Abs "y" (App (Var "x") (Var "y")))) (Var "y")
-- >>> testLambda1
-- (%x. (%y. x y)) y
testLambda2 = App (App (Abs "x" (Var "x")) (Var "a")) (App (Abs "y" (Var "y")) (Var "b"))
-- >>> testLambda2
-- (%x. x) a (%y. y) b
testLambda3 = App (App (Abs "x" (Var "x")) (Var "b")) (App (Abs "y" (Var "y")) (Var "b"))
-- >>> testLambda3
-- (%x. x) a (%y. y) b
testLambda4 = Abs "x" (App (Var "a") (Var "b"))
-- >>> testLambda4
-- (%x. a b)
testLambda5 = App (Abs "x" (Var "x")) (Var "a")
-- >>> testLambda5
-- (%x. x) a
testLambda6 = Abs "x" (Abs "y" (Var "x"))
-- >>> testLambda6
-- (%x. (%y. x))


-- ----- END -----


-- ----- Example Usage -----
-- `(λx.x) a` reduces to `a`
-- reduce (App (Abs "x" (Var "x")) (Var "a")) == (Var "a")
-- True

-- `(λx.x x) (λx.x)` reduces to `λx.x`
-- reduce (App (Abs "x" (App (Var "x") (Var "x"))) (Abs "x" (Var "x"))) == (Abs "x" (Var "x"))
-- True
-- ----- END -----

-- Implement a function freeVars t that returns a set of all free variables within a lambda term t.
-- You may want to represent sets as lists without duplicates.
-- Appendix A.2 of the lecture notes contains recursive definitions of non-freeness that you may find useful.
freeVars :: Term -> [Id]
freeVars term = freeVarsImpl term []

-- Implementation. Done in order to avoid passing an empty array on each invocation
freeVarsImpl :: Term -> [Id] -> [Id]
freeVarsImpl (Var varName) nonFreeVars = if elem varName nonFreeVars then [] else [varName]
freeVarsImpl (Abs varName term) nonFreeVars = freeVarsImpl term (nonFreeVars ++ [varName])
freeVarsImpl (App term1 term2) nonFreeVars = freeVarsImpl term1 nonFreeVars ++ freeVarsImpl term2 nonFreeVars

boundVars :: Term -> [Id]
boundVars term = nub (boundVarsImpl term)

boundVarsImpl :: Term -> [Id]
boundVarsImpl (Var varName) = []
boundVarsImpl (Abs varName term) = varName : boundVarsImpl term
boundVarsImpl (App term1 term2) = boundVarsImpl term1 ++ boundVarsImpl term2

-- >>> freeVars (App (Abs "x" (Var "x")) (Var "a"))
-- ["a"]

-- that replaces all free occurrences of the variable x within the term t with the term tx.
-- Take care to avoid capturing substitutions (you will have to do some alpha renaming with fresh variables to avoid this).
-- Appendix A.2 of the lecture notes contains a recursive definition of substitution that you may find useful.
-- In case you find the task of avoiding variable capture too challenging, skip this and only use terms with
-- unique bound and free variable names
-- substitute (x,tx) t = undefined
substitute :: (Term, Term) -> Term -> Term
substitute (Var toReplace, Var newValue) term =
  if isSubOldVar toReplace term && isSubNewVar newValue term then substituteImpl (Var toReplace, Var newValue) term else term
substitute _ term = term

substituteImpl :: (Term, Term) -> Term -> Term
substituteImpl (Var toReplace, Var newValue) (Var givenVarName) =
  if givenVarName == toReplace then Var newValue else Var givenVarName
substituteImpl (Var toReplace, Var newValue) (Abs givenVarName term) =
  Abs (if givenVarName == toReplace then newValue else givenVarName) (substituteImpl (Var toReplace, Var newValue) term)
substituteImpl (Var toReplace, Var newValue) (App term1 term2) =
  App (substituteImpl (Var toReplace, Var newValue) term1) (substituteImpl (Var toReplace, Var newValue) term2)
substituteImpl _ term = term


-- Is substitutionable if var is free or bound or none
isSubOldVar :: Id -> Term -> Bool
isSubOldVar id term = not (elem id (boundVars term) && elem id (freeVars term))

-- Is substitutionable if var is neither free nor bound
isSubNewVar :: Id -> Term -> Bool
isSubNewVar id term = not (elem id (boundVars term) || elem id (freeVars term))

-- >>> testLambda2
-- (%x. (%y. x y)) y
-- >>> substitute (Var "x", Var "y") testLambda2
-- (%y. (%y. y y)) y

-- >>> substitute2 (Var "x", Var "y") testLambda2
-- (%x. (%y. x y)) y

-- >>> substitute (Var "y", Var "a") testLambda2
-- (%x. (%a. x a)) a

-- >>> testLambda4
-- (%x. x) b (%y. y) b
-- >>> substitute (Var "b", Var "y") testLambda4
-- (%x. x) y (%y. y) y

-- >>> substitute (Var "b", Var "y") testLambda3
-- (%x. x) a (%y. y) y

-- >>> substitute (Var "x", Var "y") testLambda
-- (%y. y) a

-- Returns True if the top level of the term t is a beta redex.
isBetaRedex :: Term -> Bool
isBetaRedex (Var varName) = False
isBetaRedex (Abs varName term) = True
isBetaRedex (App term1 term2) = True

-- (λx. g x) ((λy. g y) 5)
--
-- `(λx.x) a`
-- (App (Abs "x" (Var "x")) (Var "a"))
-- Use substitute to implement a function betaReduce t that applies a beta reduction to top level of the term t.
betaReduce :: Term -> Term
betaReduce (Var name) = Var name
betaReduce (Abs varName term) = betaReduce term
betaReduce (App (Abs toReplace term) termToBePut) = substitute2 (toReplace, termToBePut) term
betaReduce term = term


-- >>> reduce testLambda5
-- a
-- >>> reduce testLambda4
-- ProgressCancelledException

reduce :: Term -> Term
reduce term 
  | isBetaRedex term = reduce (betaReduce term)
  | otherwise = term 

-- >>> testLambda1
-- (%x. (%y. x y)) y

-- >>> isNonFree "y" testLambda1
-- False


-- returns true if the given var is not used a free var in the given term
isNonFree :: Id -> Term -> Bool
isNonFree toCheck (Var varName) = toCheck /= varName
isNonFree toCheck (Abs varName term) 
  | toCheck == varName = True
  | otherwise = isNonFree toCheck term
isNonFree toCheck (App term1 term2) = isNonFree toCheck term1 && isNonFree toCheck term2


-- substitute (x,tx) t that replaces all free occurrences of the variable x within the term t with the term tx
substitute2 :: (Id, Term) -> Term -> Term
substitute2 (x, termL) (Var y)
  | x == y = termL
  | otherwise = Var y
substitute2 (x, termL) (Abs y termM)
  | x == y = Abs y termM
  | isNonFree y termL = Abs y (substitute2 (x, termL) termM)
  | otherwise = undefined -- here is some alpha conversion needed
substitute2 (x, termL) (App termM termN) = App (substitute2 (x, termL) termM) (substitute2 (x, termL) termN)
