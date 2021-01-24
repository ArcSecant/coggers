module W where

import Prelude hiding ((<>))

import qualified Data.Map as Map
import Data.Set ((\\))
import qualified Data.Set as Set

import Control.Monad.Except
import Control.Monad.State

import Text.PrettyPrint

data Exp
    = EVar String
    | ELit Lit
    | EApp Exp Exp
    | ELam String Exp
    | ELet String Exp Exp
    deriving (Eq, Ord)

data Lit
    = LInt Integer
    | LBool Bool
    deriving (Eq, Ord)

data Type
    = TVar String
    | TInt
    | TBool
    | TFun Type Type -- fun :: a -> b
    deriving (Eq, Ord)

data Scheme = Scheme [String] Type

class Types a where
    freeTypeVars :: a -> Set.Set String -- get free types
    applySubst :: Substitutions -> a -> a -- substitute type

instance Types Type where
    freeTypeVars (TVar n) = Set.singleton n
    freeTypeVars TInt = Set.empty
    freeTypeVars TBool = Set.empty
    freeTypeVars (TFun t1 t2) = Set.union (freeTypeVars t1) (freeTypeVars t2)

    applySubst s (TVar n) = case Map.lookup n s of
        Nothing -> TVar n
        Just t -> t
    applySubst s (TFun t1 t2) = TFun (applySubst s t1) (applySubst s t2)
    applySubst _ t = t

instance Types Scheme where
    freeTypeVars (Scheme vars t) = freeTypeVars t \\ Set.fromList vars
    applySubst s (Scheme vars t) = Scheme vars (applySubst (foldr Map.delete s vars) t)

instance Types a => Types [a] where
    applySubst s = map (applySubst s)
    freeTypeVars l = foldr (Set.union . freeTypeVars) Set.empty l

type Substitutions = Map.Map String Type

nullSubst :: Substitutions
nullSubst = Map.empty

composeSubst :: Substitutions -> Substitutions -> Substitutions
composeSubst s1 s2 = Map.map (applySubst s1) s2 `Map.union` s1

newtype TypeEnv = TypeEnv (Map.Map String Scheme)

remove :: TypeEnv -> String -> TypeEnv
remove (TypeEnv env) var = TypeEnv (Map.delete var env)

instance Types TypeEnv where
    freeTypeVars (TypeEnv env) = freeTypeVars (Map.elems env)
    applySubst s (TypeEnv env) = TypeEnv (Map.map (applySubst s) env)

generalize :: TypeEnv -> Type -> Scheme
generalize env t = Scheme vars t
  where
    vars = Set.toList (freeTypeVars t \\ freeTypeVars env)

data TIState = TIState
    { tiSupply :: Int
    , tiSubst :: Substitutions
    }

type TI a = ExceptT String (StateT TIState IO) a

runTI :: TI a -> IO (Either String a, TIState)
runTI t = do
    (res, st) <- runStateT (runExceptT t) initTIState
    return (res, st)
  where
    initTIState =
        TIState
            { tiSupply = 0
            , tiSubst = Map.empty
            }

newTypeVar :: String -> TI Type
newTypeVar prefix = do
    s <- get
    put s{tiSupply = tiSupply s + 1}
    return (TVar (prefix ++ show (tiSupply s)))

-- replaces bound variable names with x1, x2, ...
instantiate :: Scheme -> TI Type
instantiate (Scheme vars t) = do
    nvars <- mapM (\_ -> newTypeVar "a") vars
    let s = Map.fromList (zip vars nvars)
    return (applySubst s t)

unify :: Type -> Type -> TI Substitutions
unify (TFun l r) (TFun l' r') = do
    s1 <- unify l l'
    s2 <- unify (applySubst s1 r) (applySubst s1 r')
    return (s2 `composeSubst` s1)
unify (TVar u) t = varBind u t
unify t (TVar u) = varBind u t
unify TInt TInt = return nullSubst
unify TBool TBool = return nullSubst
unify t1 t2 = throwError ("types do not unify: " ++ show t1 ++ " and " ++ show t2)

varBind :: String -> Type -> TI Substitutions
varBind u t
    | t == TVar u = return nullSubst
    | u `Set.member` freeTypeVars t = throwError ("occur check fails: " ++ u ++ " and " ++ show t)
    | otherwise = return (Map.singleton u t)

-- Inference
ti :: TypeEnv -> Exp -> TI Type
ti (TypeEnv env) (EVar n) = case Map.lookup n env of
    Nothing -> throwError ("unbound variable" ++ n)
    Just sigma -> do instantiate sigma
ti env (ELit l) = tiLit env l
ti env (ELam n e) = do
    tv <- newTypeVar "a"
    let TypeEnv env' = remove env n
        env'' = TypeEnv (env' `Map.union` Map.singleton n (Scheme [] tv))
    t2 <- ti env'' e
    s <- get
    let t1 = applySubst (tiSubst s) tv
    return (TFun t1 t2)
ti env (EApp e1 e2) = do
    s <- get
    tv <- newTypeVar "a"
    t1 <- ti env e1
    t2 <- ti (applySubst (tiSubst s) env) e2
    s' <- unify (applySubst (tiSubst s) t1) (TFun t2 tv)
    s'' <- gets $ \st -> st{tiSubst = tiSubst st `composeSubst` s'}
    return (applySubst (tiSubst s'') tv)
ti env (ELet x e1 e2) = do
    s <- get
    t1 <- ti env e1
    let TypeEnv env' = remove env x
        t' = generalize (applySubst (tiSubst s) env) t1
        env'' = TypeEnv (Map.insert x t' env')
    ti (applySubst (tiSubst s) env'') e2

tiLit :: TypeEnv -> Lit -> TI Type
tiLit _ (LInt _) = return TInt
tiLit _ (LBool _) = return TBool

inferType :: Map.Map String Scheme -> Exp -> TI Type
inferType env e = do
    s <- get
    t <- ti (TypeEnv env) e
    return (applySubst (tiSubst s) t)

test :: Exp -> IO ()
test e = do
    (res, _) <- runTI (inferType Map.empty e)
    case res of
        Left err -> putStrLn ("error: " ++ err)
        Right t -> putStrLn (show e ++ " :: " ++ show t)

instance Show Type where
    showsPrec _ x = shows (prType x)
prType :: Type -> Doc
prType (TVar n) = text n
prType TInt = text "Int"
prType TBool = text "Bool"
prType (TFun t s) = prParenType t <+> text "->" <+> prType s

prParenType :: Type -> Doc
prParenType t = case t of
    TFun _ _ -> parens (prType t)
    _ -> prType t

instance Show Exp where
    showsPrec _ x = shows (prExp x)
prExp :: Exp -> Doc
prExp (EVar name) = text name
prExp (ELit lit) = prLit lit
prExp (ELet var ex body) = text "let" <+> text var <+> text "=" <+> prExp ex <+> text "in" $$ nest 2 (prExp body)
prExp (EApp e1 e2) = prExp e1 <+> prParenExp e2
prExp (ELam n e) = char '\\' <> text n <+> text "->" <+> prExp e

prParenExp :: Exp -> Doc
prParenExp t = case t of
    ELet{} -> parens (prExp t)
    EApp{} -> parens (prExp t)
    ELam{} -> parens (prExp t)
    _ -> prExp t

instance Show Lit where
    showsPrec _ x = shows (prLit x)
prLit :: Lit -> Doc
prLit (LInt i) = integer i
prLit (LBool b) = if b then text "True" else text "False"

instance Show Scheme where
    showsPrec _ x = shows (prScheme x)
prScheme :: Scheme -> Doc
prScheme (Scheme vars t) = text "All" <+> hcat (punctuate comma (map text vars)) <> text "." <+> prType t

test0 = ELet "id" (ELam "x" (EVar "x")) (EVar "id")
test1 = ELet "id" (ELam "x" (EVar "x")) (EApp (EVar "id") (EVar "id"))
test2 = ELet "id" (ELam "x" (ELet "y" (EVar "x") (EVar "y"))) (EApp (EVar "id") (EVar "id"))
test3 = ELet "id" (ELam "x" (ELet "y" (EVar "x") (EVar "y"))) (EApp (EApp (EVar "id") (EVar "id")) (ELit(LInt 2)))

main :: IO ()
main = do
    _ <- test test0
    _ <- test test1
    _ <- test test2
    test test3