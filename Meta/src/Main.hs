{-# LANGUAGE ParallelListComp, PatternGuards #-}
module Main where

import System.Environment (getArgs)

import Parser

import Debug.Trace

--------------------------------------------------------------------------------
-- Top-level wrapper code.
main :: IO ()
main = getArgs >>= mapM readFile >>= go . concat

go :: String -> IO ()
go s = mapM_ putStrLn (map metaValueToString (filter isNotNoReturnValue (evalMeta (fst (head (runParser (metaToken >> parseMeta) s))) [])))
    where isNotNoReturnValue NoReturnValue = False
          isNotNoReturnValue _ = True

----------------------------------------------------------------------------------------
-- Data type of values, need to evaluate Expr into these data types, then print it out       
data Value = Number Int
             | BConst Bool
             | QSymbol String Int        -- the Int in the end of QSymbol, Cons and QCons datatype is used to
             | Cons Value Value Int      -- track their quotation levels. Useful in "eval" Intrinsic function
             | QCons Value Value Int     -- and macro.
             | FClosure Environment Expr Expr
             | MClosure Environment Expr Expr
             | Intrinsic String
             | Nil
             | Err
             | NoReturnValue  -- Using "define" will return this value, will not be printed as output.
    deriving Show

type Environment = [(String, Value)]
-------------------------------------------------------------------------------------------------
-- These are some helper functions for eval0.
exprListToMetaList :: [Expr] -> Expr
exprListToMetaList [] = NilE
exprListToMetaList (e : es) = Combination ((Symbol "cons") : e : (exprListToMetaList es) : [])

fBinding :: Expr -> [Expr] -> Environment -> Environment -> Environment
fBinding (Symbol s) es env h = ((s, fst (eval0 (exprListToMetaList es) 0 h)) : env)
fBinding (Combination es1) es2 env h = 
    case (last es1) of Symbol s -> (zip [symbolToString e | e <- es1] [fst (eval0 e 0 h) | e <- es2]) ++ env
                       DotTail (Symbol s) -> (zip [symbolToString e | e <- init es1] [fst (eval0 e 0 h) | e <- take ((length es1) - 1) es2]) ++ [(s, fst (eval0 (exprListToMetaList (drop ((length es1) - 1) es2)) 0 h))] ++ env
        where symbolToString (Symbol s) = s

mBinding :: Expr -> [Expr] -> Environment -> Environment -> Environment
mBinding (Symbol s) es env h = ((s, fst (eval0 (Combination ((Symbol "quote") : (exprListToMetaList es) : [])) 0 h)) : env)
mBinding (Combination es1) es2 env h = 
    case (last es1) of Symbol s -> (zip [symbolToString e | e <- es1] [fst (eval0 (Combination ((Symbol "quote") : e : [])) 0 h) | e <- es2]) ++ env
                       DotTail (Symbol s) -> (zip [symbolToString e | e <- init es1] [fst (eval0 (Combination ((Symbol "quote") : e : [])) 0 h) | e <- take ((length es1) - 1) es2]) ++ [(s, fst (eval0 (Combination ((Symbol "quote") : (exprListToMetaList (drop ((length es1) - 1) es2)) : [])) 0 h))] ++ env
        where symbolToString (Symbol s) = s

-- attach "quote" in front of Expr
quoteN :: Int -> Expr -> Expr
quoteN n e
  | n <= 0 = e
  | otherwise = quoteN (n-1) (Combination ((Symbol "quote") : e : []))

reconstructExpr :: Int -> Value -> Expr
reconstructExpr nUq (Number n) = Const n
reconstructExpr nUq (BConst b) = Boolean b
reconstructExpr nUq (QSymbol s nQ) = quoteN (nQ-nUq) (Symbol s)
reconstructExpr nUq Nil = NilE
reconstructExpr nUq (FClosure env args body) = (Combination ((Symbol "lambda") : args : body : []))
reconstructExpr nUq (MClosure env args body) = (Combination ((Symbol "macro") : args : body : []))
reconstructExpr nUq (Intrinsic s) = Symbol s
reconstructExpr nUq (Cons v1 v2 nQ) = quoteN (nQ-nUq) (Combination ((Symbol "cons") : (reconstructExpr nQ v1) : (reconstructExpr nQ v2) : []))
reconstructExpr nUq (QCons v Nil nQ) = quoteN (nQ-nUq) (Combination ((reconstructExpr nQ v) : []))
reconstructExpr nUq (QCons v1 (QCons v2 v3 nQ2) nQ1) = 
  case (reconstructExpr nQ1 (QCons v2 v3 nQ2)) of (Combination e2) -> quoteN (nQ1 - nUq) (Combination ((reconstructExpr nQ1 v1) : e2))
reconstructExpr nUq (QCons v1 v2 nQ) =
  case (reconstructExpr nQ v2) of e2 -> quoteN (nQ - nUq) (Combination ((reconstructExpr nQ v1) : (DotTail e2) : []))

-- Main evluation function.
eval0 :: Expr -> Int -> Environment -> (Value, Environment)
eval0 (Const d) n h = (Number d, h) 
eval0 (NilE) n h = (Nil, h)
eval0 (Boolean b) n h = (BConst b, h)
eval0 (Symbol "eq?") 0 h = (Intrinsic "eq?", h)
eval0 (Symbol "add") 0 h = (Intrinsic "add", h)
eval0 (Symbol "sub") 0 h = (Intrinsic "sub", h)
eval0 (Symbol "mul") 0 h = (Intrinsic "mul", h)
eval0 (Symbol "div") 0 h = (Intrinsic "div", h)
eval0 (Symbol "cons") 0 h = (Intrinsic "cons", h)
eval0 (Symbol "fst") 0 h = (Intrinsic "fst", h)
eval0 (Symbol "snd") 0 h = (Intrinsic "snd", h)
eval0 (Symbol "number?") 0 h = (Intrinsic "number?", h)
eval0 (Symbol "pair?") 0 h = (Intrinsic "pair?", h)
eval0 (Symbol "list?") 0 h = (Intrinsic "list?", h)
eval0 (Symbol "function?") 0 h = (Intrinsic "function?", h)
eval0 (Symbol "eval") 0 h = (Intrinsic "eval", h)
eval0 (Symbol s) 0 h = case lookup s h of Just a -> (a, h)
                                          Nothing -> (Err, h)
eval0 (Symbol s) n h = (QSymbol s n, h)
eval0 (Combination []) n h = (Nil, h)
eval0 (Combination ((Symbol "define") : (Symbol s) : e : [])) 0 h = (NoReturnValue, ((s, fst (eval0 e 0 (env : h))) : h))
    where env = (s, fst (eval0 e 0 (env : h)))
eval0 (Combination ((Symbol "lambda") : e1 : e2 : [])) 0 h = (FClosure h e1 e2, h)
eval0 (Combination ((Symbol "macro") : e1 : e2 : [])) 0 h = (MClosure h e1 e2, h)
eval0 (Combination ((Symbol "cons") : e1 : e2 : [])) n h = (Cons (fst (eval0 e1 n h)) (fst (eval0 e2 n h)) n, h)
eval0 (Combination ((Symbol "quote") : e : [])) n h = eval0 e (n+1) h
eval0 (Combination ((Symbol "unquote") : e : [])) n h
  | n > 0 = eval0 e (n-1) h
  | otherwise = (Err, h)
eval0 (Combination ((Symbol "if") : cond : cons : alt : [])) 0 h = 
    case fst (eval0 cond 0 h) of BConst False -> eval0 alt 0 h
                                 _ -> eval0 cons 0 h
eval0 (Combination (e : es)) 0 h =
    case fst (eval0 e 0 h) of 
      FClosure env args body -> (fst (eval0 body 0 (fBinding args es env h)), h)
      MClosure env args body -> eval0 (reconstructExpr 1 (fst (eval0 body 0 (mBinding args es env h)))) 0 h
      Intrinsic "eq?" -> 
        case es of (e1 : e2 : []) -> (metaEq1 (fst (eval0 e1 0 h)) (fst (eval0 e2 0 h)), h)
                   _ -> (Err, h)
          where metaEq1 (Number n1) (Number n2) = BConst (n1 == n2)
                metaEq1 (BConst b1) (BConst b2) = BConst (b1 == b2)
                metaEq1 (QSymbol s1 _) (QSymbol s2 _) = BConst (s1 == s2)
                metaEq1 (Cons v1 v2 _) (Cons v3 v4 _) = BConst (removeBConst (metaEq1 v1 v3) && removeBConst (metaEq1 v2 v4))
                metaEq1 (Cons v1 v2 _) (QCons v3 v4 _) = BConst (removeBConst (metaEq1 v1 v3) && removeBConst (metaEq1 v2 v4))
                metaEq1 (QCons v1 v2 _) (Cons v3 v4 _) = BConst (removeBConst (metaEq1 v1 v3) && removeBConst (metaEq1 v2 v4))
                metaEq1 (QCons v1 v2 _) (QCons v3 v4 _) = BConst (removeBConst (metaEq1 v1 v3) && removeBConst (metaEq1 v2 v4))
                metaEq1 Nil Nil = BConst True
                metaEq1 _ _ = BConst False
                removeBConst (BConst b) = b
      Intrinsic "add" -> 
        case es of (e1 : e2 : []) -> (metaAdd1 (fst (eval0 e1 0 h)) (fst (eval0 e2 0 h)), h)
                   _ -> (Err, h)
          where metaAdd1 (Number n1) (Number n2) = Number (n1 + n2)
      Intrinsic "sub" ->        
        case es of (e1 : e2 : []) -> (metaSub1 (fst (eval0 e1 0 h)) (fst (eval0 e2 0 h)), h)
                   _ -> (Err, h)
          where metaSub1 (Number n1) (Number n2) = Number (n1 - n2)
      Intrinsic "mul" -> 
        case es of (e1 : e2 : []) -> (metaMul1 (fst (eval0 e1 0 h)) (fst (eval0 e2 0 h)), h)
                   _ -> (Err, h)
          where metaMul1 (Number n1) (Number n2) = Number (n1 * n2)
      Intrinsic "div" -> 
        case es of (e1 : e2 : []) -> (metaDiv1 (fst (eval0 e1 0 h)) (fst (eval0 e2 0 h)), h)
                   _ -> (Err, h)
          where metaDiv1 (Number n1) (Number n2) = Number (div n1 n2)
      Intrinsic "cons" -> 
        case es of (e1 : e2 : []) -> (Cons (fst (eval0 e1 0 h)) (fst (eval0 e2 0 h)) 0, h)
                   _ -> (Err, h)
      Intrinsic "fst" -> 
        case es of (e1 : []) -> (metaFst1 (fst (eval0 e1 0 h)), h)
                   _ -> (Err, h)
          where metaFst1 (Cons v1 v2 _) = v1
                metaFst1 (QCons v1 v2 _) = v1
      Intrinsic "snd" -> 
        case es of (e1 : []) -> (metaSnd1 (fst (eval0 e1 0 h)), h)
                   _ -> (Err, h)
          where metaSnd1 (Cons v1 v2 _) = v2
                metaSnd1 (QCons v1 v2 _) = v2
      Intrinsic "number?" ->
        case es of (e1 : []) -> (metaNumber1 (fst (eval0 e1 0 h)), h)
                   _ -> (Err, h)
          where metaNumber1 (Number n1) = BConst True
                metaNumber1 _ = BConst False
      Intrinsic "pair?" -> 
        case es of (e1 : []) -> (metaPair1 (fst (eval0 e1 0 h)), h)
                   _ -> (Err, h)
          where metaPair1 (Cons v1 v2 _) = BConst True
                metaPair1 (QCons v1 v2 _) = BConst True
                metaPair1 _ = BConst False
      Intrinsic "list?" -> 
        case es of (e1 : []) -> (metaList1 (fst (eval0 e1 0 h)), h)
                   _ -> (Err, h)
          where metaList1 Nil = BConst True
                metaList1 (Cons v1 v2 _) = metaList1 v2
                metaList1 (QCons v1 v2 _) = metaList1 v2
                metaList1 _ = BConst False
      Intrinsic "function?" -> 
        case es of (e1 : []) -> (metaFunction1 (fst (eval0 e1 0 h)), h)
                   _ -> (Err, h)
          where metaFunction1 (FClosure h1 args1 body1) = BConst True
                metaFunction1 (MClosure h1 args1 body1) = BConst True
                metaFunction1 (Intrinsic s1) = BConst True
                metaFunction1 _ = BConst False
      Intrinsic "eval" -> 
        case es of 
          e1 : [] -> eval0 (reconstructExpr 1 (fst (eval0 e1 0 h))) 0 (snd (eval0 e1 0 h))
          _ -> (Err, h)
      _ -> (Err, h)
eval0 (Combination (e1 : (DotTail e2) : [])) n h = (QCons (fst (eval0 e1 n h)) (fst (eval0 e2 n h)) n, h)
eval0 (Combination (e : es)) n h = (QCons (fst (eval0 e n h)) (fst (eval0 (Combination es) n h)) n, h) -- or maybe = eval0 (cons e es) n h ?
eval0 _ _ h = (Err, h)

-- Evaluate the entire meta code, able to preserve environment changes made by "define".
evalMeta :: [Expr] -> Environment -> [Value]
evalMeta [] h = []
evalMeta (e : es) h = (fst (eval0 e 0 h)) : evalMeta es (snd (eval0 e 0 h))
-----------------------------------------------------------------------------------------------
-- Printers
metaExprToString :: Expr -> String
metaExprToString (Const n) = show n
metaExprToString (Boolean b) = show b
metaExprToString (Symbol s) = s
metaExprToString (Combination []) = "()"
metaExprToString (Combination es) = "(" ++ (concatMap (\e -> (metaExprToString e) ++ " ") (init es)) ++ metaExprToString (last es) ++ ")"
metaExprToString (DotTail e) = ". " ++ metaExprToString e
metaExprToString NilE = "()"

metaValueToString :: Value -> String
metaValueToString (Number n) = show n
metaValueToString (BConst b) = show b
metaValueToString (QSymbol s _) = "\'" ++ s
metaValueToString (Cons v1 v2 _) = "(cons " ++ metaValueToString v1 ++ " " ++ metaValueToString v2 ++ ")"
metaValueToString (QCons v1 v2 _) = "(cons " ++ metaValueToString v1 ++ " " ++ metaValueToString v2 ++ ")"
metaValueToString (FClosure env args body) = "#<function: " ++ show (map envValueToString env) ++ " " ++ metaExprToString args ++ " " ++ metaExprToString body ++ ">"
metaValueToString (MClosure env args body) = "#<macro: " ++ show (map envValueToString env) ++ " " ++ metaExprToString args ++ " " ++ metaExprToString body ++ ">"
metaValueToString (Intrinsic s) = "Intrinsic function: " ++ "s"
metaValueToString Nil = "()"
metaValueToString Err = "Error"

envValueToString :: (String, Value) -> (String, String)
envValueToString (s, FClosure _ args body) = (s, "#<Function Closure>") -- These two lines are here to avoid infinite loops when 
envValueToString (s, MClosure _ args body) = (s, "#<Macro Closure>")    -- the evironment contains recursively defined functions and macros.
envValueToString (s, v) = (s, metaValueToString v)
