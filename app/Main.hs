{-# LANGUAGE ViewPatterns #-}
module Main where

import Data.Char (isAlpha)
import Data.List (nub, (\\))
import System.IO

-- type datatype printer and parser

data Ty = Unit | Fun Ty Ty

instance Show Ty where
    showsPrec 0 t = pp t
    showsPrec _ t = ('(':) . pp t . (')':)

pp :: Ty -> String -> String
pp Unit        = ('1' :)
pp (Fun t1 t2) = paren t1 . (" -> " ++) . pp t2 where
    paren Unit = pp Unit
    paren t@(Fun _ _) = ("(" ++) . pp t . (")" ++)

type Parser a = [Token] -> Maybe (a, [Token])

data Token =
    TokColon | TokOne | TokStar | TokOpen | TokClose | TokLam | TokLetter Char | TokArrow | TokErr
        deriving Show

parseType :: String -> Maybe Ty
parseType input = case ty (tokens input) of
    Just (t, []) -> Just t
    Nothing      -> Nothing

ty :: Parser Ty
ty (chain primary -> Just (ts, rest)) = Just (foldr1 Fun ts, rest)
ty _                                  = Nothing

primary :: Parser Ty
primary (TokOne : rest)                               = Just (Unit, rest)
primary (TokOpen : (ty -> Just (t, TokClose : rest))) = Just (t, rest)
primary _                                             = Nothing

chain :: Parser a -> Parser [a]
chain p (p -> Just (x, TokArrow : (chain p -> Just (xs, rest)))) = Just (x:xs, rest)
chain p (p -> Just (x, rest))                                    = Just ([x], rest)
chain p _                                                        = Nothing


-- term datatype printer and parser

data Term =
    Star |
    Var Char |
    App Term Term |
    Lambda Char (Maybe Ty) Term

instance Show Term where
    showsPrec 0 t = tpp t
    showsPrec _ t = ('(':) . tpp t . (')':)

tpp :: Term -> String -> String
tpp Star = ('*':)
tpp (Var c) = (c:)
tpp (Lambda x (Just t) e) = (("\\" ++ [x] ++ ":" ++ sh t ++ " -> ") ++) . tpp e where
    sh Unit = show Unit
    sh other = showsPrec 1 other ""
tpp (Lambda x Nothing e) = (("\\" ++ [x] ++ " -> ") ++) . tpp e
tpp (App e1 e2) = lparen e1 . (' ':) . rparen e2 where
    lparen t@(Lambda _ _ _) = parens t
    lparen other          = tpp other
    rparen t@(App _ _)    = parens t
    rparen t@(Lambda _ _ _) = parens t
    rparen other          = tpp other
    parens t = ('(':) . tpp t . (')':)

tokens :: String -> [Token]
tokens [] = []
tokens (' ' : more) = tokens more
tokens ('\n' : more) = tokens more
tokens ('\t' : more) = tokens more
tokens ('*' : more) = TokStar : tokens more
tokens ('1' : more) = TokOne : tokens more
tokens (':' : more) = TokColon : tokens more
tokens ('(' : more) = TokOpen : tokens more
tokens (')' : more) = TokClose : tokens more
tokens ('\\' : more) = TokLam : tokens more
tokens ('-' : '>' : more) = TokArrow : tokens more
tokens (c : more)
    | isAlpha c = TokLetter c : tokens more
    | otherwise = [TokErr]

tprimary :: [Token] -> Maybe (Term, [Token])
tprimary (TokStar : more) = Just (Star, more)
tprimary (TokLetter x : more) = Just (Var x, more)
tprimary (TokLam : TokLetter x : TokColon : (ty -> Just (t, TokArrow : (term -> Just (e,more))))) = Just (Lambda x (Just t) e, more)
tprimary (TokLam : TokLetter x : TokArrow : (term -> Just (e,more))) = Just (Lambda x Nothing e, more)
tprimary (TokOpen : (term -> Just (e, TokClose : more))) = Just (e, more)
tprimary _ = Nothing

term input = fmap g (tchain tprimary input) where
    g (terms, more) = (foldl1 App terms, more)

tchain :: ([Token] -> Maybe (a, [Token])) -> [Token] -> Maybe ([a], [Token])
tchain p (p -> Just (x, (tchain p -> Just (xs, rest)))) = Just (x:xs, rest)
tchain p (p -> Just (x, rest))                          = Just ([x], rest)
tchain p _                                              = Nothing

parseTerm :: String -> Maybe Term
parseTerm input = case term (tokens input) of
    Just (t, []) -> Just t
    _            -> Nothing


-- reduce a well-typed, closed, term to normal form
nf :: (Char -> Term) -> Term -> Term
nf env l@(Lambda _ _ _) = l
nf env Star             = Star
nf env term             = nf env (step env term)

-- reduce a well-typed, closed, term by one step
step :: (Char -> Term) -> Term -> Term
step env (App (Lambda x _ e1) e2) = subst x e2 e1
step env (App e1 e2) = App (step env e1) e2
step env l@(Lambda _ _ _) = l
step env Star    = Star
step env (Var x) = env x

-- substitute free occurrence of x with rep
-- if rep has no free variables, capture avoidance is satisfied
subst :: Char -> Term -> Term -> Term
subst x rep (App e1 e2)      = App (subst x rep e1) (subst x rep e2)
subst x rep l@(Lambda y t e) = if x==y then l else Lambda y t (subst x rep e)
subst x rep (Var y)          = if x==y then rep else (Var y)
subst x rep Star             = Star

-- check that a term has a given type
check :: (Char -> Ty) -> Term -> Ty -> Either String ()
check ctx (Var x) t = match (ctx x) t
check ctx Star Unit = Right ()
check ctx Star _    = Left "star type mismatch"
check ctx (App e1 e2) t = do
    w <- infer ctx e1
    case w of
        Fun u v -> do
            check ctx e2 u
            match v t
        Unit    -> Left "app type mismatch"
check ctx (Lambda x (Just t) e) Unit = Left "lambda type mismatch"
check ctx (Lambda x (Just t) e) (Fun u v) = do
    match t u
    check (\c -> if c==x then t else ctx c) e v

-- infer the type of a lambda term if possible
infer :: (Char -> Ty) -> Term -> Either String Ty
infer ctx (Var x) = Right (ctx x)
infer ctx Star    = Right Unit
infer ctx (Lambda x (Just t) e) = fmap (\u -> Fun t u) (infer ctx' e)
    where ctx' c = if c==x then t else ctx c
infer ctx (Lambda x Nothing e) = Left "lambda missing type annotation"
infer ctx (App e1 e2) = do
    t <- infer ctx e1
    case t of
        Unit -> Left "app inference error"
        Fun u v -> do
            w <- infer ctx e2
            match u w
            Right v

match (Fun a b) (Fun c d) = match a c >> match b d
match Unit Unit           = Right ()
match _ _                 = Left "match failed"



-- A repl


-- enumerate the free variables in the term
frees :: Term -> [Char]
frees term = nub (go [] term) where
    go env (Var x) = if x `elem` env then [] else [x]
    go env Star = []
    go env (App e1 e2) = go env e1 ++ go env e2
    go env (Lambda x _ e) = go (x:env) e

p x = let Just t = parseTerm x in t

defHelp = "definitions must be of the form <letter> = <term>"

parseDef :: String -> Either String (Char, Term)
parseDef (c : ' ' : '=' : ' ' : more)
    | isAlpha c = case parseTerm more of
        Just term -> Right (c, term);
        Nothing -> Left "failed to parse term"
    | otherwise = Left defHelp
parseDef _ = Left defHelp

printDef :: (Char, (Term,Ty)) -> IO ()
printDef (c,(term,t)) = do
    putStrLn ([c] ++ " : " ++ show t)
    putStrLn ([c] ++ " = " ++ show term)
    putStrLn ""

saveDefs :: [(Char,(Term,Ty))] -> IO ()
saveDefs env = do
    writeFile "floppy" $ unlines (map (\(c,(term,_)) -> [c] ++ " = " ++ show term) env)

loadDefs :: [String] -> Either String [(Char, (Term,Ty))]
loadDefs ls = go 0 [] ls where
    go n env [] = Right env
    go n env (l:ls) = case parseDef l of
        Right (c,term) -> case mergeEnv c term env of
            Right (_,env') -> go (n+1) env' ls
            Left msg -> Left ("line " ++ show n ++ ": " ++ msg)
        Left err -> Left ("line " ++ show n ++ ": " ++ err)

mergeEnv :: Char -> Term -> [(Char, (Term,Ty))] -> Either String (Ty, [(Char, (Term, Ty))])
mergeEnv c term env = 
    let ctx v = case lookup v env of Just (_,t) -> t; Nothing -> error "missing in context" in
    let vs = frees term in
    case frees term \\ map fst env of
        [] -> case infer ctx term of
            Right t  -> Right (t, ((c, (term,t)) : env))
            Left msg -> Left msg
        (c:_) -> Left ([c] ++ " not defined")

envGet :: [(Char, (Term, Ty))] -> Char -> Term
envGet env c = case lookup c env of
    Just (term,_) -> term
    Nothing       -> error ([c] ++ " not in environment")

repl :: [(Char,(Term,Ty))] -> IO ()
repl env = do
    putChar '>'
    putChar ' '
    hFlush stdout
    line <- getLine
    case words line of
        ["help"] -> do
            putStrLn helpMsg
            repl env
        ["list"] -> do
            mapM_ printDef (reverse env)
            repl env
        ["save"] -> do
            saveDefs (reverse env)
            putStrLn "environment saved to file `floppy'"
            repl env
        ["load"] -> do
            ls <- fmap lines (readFile "floppy")
            case loadDefs ls of
                Right env' -> do
                    mapM_ printDef (reverse env')
                    repl env'
                Left msg -> do
                    putStrLn msg
                    repl env
        ["eval", [c]] -> case lookup c env of
            Just (term,_) -> do
                let value = nf (envGet env) term
                print value
                repl env
            Nothing -> do
                putStrLn "not found"
                repl env
        _ -> case parseDef line of
            Left msg -> putStrLn msg >> repl env
            Right (c, term) -> case mergeEnv c term env of
                Right (t, env') -> do
                    putStrLn ([c] ++ " : " ++ show t)
                    putStrLn "Ok."
                    repl env'
                Left msg -> do
                    putStrLn msg
                    repl env


helpMsg =
    "Simply typed lambda calculus program.\n\
    \\n\
    \Commands: help list save load eval\n\
    \\n\
    \Definitions: <letter> = <term>\n\
    \\n\
    \<term> = * | <var> | <term> <term> | \\<var>:<type> -> <term>\n\
    \<var> = <letter>\n\
    \<type> = 1 | <type> -> <type>\n\
    \\n\
    \a chain of <term> <term> <term> ... associates to the left\n\
    \a chain of <type> -> <type> -> <type> -> ... associates to the right\n\
    \parentheses can be used in terms and types to override associativity\n\
    \\n\
    \help command - you're looking at it\n\
    \list command - display the defined terms held in memory and their types\n\
    \save command - save the defined terms to a file called `floppy'\n\
    \load command - clear all definitions and load those in file `floppy'\n\
    \eval <letter> command - evaluate the term <letter> found in the environment\n\
    \\n\
    \Typing judgments. <term> : <type> means the term <term> has type <type>.\n\
    \When a definition is entered, the program will check that the term is well-typed\n\
    \in the context of previously terms entered. If there is a problem during this\n\
    \process an error message will be printed and nothing new is defined. Otherwise\n\
    \the term's type is printed and the definition is appended to the environment.\n"


main = do
    repl []
