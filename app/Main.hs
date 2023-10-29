{-# LANGUAGE ViewPatterns #-}
module Main where

import Data.Char (isLetter, isLower)
import Data.List (nub, (\\))
import System.IO

-- type datatype printer and parser

type Token = String

type Parser a = [Token] -> Maybe (a, [Token])

data Ty = Unit | Fun Ty Ty

parseType :: String -> Maybe Ty
parseType input = case ty (tokens input) of
    Just (t, []) -> Just t
    _            -> Nothing

ty :: Parser Ty
ty (chain primary -> Just (ts, rest)) = Just (foldr1 Fun ts, rest)
ty _                                  = Nothing

primary :: Parser Ty
primary ("1" : rest)                         = Just (Unit, rest)
primary ("(" : (ty -> Just (t, ")" : rest))) = Just (t, rest)
primary _                                    = Nothing

chain :: Parser a -> Parser [a]
chain p (p -> Just (x, "->" : (chain p -> Just (xs, rest)))) = Just (x:xs, rest)
chain p (p -> Just (x, rest))                                = Just ([x], rest)
chain p _                                                    = Nothing

pp :: Ty -> String -> String
pp Unit        = ('1' :)
pp (Fun t1 t2) = paren t1 . (" -> " ++) . pp t2 where
    paren Unit = pp Unit
    paren t@(Fun _ _) = ("(" ++) . pp t . (")" ++)

instance Show Ty where
    showsPrec 0 t = pp t
    showsPrec _ t = ('(':) . pp t . (')':)


-- term datatype printer and parser

data Term =
    Star |
    Var Char |
    App Term Term |
    Lambda Char (Maybe Ty) Term

parseTerm :: String -> Maybe Term
parseTerm input = case term (tokens input) of
    Just (t, []) -> Just t
    _            -> Nothing

term input = fmap g (tchain tprimary input) where
    g (terms, more) = (foldl1 App terms, more)

tprimary :: [Token] -> Maybe (Term, [Token])
tprimary ("*" : more) = Just (Star, more)
tprimary (['a',x] : more) = Just (Var x, more)
tprimary ("\\" : ['a',x] : ":" : (ty -> Just (t, "->" : (term -> Just (e,more))))) =
    Just (Lambda x (Just t) e, more)
tprimary ("\\" : ['a',x] : "->" : (term -> Just (e,more))) = Just (Lambda x Nothing e, more)
tprimary ("(" : (term -> Just (e, ")" : more))) = Just (e, more)
tprimary _ = Nothing

tchain :: ([Token] -> Maybe (a, [Token])) -> [Token] -> Maybe ([a], [Token])
tchain p (p -> Just (x, (tchain p -> Just (xs, rest)))) = Just (x:xs, rest)
tchain p (p -> Just (x, rest))                          = Just ([x], rest)
tchain p _                                              = Nothing

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

instance Show Term where
    showsPrec 0 t = tpp t
    showsPrec _ t = ('(':) . tpp t . (')':)

-- tokenizer

tokens :: String -> [Token]
tokens [] = []
tokens (' ' : more) = tokens more
tokens ('\n' : more) = tokens more
tokens ('\t' : more) = tokens more
tokens ('*' : more) = "*" : tokens more
tokens ('1' : more) = "1" : tokens more
tokens (':' : more) = ":" : tokens more
tokens ('(' : more) = "(" : tokens more
tokens (')' : more) = ")" : tokens more
tokens ('\\' : more) = "\\" : tokens more
tokens ('-' : '>' : more) = "->" : tokens more
tokens (c : more)
    | isLetter c = ['a', c] : tokens more
    | otherwise = ["LexError"]


-- evaluator

-- reduce a well-typed (in the environment) term to normal form
nf :: (Char -> Term) -> Term -> Term
nf env l@(Lambda _ _ _) = l
nf env Star             = Star
nf env term             = nf env (step env term)

-- reduce a well-typed term by one step. Environment is used for free variables only
step :: (Char -> Term) -> Term -> Term
step env (App (Lambda x _ e1) e2) = subst (frees e2) x e2 e1
step env (App e1 e2)              = App (step env e1) e2
step env l@(Lambda _ _ _)         = l
step env Star                     = Star
step env (Var x)                  = env x

-- capture avoiding substitution
subst :: [Char] -> Char -> Term -> Term -> Term
subst vs c rep Star           = Star
subst vs c rep (Var x)        = if c==x then rep else Var x
subst vs c rep (App e1 e2)    = App (subst vs c rep e1) (subst vs c rep e2)
subst vs c rep (Lambda x t e) =
    if c == x || absent c e -- then nothing would be substituted anyway, do nothing
        then Lambda x t e
        else if not (x `elem` vs) -- substituting would not capture x, go ahead
            then Lambda x t (subst vs c rep e)
            else -- need to rename the bound variable to avoid disaster
                let y = head (unused (Lambda x t e) \\ vs)
                in Lambda y t (subst vs c rep (rename x y e))

-- test if variable is not found in term
absent :: Char -> Term -> Bool
absent c (Var x)        = c /= x
absent c (App e1 e2)    = absent c e1 && absent c e2
absent c (Lambda x _ e) = if c==x then True else absent c e
absent c Star           = True

-- produce a stream of unused letters
unused :: Term -> String
unused term = (filter isLower (filter isLetter ['\0'..])) \\ frees term

-- rename free variables assuming the new name isn't used free
rename :: Char -> Char -> Term -> Term
rename a b (Var x)        = if a==x then (Var b) else (Var x)
rename a b (Lambda x t e) = if a==x then Lambda x t e else Lambda x t (rename a b e)
rename a b (App e1 e2)    = App (rename a b e1) (rename a b e2)
rename a b Star           = Star

-- enumerate the free variables in the term
frees :: Term -> [Char]
frees term = nub (go [] term) where
    go env (Var x) = if x `elem` env then [] else [x]
    go env Star = []
    go env (App e1 e2) = go env e1 ++ go env e2
    go env (Lambda x _ e) = go (x:env) e




-- type checker

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
check ctx (Lambda x _       _) Unit      = Left "lambda type mismatch"
check ctx (Lambda _ Nothing _) (Fun _ _) = Left "unannotated lambda"
check ctx (Lambda x (Just t) e) (Fun u v) = do
    match t u
    check (\c -> if c==x then t else ctx c) e v

-- infer the type of a lambda term if possible
infer :: (Char -> Ty) -> Term -> Either String Ty
infer ctx (Var x) = Right (ctx x)
infer _   Star    = Right Unit
infer ctx (Lambda x (Just t) e) = fmap (\u -> Fun t u) (infer ctx' e)
    where ctx' c = if c==x then t else ctx c
infer _   (Lambda _ Nothing _) = Left "lambda missing type annotation"
infer ctx (App e1 e2) = do
    t <- infer ctx e1
    case t of
        Unit -> Left "app inference error"
        Fun u v -> do
            w <- infer ctx e2
            match u w
            Right v

-- check that types match
match :: Ty -> Ty -> Either String ()
match (Fun a b) (Fun c d) = match a c >> match b d
match Unit Unit           = Right ()
match _ _                 = Left "match failed"




-- A repl

type Env = [(Char, (Term,Ty))]

repl :: Env -> IO ()
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
        ("eval" : more) -> case parseTerm (unwords more) of
            Just term -> case wouldMerge term env of
                Right t -> do
                    putStrLn ("inferred type: " ++ show t)
                    let value = nf (envGet env) term
                    putStrLn ("evaluates to: " ++ show value)
                    repl env
                Left msg -> do
                    putStrLn msg
                    repl env
            Nothing -> do
                putStrLn "failed to parse the program"
                repl env
        ("type" : more) -> case parseTerm (unwords more) of
            Just term -> case wouldMerge term env of
                Right t -> do
                    print t
                    repl env
                Left msg -> do
                    putStrLn msg
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

parseDef :: String -> Either String (Char, Term)
parseDef (c : ' ' : '=' : ' ' : more)
    | isLetter c = case parseTerm more of
        Just term -> Right (c, term);
        Nothing -> Left "failed to parse term"
    | otherwise = Left defHelp
parseDef _ = Left defHelp

printDef :: (Char, (Term,Ty)) -> IO ()
printDef (c,(term,t)) = do
    putStrLn ([c] ++ " : " ++ show t)
    putStrLn ([c] ++ " = " ++ show term)
    putStrLn ""

saveDefs :: Env -> IO ()
saveDefs env = do
    writeFile "floppy" $ unlines (map (\(c,(term,_)) -> [c] ++ " = " ++ show term) env)

loadDefs :: [String] -> Either String Env
loadDefs strings = go 0 [] strings where
    go :: Int -> Env -> [String] -> Either String Env
    go _ env [] = Right env
    go n env (l:ls) = case parseDef l of
        Right (c,term) -> case mergeEnv c term env of
            Right (_,env') -> go (n+1) env' ls
            Left msg -> Left ("line " ++ show n ++ ": " ++ msg)
        Left err -> Left ("line " ++ show n ++ ": " ++ err)

mergeEnv :: Char -> Term -> Env -> Either String (Ty, Env)
mergeEnv c term env = 
    let ctx v = case lookup v env of Just (_,t) -> t; Nothing -> error "missing in context" in
    case frees term \\ map fst env of
        [] -> case infer ctx term of
            Right t  -> Right (t, ((c, (term,t)) : env))
            Left msg -> Left msg
        (v:_) -> Left ([v] ++ " not defined")

wouldMerge :: Term -> Env -> Either String Ty
wouldMerge term env =
    let ctx v = case lookup v env of Just (_,t) -> t; Nothing -> error "missing in context" in
    case frees term \\ map fst env of
        []    -> infer ctx term
        (v:_) -> Left ([v] ++ " not defined")

envGet :: Env -> Char -> Term
envGet env c = case lookup c env of
    Just (term,_) -> term
    Nothing       -> error ([c] ++ " not in environment")

helpMsg :: String
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
    \eval <term> command - evaluate the term <term> within the environment\n\
    \type <term> command - infer the type of <term> within the environment\n\
    \\n\
    \Typing judgments. <term> : <type> means the term <term> has type <type>.\n\
    \When a definition is entered, the program will check that the term is well-typed\n\
    \in the context of previously terms entered. If there is a problem during this\n\
    \process an error message will be printed and nothing new is defined. Otherwise\n\
    \the term's type is printed and the definition is appended to the environment.\n\
    \\n\
    \Notable facts about simply typed lambda calculus. Once a definition is parsed\n\
    \and type-checked within a given environment, evaluation always produces a\n\
    \normal form in finite time. The normal form is unique and of the correct type.\n"

defHelp :: String
defHelp = "definitions must be of the form <letter> = <term>"

p :: String -> Term
p (parseTerm -> Just t) = t
p _                     = error "parse failed"

main :: IO ()
main = repl []
