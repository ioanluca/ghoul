module Main where

import System.Environment
import System.Exit
import Control.Applicative hiding (many)
import Control.Monad
import Data.Char
import Data.Foldable
import Data.List

ackerman :: Int -> Int -> Int
ackerman 0 n = n + 1
ackerman m 0 = ackerman (m-1) 1
ackerman m n = ackerman (m-1) (ackerman m (n-1))


plusProgram :: String
plusProgram =
  "plus(Z, y) = y;\
  \plus(S(x),y) = S (plus(x,   y));\
  \main() = plus(S(S(Z)),S(S(Z)));"

printProg :: String
printProg =
  "plus(Z,y) = print( \"salutare\" , y ) ;\
  \plus (S(x )  ,   y) = print( \" another msg \" , S(plus(x,y)));\
  \main(    ) = plus(S(S(Z) ),S(S(Z))   )  ;"


runGHOUL :: String -> Either ErrorMessage ([String], Either ErrorMessage Val)
runGHOUL text = do
  prog <- parseAllInput equations text
  checkProgram prog
  return (evalProgram prog)


type ErrorMessage = String


type Program =
  [Equation]


data Equation = MkEqn String [Pat] Exp
  deriving (Show, Eq)


data Pat
  = PV String
  | PC String [Pat]
  | PHole
  deriving (Show, Eq)


data Exp
  = EV String
  | EA String [Exp]
  | EC String [Exp]
  | EP String Exp
  deriving (Show, Eq)


plusProgramAST :: Program
plusProgramAST =
  [ MkEqn "plus"
          [PC "Z" [], PV "y"]
          (EV "y")
  , MkEqn "plus"
          [PC "S" [PV "x"], PV "y"]
          (EC "S" [EA "plus" [EV"x", EV"y"]])
  , MkEqn "main"
          []
          (EA "plus" [EC "S" [EC "S" [EC "Z" []]],
                      EC "S" [EC "S" [EC "Z" []]]])
  ]



appendProgram :: String
appendProgram = 
        "append(Empty,ys) = ys;     \
        \append(Cons(x,xs),ys) = Cons(x,append(xs,ys)); \n   \
        \main() = append(Cons(Z,Empty),Cons(Z,Cons(JustAConstructor(Z),Empty)));"


appendProgramAST :: Program
appendProgramAST = 
    [
        MkEqn "append"
            [PC "Empty" [], PV "ys"]
            (EV "ys"),
        MkEqn "append"
            [PC "Cons" [PV "x", PV "xs"], PV "ys"]
            (EC "Cons" [EV "x", EA "append" [EV "xs", EV "ys"]]),
        MkEqn "main"
            []
            (EA "append" [EC "Cons" [EC "Z" [], EC "Empty" []], EC "Cons" [EC "Z" [], EC "Cons" [EC "JustAConstructor" [EC "Z" []], EC "Empty" []]]])
        
    ]

progVsAST_prop :: String -> Program -> Bool
progVsAST_prop s p  = let Right (r,_) = runParser equations s
                      in r == p


myAppend :: [a] -> [a] -> [a]
myAppend [] xs = xs
myAppend (x:xs) ys = x : myAppend xs ys   


newtype Parser a = MkParser (String -> Either ErrorMessage (a, String))


runParser :: Parser a -> String -> Either ErrorMessage (a,String)
runParser (MkParser p) input = p input


parseAllInput :: Parser a -> String -> Either ErrorMessage a
parseAllInput p input =
  case runParser (p <* eoi) input of
    Right (a, _) -> Right a
    Left msg     -> Left ("Parse error: " ++ msg)


varname :: Parser String
varname = do
    id@(i:_) <- identifier
    if isLower i then return id else parseFail $
             [i] ++ " is not lowercase in the beginning of var " ++ id  
    


constructorname :: Parser String
constructorname = do
    var@(a:_) <- identifier
    if isUpper a then return var else parseFail $
             [a] ++ " is not uppercase in the beginning of constructor " ++ var  



numberToPat :: Int -> Pat
numberToPat 0 = PC "Z" []
numberToPat n = PC "S" [numberToPat $ n-1]

numberToExp :: Int -> Exp
numberToExp 0 = EC "Z" []
numberToExp n = EC "S" [numberToExp $ n-1]

parens :: Parser a -> Parser a
parens p =  isChar '(' *> spaces *> p <* spaces <* isChar ')'

args :: Parser a -> Parser [a]
args p = parens (sepBy (spaces *> isChar ',' <* spaces) p)

pat :: Parser Pat
pat =  numberToPat <$> number
       <|>
       PC <$> constructorname <* spaces <*> args pat
       <|>
       PV  <$> varname
       <|>
       (\ cn -> PC cn []) <$> constructorname
       <|> 
       PHole <$ satisfies "_" (== '_') 


strdel :: Char
strdel = '\"'

printParser :: Parser Exp
printParser = EP <$ string "print" <* spaces <*
               isChar '(' <* spaces <* isChar strdel <*>
               many ( satisfies [strdel] $ (/=) strdel) <* 
               isChar strdel <* spaces <* isChar ',' <* spaces <*> expr <*
               spaces <* isChar ')'

expr :: Parser Exp
expr =
    numberToExp <$> number
    <|>
    printParser
    <|>
    EA <$> varname <* spaces <*> args expr 
    <|>
    EC <$> constructorname <* spaces <*> args expr
    <|>
    EV <$> varname
    <|> 
    (\ con -> EC con []) <$> constructorname
    


equation :: Parser Equation
equation = 
    MkEqn <$>
    varname <* spaces <*> args pat <* spaces
            <* isChar '=' <* spaces <*> expr <* spaces <* isChar ';'


equations :: Parser Program
equations = spaces *>
            sepBy spaces equation <*
            spaces 


checkProgram :: Program -> Either ErrorMessage ()
checkProgram prog = do
    hasMainCheck prog
    scopeCheck prog
    arityCheck prog
    functionCheck prog


abortWithMessage :: ErrorMessage -> Either ErrorMessage a
abortWithMessage msg = Left msg


hasMainCheck :: Program -> Either ErrorMessage ()
hasMainCheck prog 
    | (length . filter (\ (MkEqn n ps ex) 
                -> n == "main" && ps == [])) prog == 1 = return ()
    | otherwise = abortWithMessage "no proper main"


--removeDuplicates :: Ord a => [a] -> [a]
--removeDuplicates = toList . fromList

lhs :: [Pat] -> [String]
lhs [] = []
lhs (p:ps) = case p of
             (PV var) -> var : lhs ps
             (PC _ ps') -> lhs ps' ++ lhs ps
             PHole -> []

rhs :: [Exp] -> [String]
rhs [] = []
rhs (e:es) = case e of 
                (EV var) -> var : rhs es
                (EA _ es') -> rhs es ++ rhs es'
                (EC _ es') -> rhs es ++ rhs es'
                (EP _ e) -> rhs [e]

equationScopeCheck :: Equation -> Either ErrorMessage ()
equationScopeCheck (MkEqn name ps e) = do
    let lefts = lhs ps
    let rights = rhs [e]
    let isScoped = all (`elem` lefts) rights
    if isScoped then return ()
         else abortWithMessage $ name ++ " equation not scoped"

scopeCheck :: Program -> Either ErrorMessage ()
scopeCheck [] = return ()
scopeCheck prg = do
    traverse equationScopeCheck prg
    return ()
    


sameName :: Equation -> Equation -> Bool
sameName (MkEqn n1 _ _) (MkEqn n2 _ _) = n1 == n2

compareByName :: Equation -> Equation -> Ordering
compareByName (MkEqn n1 _ _) (MkEqn n2 _ _) = compare n1 n2

groupByName :: [Equation] -> [[Equation]]
groupByName = groupBy sameName . sortBy compareByName

checkGroup :: [Equation] -> Either ErrorMessage ()
checkGroup [] = return () 
checkGroup ((MkEqn name ps _):es) = do
    let n = length ps
    let checkTheRest = all 
            (\(MkEqn _ ps _) -> length ps == n) es
    if checkTheRest then return () 
    else abortWithMessage $
         name ++ " equations have different number of patterns"

arityCheck :: Program -> Either ErrorMessage ()
arityCheck [] = return ()
arityCheck prg = do
    let groups = groupByName prg
    traverse checkGroup groups
    return ()
    

callsInExp :: Exp -> [String]
callsInExp (EA n es) = [n] ++ rest es 
callsInExp (EP _ e) = callsInExp e
callsInExp (EC n es) = rest es
callsInExp _ = []

rest :: [Exp] -> [String]    
rest = foldl (\acc e -> (callsInExp e) ++ acc) []  

equationFunctionCheck :: [String] -> Equation -> Either ErrorMessage ()
equationFunctionCheck ds (MkEqn fun ps e) = do
    let cs = callsInExp e
    let ds'= foldl getDefLHS [] ps
    if all (`elem` (ds ++ ds')) cs then return ()
    else abortWithMessage $ "undefined functions used in equation " ++ fun
    where getDefLHS acc (PV x) = x : acc
          getDefLHS acc _ = acc

functionCheck :: Program -> Either ErrorMessage ()
functionCheck prog = do
  let definedNames = foldl getName [] prog
  traverse_ (equationFunctionCheck definedNames) prog
  where getName acc (MkEqn n _ _) = if n `elem` acc then acc else n : acc




data Val = VC String [Val] |
           VPA String [Val]
         deriving (Show, Eq)


type Env = [(String, Val)]


newtype Matcher a = MkMatcher (Env -> Maybe (a, Env))


runMatcher :: Matcher a -> Env -> Maybe (a, Env)
runMatcher (MkMatcher m) = m


instance Functor Matcher where
  fmap f (MkMatcher m) =
    MkMatcher (fmap (\(a, env) -> (f a, env)) . m)

instance Applicative Matcher where
  pure a =
    MkMatcher (\env -> pure (a, env))

  mf <*> ma =
    MkMatcher (\env -> do
                  (f, env')  <- runMatcher mf env
                  (a, env'') <- runMatcher ma env'
                  return (f a, env''))

instance Monad Matcher where
  return = pure

  m >>= f =
    MkMatcher (\env -> do
                  (a, env') <- runMatcher m env
                  runMatcher (f a) env')

instance Alternative Matcher where
  empty =
    MkMatcher (\env -> empty)

  m1 <|> m2 =
    MkMatcher (\env -> runMatcher m1 env <|> runMatcher m2 env)


bindVar :: String -> Val -> Matcher ()
bindVar x v =
  MkMatcher (\env -> case lookup x env of
                       Nothing -> Just ((), (x,v):env)
                       Just _  -> Nothing)


zipChecked :: [a] -> [b] -> Maybe [(a,b)]
zipChecked xs ys = go xs ys []
  where go []     []     zs = Just (reverse zs)
        go (x:xs) (y:ys) zs = go xs ys ((x,y):zs)
        go _      _      _  = Nothing

matchPat :: (Pat, Val) -> Matcher ()
matchPat (PV p, val) = bindVarAllowRepeats p val
matchPat (PC pat ps, VC val vs) = 
    if pat == val then matchPats ps vs else empty
matchPat (PHole, _) = return ()

matchPats :: [Pat] -> [Val] -> Matcher ()
matchPats ps vs = 
        case (zipChecked ps vs) of
          Nothing -> empty
          Just pvs -> traverse_ matchPat pvs



takeFromBehind :: Int -> [a] -> [a]
takeFromBehind n = reverse . take n . reverse

partiallyApply :: [Val] -> Equation -> Matcher (Either Exp Val)
partiallyApply vs (MkEqn name ps expr) 
    | lps == lvs = (Left expr) <$ matchPats ps vs
    | lvs < lps = return $ Right (VPA name (takeFromBehind (lps - lvs) vs))
    | otherwise = empty
    where lvs = length vs
          lps = length ps
    

findMatchingEquation :: String -> [Val] -> Program -> Matcher (Either Exp Val)
findMatchingEquation _  _ [] = empty
findMatchingEquation n vs (e@(MkEqn eqn ps expr):es) = 
    (if n == eqn then partiallyApply vs e else empty)
    <|> 
    findMatchingEquation n vs es
    <|>
    empty
    


bindVarAllowRepeats :: String -> Val -> Matcher ()
bindVarAllowRepeats x v =
  MkMatcher (\env -> case lookup x env of
                       Nothing -> Just ((), (x,v):env)
                       Just v'  -> 
                            if(v == v') then Just ((), env) 
                                        else Nothing)


newtype Eval a =
  MkEval (Program -> Env -> ([String], Either ErrorMessage a))


runEval :: Eval a -> Program -> Env -> ([String], Either ErrorMessage a)
runEval (MkEval e) program env =
  e program env


instance Monad Eval where
  return x = MkEval (\prg env -> ([], return x))

  e >>= k = MkEval (\prg env -> 
                let (ls, r) = runEval e prg env in
                    case r of
                        Left err -> (ls, Left err)
                        Right a -> let (ls', r') = runEval (k a) prg env
                            in (ls ++ ls', r'))

instance Functor Eval where
  fmap f ea = do a <- ea; return (f a)

instance Applicative Eval where
  pure = return
  ef <*> ea = do f <- ef; a <- ea; return (f a)


abortEval :: ErrorMessage -> Eval a
abortEval msg = MkEval (\prg env -> ([], abortWithMessage msg))

currentEnvironment :: Eval Env
currentEnvironment = MkEval (\prg env -> ([], return env))

currentProgram :: Eval Program
currentProgram = MkEval (\prg env -> ([], return prg))

putLog :: String -> Eval ()
putLog s = MkEval $ \prg env -> ([s], return ())


afterMatch :: (a -> Eval b) -> Matcher a -> Eval b
afterMatch f (MkMatcher m) =
  MkEval (\prg _ -> case m [] of
                      Nothing       -> ([], abortWithMessage "Match failure")
                      Just (a, env) -> runEval (f a) prg env)

eval (EC con es) = do 
        vs <- traverse eval es 
        return $ VC con vs 

eval (EP msg e) = do
        v <- eval e
        putLog $ formatLog msg (prettyVal v)
        return v
    

eval (EV var) = do
    env <- currentEnvironment
    case (lookup var env) of
        Nothing -> abortEval "no such var in env"
        Just val -> return val

eval (EA fun es) = do
    env <- currentEnvironment
    prog <- currentProgram
    vs <- traverse eval es
    case(lookup fun env) of
        Nothing ->
            afterMatch fff $ findMatchingEquation fun vs prog
        Just (VPA pfun vs') -> 
            afterMatch fff $ findMatchingEquation pfun (vs ++ vs') prog

fff :: (Either Exp Val) -> Eval Val
fff (Left e) = eval e
fff (Right v) = return v




formatLog :: String -> String -> String
formatLog log val = 
    foldr (\x acc -> if x == '%' then val ++ acc else x : acc) [] log

    
    

evalProgram :: Program -> ([String], Either ErrorMessage Val)
evalProgram prog =
  runEval                 -- run an evaluation
    (eval (EA "main" [])) -- of the expression that calls the 'main' function
    prog                  -- in the given program
    []                    -- and the empty environment


partialProg :: String
partialProg =
  " plus(Z,y) = y;\
  \ plus(S(x),y) = S(plus(x,y));\
  \ plusTwo() = plus(S(S(Z)));\
  \ apply(f,a) = f(a);\
  \ main() = apply(plusTwo(),S(S(Z)));"


{- 10 MARKS -}
{----------------------------------------------------------------------}



{--------------------------------------------------------------------}
{- APPENDIX : RUNNING GHOUL FROM THE COMMAND LINE                   -}
{--------------------------------------------------------------------}


main :: IO ()
main = do
  args <- getArgs
  progName <- getProgName
  when (null args || (not . null . tail) args) $
    exitFail ("not exactly one input file.\n" ++
              "Usage: " ++ progName ++ " <input-file>")
  input <- readFile $ head args
  case runGHOUL input of
    Left err -> exitFail err
    Right (ls, Left err) -> do printLogs ls; exitFail err
    Right (ls, Right v) -> do printLogs ls; putStrLn $ "RESULT:\n" ++ (prettyVal v)
  where exitFail :: String -> IO ()
        exitFail msg = putStrLn ("GHOUL: " ++ msg) >> exitFailure
        printLogs :: [String] -> IO ()
        printLogs ls = do
                putStrLn "\nLOGS: "
                traverse putStrLn ls
                putStrLn ""
                 

prettyVal :: Val -> String
prettyVal (VC "Z" []) = show 0 
prettyVal x@(VC "S" [p]) = show $ go x
    where go (VC "Z" []) = 0
          go (VC "S" [p]) = 1 + go p
          
prettyVal (VC con args) = con ++ (if (null args) then "" else "(")
                              ++ concat (intersperse ", " $ map prettyVal args)
                              ++ (if (null args) then "" else ")")

prettyVal (VPA n vs) = "Partially appled: " 
                            ++ n ++ "(" 
                            ++ concat (intersperse ", " $ map prettyVal vs)
                            ++")"



{-  PARSER COMBINATORS    -}


instance Functor Parser where
  fmap f (MkParser p) =
    MkParser (fmap (fmap (\(a,s) -> (f a,s))) p)

instance Applicative Parser where
  pure x = MkParser (\s -> Right (x,s))

  MkParser pf <*> MkParser pa =
    MkParser (\s -> case pf s of
                      Left msg ->
                        Left msg
                      Right (f, s1) ->
                        case pa s1 of
                          Left msg ->
                            Left msg
                          Right (a, s2) ->
                            Right (f a, s2))

instance Monad Parser where
  MkParser p >>= k =
    MkParser (\s -> case p s of
                      Left msg -> Left msg
                      Right (a, s1) ->
                        let MkParser p2 = k a in
                          p2 s1)

instance Alternative Parser where
  empty =
    MkParser (\s -> Left "<empty>")

  MkParser p1 <|> MkParser p2 =
    MkParser (\s -> case p1 s of
                      Left _       -> p2 s
                      Right (a, s) -> Right (a,s))

eoi :: Parser ()
eoi = MkParser (\s -> case s of
                        "" -> Right ((), "")
                        s  -> Left ("expecting end of input; got " ++ show s))

parseFail :: String -> Parser a
parseFail msg = MkParser (\s -> Left msg)

char :: Parser Char
char = MkParser p
  where p []     = Left "expecting a character, but end of input was found"
        p (c:cs) = Right (c, cs)

isChar :: Char -> Parser ()
isChar expected = do
  seen <- char
  if expected == seen then
    return ()
  else
    parseFail ("Expecting " ++ show expected ++ ", got " ++ show seen)

satisfies :: String -> (Char -> Bool) -> Parser Char
satisfies p_description p = do
  c <- char
  if p c then return c else parseFail ("Expecting " ++ p_description ++ ", got " ++ show c)

string :: String -> Parser ()
string = mapM_ isChar

digit :: Parser Int
digit = do
  c <- char
  if isNumber c then
    return (digitToInt c)
  else
    parseFail "Expecting a digit"

number :: Parser Int
number = foldl (\l r -> l*10+r) 0 <$> some digit

space :: Parser ()
space = () <$ satisfies "a space character" isSpace

spaces :: Parser ()
spaces = () <$ many space

identifier :: Parser String
identifier = (:) <$> satisfies "alphabetic character" isAlpha
                 <*> many (satisfies "alphanumeric character" isAlphaNum)

sepBy :: Parser () -> Parser a -> Parser [a]
sepBy sep p = (:) <$> p <*> many (sep *> p) <|> pure []

many :: Parser a -> Parser [a]
many p = (:) <$> p <*> many p <|> pure []

