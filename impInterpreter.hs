--Jaracah Teague

import Data.Char

-----------------------------------------------------------------------------------------
--Variables 
type Vars = String
-- Arithmetic expressions
data AExpr = Var Vars | Const Integer
           | Add AExpr AExpr | Sub AExpr AExpr
           | Mul AExpr AExpr | Div AExpr AExpr 
  deriving Show
-- Boolean expressions
data BExpr = TT | FF 
           | And BExpr BExpr | Or BExpr BExpr | Not BExpr 
           | Eql AExpr AExpr
           | Lt AExpr AExpr 
  deriving Show
-- Instructions
data Instr = Assign Vars AExpr
           | IfThenElse BExpr Instr Instr | While BExpr Instr
           | Do [Instr]
           | Nop
  deriving Show
-- A program is a list of instructions type Program = [ Instr ]
type Program = [Instr]
--Environments
type Env = [(Vars, Integer)]

-----------------------------------------------------------------------------------------
--Helper Functions

--LookUp
lookUp :: Vars -> Env -> Integer
lookUp x ((y1,y2):ys) = if x == y1 then y2 else lookUp x ys
lookUp _ _            = error "not found"

--Update 
switch :: Vars -> Integer -> (Vars, Integer) -> (Vars, Integer) 
switch v x (e1,e2) = if v == e1 then (v,x) else (e1,e2)

update :: Vars -> Integer -> Env -> Env
update v x [] = [(v,x)]
update v x e = map (switch v x) e

-----------------------------------------------------------------------------------------
--Question 1. Evaluating arithmetic and boolean expressions

evala :: Env -> AExpr -> Integer
evala env (Var x)     = lookUp x env
evala env (Const x)   = x
evala env (Add a1 a2) = (evala env a1) + (evala env a2)
evala env (Sub a1 a2) = (evala env a1) - (evala env a2)
evala env (Mul a1 a2) = (evala env a1) * (evala env a2)
evala env (Div a1 a2) = (evala env a1) `div` (evala env a2)

evalb :: Env -> BExpr -> Bool
evalb env (TT)        = True
evalb env (FF)        = False
evalb env (And b1 b2) = (evalb env b1) && (evalb env b2)
evalb env (Or b1 b2)  = (evalb env b1) || (evalb env b2)
evalb env (Not b)     = not (evalb env b)
evalb env (Eql a1 a2) = (evala env a1) == (evala env a2)
evalb env (Lt a1 a2)  = (evala env a1) <  (evala env a2)

-----------------------------------------------------------------------------------------
--Question 2. Executing instructions

exec :: Instr -> Env -> Env
exec (Assign v a)         e = (update v (evala e a) e)
exec (IfThenElse b i1 i2) e = if (evalb e b) then (exec i1 e) else (exec i2 e)
exec (While b i)          e = if (evalb e b) then (exec i e) else exec i e  --needs work
exec (Do (i:is))          e = (exec (Do is ) (exec i e))
exec (Nop)                e = e

-----------------------------------------------------------------------------------------
--Question 3. Lexical Analysis
data UOps = NotOp deriving Show
data BOps = AddOp | SubOp | MulOp | DivOp | AndOp | OrOp | EqlOp | LtOp | AssignOp
  deriving (Show,Enum,Eq,Ord)
data Token = VSym String | CSym Integer | BSym Bool
           | UOp UOps | BOp BOps
           | LPar | RPar | LBra | RBra | Semi | Keyword String
           | Err
           | PA AExpr | PB BExpr | PI Instr | PDo [Instr]
  deriving Show

--------------------------------------------

addSpaces :: String -> String
addSpaces [] = []
addSpaces ('/':'\\':xs) = " /\\ " ++ addSpaces xs
addSpaces ('\\':'/':xs) = " \\/ " ++ addSpaces xs
addSpaces ('(':xs)      = " ( "   ++ addSpaces xs
addSpaces (')':xs)      = " ) "   ++ addSpaces xs
addSpaces ('{':xs)      = " { "   ++ addSpaces xs
addSpaces ('}':xs)      = " } "   ++ addSpaces xs
addSpaces (';':xs)      = " ; "   ++ addSpaces xs
addSpaces ('+':xs)      = " + "   ++ addSpaces xs
addSpaces ('*':xs)      = " * "   ++ addSpaces xs
addSpaces ('/':xs)      = " / "   ++ addSpaces xs
addSpaces ('<':xs)      = " < "   ++ addSpaces xs
addSpaces ('=':'=':xs)  = " == "  ++ addSpaces xs
addSpaces (':':'=':xs)  = " := "  ++ addSpaces xs
addSpaces ('-':xs)      = " - "   ++ addSpaces xs
addSpaces (x:xs)        = x : addSpaces xs

isVSym :: String -> Bool
isVSym "" = False
isVSym (x:xs) = isLower x && q1 xs
  where q1 "" = True
        q1 (y:ys) = (isAlpha y || isDigit y || y `elem` "-_'") && q1 ys

isCSym :: String -> Bool
isCSym "" = False
isCSym (x:xs) = isDigit x && q1 xs
  where q1 "" = True
        q1 (y:ys) = (isDigit y && q1 ys) || (y == '.' && not (null ys) && q2 ys)
        q2 ys = all isDigit ys

classify :: String -> Token
classify ";"       = Semi
classify "("       = LPar
classify ")"       = RPar
classify "{"       = LBra
classify "}"       = RBra

classify s@"while" = Keyword s
classify s@"if"    = Keyword s
classify s@"then"  = Keyword s
classify s@"else"  = Keyword s
classify s@"nop"   = Keyword s

classify "T"       = BSym True
classify "F"       = BSym False

classify "!"       = UOp NotOp

classify "+"       = BOp AddOp
classify "-"       = BOp SubOp
classify "*"       = BOp MulOp
classify "/"       = BOp DivOp 
classify "/\\"     = BOp AndOp
classify "\\/"     = BOp OrOp
classify "=="      = BOp EqlOp
classify "<"       = BOp LtOp
classify ":="      = BOp AssignOp

classify s | isVSym s = VSym s
classify s | isCSym s = CSym (read s)

classify _         = Err

lexer :: String -> [Token]
lexer s = map classify (words (addSpaces s))

-----------------------------------------------------------------------------------------
--Question 4. Parsing

sr :: [Token] -> [Token] -> [Token]
sr (VSym v : ts)                              i = sr (PA (Var v) : ts) i
sr (CSym c : ts)                              i = sr (PA (Const c) : ts) i
sr s@(PA e2 : BOp op1 : PA e1 : ts) (BOp op2 : i) | op1 < op2 = sr (BOp op2 : s) i
sr (BSym True  : ts)                          i = sr (PB TT : ts) i
sr (BSym False : ts)                          i = sr (PB FF : ts) i
sr (PA p2 : BOp AddOp      : PA p1 : ts)      i = sr (PA (Add p1 p2)  : ts) i
sr (PA p2 : BOp SubOp      : PA p1 : ts)      i = sr (PA (Sub p1 p2)  : ts) i
sr (PA p2 : BOp MulOp      : PA p1 : ts)      i = sr (PA (Mul p1 p2)  : ts) i
sr (PA p2 : BOp DivOp      : PA p1 : ts)      i = sr (PA (Div p1 p2)  : ts) i
sr (PB p2 : BOp AndOp      : PB p1 : ts)      i = sr (PB (And p1 p2)  : ts) i
sr (PB p2 : BOp OrOp       : PB p1 : ts)      i = sr (PB (Or p1 p2)  : ts) i
sr (PA p2 : BOp EqlOp      : PA p1 : ts)      i = sr (PB (Eql p1 p2)  : ts) i
sr (PA p2 : BOp LtOp       : PA p1 : ts)      i = sr (PB (Lt p1 p2)   : ts) i
sr (PB b  : UOp NotOp : ts)                   i = sr (PB (Not b) : ts) i 
sr (PA p  : BOp AssignOp   : PA (Var x) : ts) i = sr (PI (Assign x p) : ts) i
sr (RPar  : PA p           : LPar : ts)       i = sr (PA p : ts) i
sr (RPar  : PB p           : LPar : ts)       i = sr (PB p : ts) i
sr (PI i2 : Keyword "else" : PI i1 : Keyword "then" : PB b : Keyword "if" : ts) i = sr (PI (IfThenElse b i1 i2) : ts) i
sr (PI a : PB b : Keyword "while" : ts)       i = sr (PI (While b a) : ts) i  
sr (Keyword "Nop" : ts)                       i = sr (PI (Nop) : ts) i


sr (RBra : PI a : ts)          i = sr (PDo [a] : ts) i
sr (RBra : ts)                 i = sr (PDo [] : ts) i
sr (PDo s : Semi : PI a : ts)  i = sr (PDo (a:s) : ts) i
sr (PDo s : LBra : ts)         i = sr (PI (Do s) : ts) i

sr ts                                 (i:input) = sr (i:ts) input
sr ts                                        [] = ts


parser :: [Token] -> Instr
parser ts = case (sr [] ts) of
  [PI s] -> s
  l      -> error ("No parse:" ++ show l)

-----------------------------------------------------------------------------------------
--Question 5. I/O

main :: IO ()
main = do
  --filename <- getLine
  let filename = "test.imp"
  contents <- readFile filename
  let analyzed  = lexer contents
  let parsed    = sr [] analyzed
  let exectuted = exec (parser parsed) []
  putStrLn (show parsed)

