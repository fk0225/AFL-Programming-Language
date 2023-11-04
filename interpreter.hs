import System.Environment
import System.IO
import Control.Monad.Except
import Control.Monad.Identity
import Data.Map 
import qualified Data.Map as Map
import qualified Data.String

import AbsAFLMay as A
import ParAFLMay as P


type Env = Map String Value

type TypeEnv = Map String TypeValue

type EvalMonad a =  (ExceptT Err Identity) a

type TypeMonad a =  (ExceptT Err Identity) a

type FunEnv = Map String TypeValue

type Err = String

data TypeValue = TInt | TBool
    | TListEmpty
    | TList TypeValue
    | TFun TypeValue TypeValue
    | TDecl
    | TDef
  deriving (Eq, Ord, Show, Read)
 
data Value = VInt Integer | VBool Bool
    | VList [Value]
    | VClos String Evaluable Env 
  deriving (Eq, Ord, Show, Read)
  

typeValidCheck :: A.TypeName -> TypeEnv -> TypeMonad TypeValue

typeValidCheck (A.TypeName typeName) typeEnv =  
    if member typeName typeEnv
        then do return (typeEnv ! typeName) 
        else throwError ("Unknown type: " ++ typeName)

typeCheckSingleSignat :: A.Signature -> TypeEnv -> TypeMonad TypeValue

typeCheckSingleSignat (A.SignatVar typeName) typeEnv = do
    v <- typeValidCheck typeName typeEnv;
    return v
    
typeCheckSingleSignat (A.SignatL s) typeEnv = do
    vs <- typeCheckSingleSignat s typeEnv;
    return $ TList vs
    
typeCheckSingleSignat (A.SignatFun s) typeEnv = do
    vs <- typeCheckSignat s typeEnv;
    return vs

typeCheckSignat :: [A.Signature] -> TypeEnv -> TypeMonad TypeValue

typeCheckSignat [] _ = do throwError $ "Signature can't be empty"

typeCheckSignat (dom:[]) typeEnv = do 
    vd <- typeCheckSingleSignat dom typeEnv;
    return vd

typeCheckSignat (dom:(hcodom:tcodom)) typeEnv = do
    vd <- typeCheckSingleSignat dom typeEnv;
    vc <- typeCheckSignat (hcodom:tcodom) typeEnv;
    return $ TFun vd vc 

typeCheckEx :: A.Expr -> FunEnv -> TypeEnv -> TypeMonad TypeValue

typeCheckEx (A.ExDecl (A.FunName f) signat) funEnv typeEnv = do
    vsignat <- typeCheckSignat signat typeEnv;
    return vsignat

typeCheckEx (A.ExDef d) funEnv typeEnv = do
    v <- typeCheckDefinition d funEnv typeEnv;
    return v

typeCheckEv :: A.Evaluable -> FunEnv -> TypeEnv -> TypeMonad TypeValue

typeCheckEv(A.ELitInt i) funEnv typeEnv = do return TInt

typeCheckEv(A.ELitTrue) funEnv typeEnv = do return TBool

typeCheckEv(A.ELitFalse) funEnv typeEnv = do return TBool

typeCheckEv(A.EList l) funEnv typeEnv = do 
    v <- typeCheckL l funEnv typeEnv;
    return v;

typeCheckEv (A.ENeg e) funEnv typeEnv = do {
    v <- typeCheckEv e funEnv typeEnv;
    case v of
        TInt -> return TInt
        otherwise -> throwError $ "Argument of integer negation is of wrong type " ++ (show v)
}

typeCheckEv(A.ENot e) funEnv typeEnv = do {
    v <- typeCheckEv e funEnv typeEnv;
    case v of
        TBool -> return TBool
        otherwise -> throwError $ "Argument of logical negation is of wrong type " ++ (show v)
}


typeCheckEv(A.EPow e1 e2) funEnv typeEnv = do {
    v1 <- typeCheckEv e1 funEnv typeEnv;
    v2 <- typeCheckEv e2 funEnv typeEnv;
    if v1/=TInt then throwError $ "First argument of (^) is of wrong type " ++ (show v1) else
    if v2/=TInt then throwError $ "Second argument of (^) is of wrong type " ++ (show v2) else
    return v1
}


typeCheckEv (A.EMul e1 op e2) funEnv typeEnv = do
  v1 <- typeCheckEv e1 funEnv typeEnv
  case v1 of
    TInt -> do
      v2 <- typeCheckEv e2 funEnv typeEnv 
      case v2 of
        TInt -> return TInt
        otherwise -> throwError $ "Second argument of " ++ show(op) ++ " is of wrong type " ++ (show v2)
    otherwise -> throwError $ "First argument of " ++ show(op) ++ " is of wrong type " ++ (show v1)

typeCheckEv (A.EAdd e1 op e2) funEnv typeEnv = do
  v1 <- typeCheckEv e1 funEnv typeEnv
  case v1 of
    TInt -> do
      v2 <- typeCheckEv e2 funEnv typeEnv
      case v2 of
        TInt -> return TInt
        otherwise -> throwError $ "Second argument of " ++ show(op) ++ " is of wrong type " ++ (show v2)
    otherwise -> throwError $ "First argument of " ++ show(op) ++ " is of wrong type " ++ (show v1)

typeCheckEv (A.ERel e1 op e2) funEnv typeEnv = do
  v1 <- typeCheckEv e1 funEnv typeEnv
  case v1 of
    TInt -> do
      v2 <- typeCheckEv e2 funEnv typeEnv
      case v2 of
        TInt -> return TBool
        otherwise -> throwError $ "Second argument of " ++ show(op) ++ " is of wrong type " ++ (show v2)
    otherwise -> throwError $ "First argument of " ++ show(op) ++ " is of wrong type " ++ (show v1)

typeCheckEv (A.EAnd e1 e2) funEnv typeEnv = do
  v1 <- typeCheckEv e1 funEnv typeEnv
  case v1 of
    TBool -> do
      v2 <- typeCheckEv e2 funEnv typeEnv
      case v2 of
        TBool -> return TBool
        otherwise -> throwError $ "Second argument of AND is of wrong type " ++ (show v2)
    otherwise -> throwError $ "First argument of AND is of wrong type " ++ (show v1)

typeCheckEv (A.EOr e1 op e2) funEnv typeEnv = do
  v1 <- typeCheckEv e1 funEnv typeEnv
  case v1 of
    TBool -> do
      v2 <- typeCheckEv e2 funEnv typeEnv
      case v2 of
        TBool -> return TBool
        otherwise -> throwError $ "Second argument of "++(show op)++" is of wrong type " ++ (show v2)
    otherwise -> throwError $ "First argument of "++(show op)++" is of wrong type " ++ (show v1)
    
typeCheckEv(A.ECond cond outIf outElse) funEnv typeEnv = do
    vCond <- typeCheckEv cond funEnv typeEnv
    case vCond of
        TBool -> do 
            vIf <- typeCheckEv outIf funEnv typeEnv
            vElse <- typeCheckEv outElse funEnv typeEnv
            case (vIf, vElse) of
                (v1, v2) | v1 == v2 -> return vElse
                otherwise -> throwError $ "Conditional branches types do not match: " ++ show vIf ++ " and " ++ show vElse
        otherwise -> throwError $ "Branching condition not of type TBool, instead: " ++ show vCond
   
typeCheckEv (A.ELet (A.FunName i) s e1 e2) funEnv typeEnv = do
    vs <- typeCheckSignat s typeEnv;
    v1 <- typeCheckEv e1 funEnv typeEnv;
    if v1 == vs then do
        v2 <- typeCheckEv e2 (insert i v1 funEnv) typeEnv;
        return v2
    else throwError $ "Signature and definition of mismatching types"   
    
typeCheckEv (A.ELam (FunName i) si e se) funEnv typeEnv = do
    vsi <- typeCheckSignat si typeEnv;
    vse <- typeCheckSignat se typeEnv;
    ve <- typeCheckEv e (insert i vsi funEnv) typeEnv;
    if ve/=vse then throwError ("Lambda expression definition not matching its signature") else do
    return $ TFun vsi vse
    

typeCheckEv (A.EVar (A.FunName f)) funEnv typeEnv =
    if member f funEnv 
        then do return (funEnv ! f)
        else throwError ("Function " ++ f ++ " without declaration") 
    
typeCheckEv (A.EFunApp f e) funEnv typeEnv = do 
    vf <- typeCheckEv f funEnv typeEnv;
    ve <- typeCheckEv e funEnv typeEnv;
    v <- (reduceType vf ve);
    return v

reduceType :: TypeValue->TypeValue->TypeMonad TypeValue

reduceType (TFun dom codom) evalType = do 
    case evalType of
        evalType | evalType == dom -> return codom
        otherwise -> throwError $ "Function argument is of wrong type " ++ (show evalType)
  
typeCheckL :: A.List -> FunEnv -> TypeEnv -> TypeMonad TypeValue

typeCheckL (A.LBrackets []) funEnv typeEnv = do return TListEmpty

typeCheckL(A.LBrackets (h:t)) funEnv typeEnv = 
    if t==[] then do {
        vh <- typeCheckEv h funEnv typeEnv;
        return (TList vh)
    } else do {
        vh <- typeCheckEv h funEnv typeEnv;
        vt <- typeCheckL (A.LBrackets t) funEnv typeEnv;
        case vt of 
            TListEmpty -> return (TList vh)
            (TList vtcontent) -> 
                case vtcontent of
                    vtcontent | vh==vtcontent -> return (TList vh);
                    otherwise -> throwError $ "List arguments of mismatching types "++ show(vh) ++" "++ show(vtcontent)
    }

typeCheckL(A.LHeadTail h t) funEnv typeEnv = 
    case t of
        (A.LBrackets []) -> do
            vh <- typeCheckEv h funEnv typeEnv;
            return (TList vh)
        otherwise -> do
            vh <- typeCheckEv h funEnv typeEnv;
            vt <- typeCheckL t funEnv typeEnv; 
            let (TList vtcontent) = vt 
            case vtcontent of
                vtcontent | vh==vtcontent -> return (TList vh)
                otherwise -> throwError $ "List arguments of mismatching types "++ show(vh) ++" "++ show(vtcontent)


typeCheckDefinition :: A.Definition -> FunEnv -> TypeEnv -> TypeMonad TypeValue 

typeCheckDefinition (A.Nonrec (A.FunName i) e) funEnv typeEnv = do
    if member i funEnv then do
        let vi = (funEnv ! i)
        ve <- typeCheckEv e funEnv typeEnv;
        if vi/=ve then throwError ("Function signature not matching definition type") else do
        return TDef
    else throwError $ "Function without declaration"
    
typeCheckDefinition (A.Rec (A.FunName i) e) funEnv typeEnv = do
    if member i funEnv then do
        let vi = (funEnv ! i)
        ve <- typeCheckEv e funEnv typeEnv;
        if vi/=ve then throwError ("Function signature not matching definition type") else do
        return TDef
    else throwError $ "Function without declaration"


applyAddOp A.Plus = (+)

applyAddOp A.Minus = (-)

applyMulOp A.Times = (*)

applyMulOp A.Div = div 

applyMulOp A.Mod = mod

applyRelOp A.LT = (<)

applyRelOp A.GT = (>)

applyRelOp A.LE = (<=)

applyRelOp A.GE = (>=)

applyRelOp A.EQ = (==)

applyRelOp A.NE = (/=)

applyOrOp A.OR = (||)

applyOrOp A.XOR = xor


xor :: Bool -> Bool -> Bool

xor x y = (x || y) && not (x && y)


evalEv :: Evaluable -> Env -> EvalMonad Value

evalEv (A.ELitInt i) env = do return (VInt i)

evalEv (A.ELitTrue) env = do return (VBool True)

evalEv (A.ELitFalse) env = do return (VBool False)

evalEv (A.ENeg e) env = do
    v <- evalEv e env;
    let (VInt n) = v;
    return (VInt (negate n));

evalEv (A.ENot e) env = do
    v <- evalEv e env;
    let (VBool b) = v;
    return (VBool (not b));
    
evalEv (A.EPow e1 e2) env = do 
    v1 <- evalEv e1 env;
    v2 <- evalEv e2 env;
    let (VInt n1) = v1;
    let (VInt n2) = v2;
    case n2 of 
        n2 | n2 < 0 -> throwError $ "Negative exponent"
        otherwise -> return (VInt (n1 ^ n2)); 

evalEv (A.EMul e1 op e2) env = do 
    v1 <- evalEv e1 env;
    v2 <- evalEv e2 env;
    let (VInt n1) = v1;
    let (VInt n2) = v2;
    case (op,n2) of
        (A.Div,0) -> throwError $ "Division by zero"
        otherwise -> return (VInt (applyMulOp op n1 n2));

evalEv (A.EAdd e1 op e2) env = do  
    v1 <- evalEv e1 env;
    v2 <- evalEv e2 env;
    let (VInt n1) = v1;
    let (VInt n2) = v2;
    return (VInt (applyAddOp op n1 n2));

evalEv (A.ERel e1 op e2) env = do 
    v1 <- evalEv e1 env;
    v2 <- evalEv e2 env;
    let (VInt n1) = v1;
    let (VInt n2) = v2;
    return (VBool (applyRelOp op n1 n2));

evalEv (A.EAnd e1 e2) env = do 
    v1 <- evalEv e1 env;
    v2 <- evalEv e2 env;
    let (VBool b1) = v1;
    let (VBool b2) = v2 
    return (VBool (b1 && b2));

evalEv (A.EOr e1 op e2) env = do 
    v1 <- evalEv e1 env;
    v2 <- evalEv e2 env;
    let (VBool b1) = v1;
    let (VBool b2) = v2;
    return (VBool (applyOrOp op b1 b2));

evalEv(A.ECond cond outIf outElse) env = do
    vCond <- evalEv cond env;
    case vCond of
        (VBool True) -> do
            vOutIf <- evalEv outIf env;
            return vOutIf
        otherwise -> do
            vOutElse <- evalEv outElse env;
            return vOutElse
            
evalEv(A.EList l) env = do
    v <- evalL l env
    return v
    
evalEv(A.ELet (A.FunName i) s e1 e2) env = do
  if member i env then throwError ("Overshadowing attempt") else do
  v1 <- evalEv e1 env;
  v2 <- evalEv e2 (insert i v1 env); 
  return v2

evalEv(A.ELam (A.FunName i) si e se) env = do return (VClos i e env)
    
evalEv(A.EFunApp f x) env = do 
    vf <- evalEv f env;
    vx <- evalEv x env;
    vApp <- apply vf vx; 
    return vApp

evalEv (A.EVar (A.FunName f)) env = do
    if member f env
        then return (env ! f) 
        else throwError ("Unknown function: " ++ f)
            
evalL(A.LBrackets []) env = do return (VList []) 

evalL (A.LBrackets (h:t)) env =
  if t == []
    then do
      vh <- evalEv h env
      return (VList [vh])
    else do
      vh <- evalEv h env
      vt <- evalL (A.LBrackets t) env
      let (VList l) = vt
      return (VList (vh:l))

evalL (A.LHeadTail h t) env =
  case t of
    A.LBrackets [] -> do
      vh <- evalEv h env
      return (VList [vh])
    otherwise -> do
      vh <- evalEv h env
      vt <- evalL t env
      let (VList l) = vt
      return (VList (vh:l))

apply :: Value->Value->EvalMonad Value

apply (VClos param mappedTo env) x = do
    vMappedTo <- evalEv mappedTo (insert param x env)
    return vMappedTo 


addDefToEnv :: A.Definition -> Env -> EvalMonad Env

addDefToEnv (A.Nonrec (A.FunName i) e) env = do 
    v <- evalEv e env;
    return $ insert i v env

addDefToEnv (A.Rec (A.FunName i) (A.ELam (A.FunName p) sp e se)) env = do return $ newenv where newenv = insert i (VClos p e newenv) env

addDefToEnv _ _ = throwError $ "Invalid Definition"

initialEnv :: Env

initialEnv = empty

initialFunEnv :: FunEnv

initialFunEnv = empty 

initialTypeEnv :: TypeEnv 

initialTypeEnv = Map.fromList [("Int",TInt), ("Bool", TBool)]


runEvalMonad :: (EvalMonad a) -> Either Err a

runEvalMonad v = runIdentity (runExceptT v)

runTypeMonad :: (TypeMonad a) -> Either Err a

runTypeMonad v = runIdentity (runExceptT  v)


addDeclToFunEnv :: Expr -> FunEnv -> TypeEnv -> TypeMonad TypeEnv

addDeclToFunEnv (A.ExDecl (A.FunName f) signat) funEnv typeEnv = do
    st <- typeCheckSignat signat typeEnv;
    return $ insert f st funEnv
    
typeCheckProg :: Program -> FunEnv -> TypeEnv -> TypeMonad FunEnv 

typeCheckProg (A.Prog []) funEnv typeEnv = do throwError $ "Program invalid: main not found"

typeCheckProg (A.Prog ((A.ExDecl f s):t)) funEnv typeEnv = do 
    newFunEnv <- addDeclToFunEnv (A.ExDecl f s) funEnv typeEnv;
    v <- typeCheckProg (A.Prog t) newFunEnv typeEnv;
    return v
    
typeCheckProg (A.Prog ((A.ExDef d):t)) funEnv typeEnv = do
    vd <- typeCheckDefinition d funEnv typeEnv; 
    case t of
        [] -> case d of 
            (A.Rec (A.FunName "main") e) -> do throwError $ "Program invalid: main cannot be recursive";
            (A.Nonrec (A.FunName "main") e) -> do 
                return funEnv
            otherwise -> do throwError $ "Program invalid: main not found"
        otherwise -> case d of 
            (A.Nonrec (A.FunName "main") e) -> do throwError $ "Program invalid: main definition not the last expression"
            otherwise -> do 
                v <- typeCheckProg (A.Prog t) funEnv typeEnv;
                return v    

evalProg :: Program -> Env -> FunEnv -> EvalMonad Value


evalProg (A.Prog []) env funEnv = do throwError $ "Program invalid: main not found"


evalProg (A.Prog ((A.ExDecl f s):t)) env funEnv = do 
    v <- evalProg (A.Prog t) env funEnv;
    return v

evalProg (A.Prog ((A.ExDef def):t)) env funEnv = do
    case t of
        [] -> do
            let (A.Nonrec f e) = def;
            v <- evalEv e env;  
            return v
        otherwise -> do
            case runEvalMonad (addDefToEnv def env) of
                Right newenv -> do
                    v <- evalProg (A.Prog t) newenv funEnv;
                    return v
                Left err -> do throwError $ err

runEvaluator :: Env -> FunEnv -> Program -> Either Err Value

runEvaluator env funEnv p = runEvalMonad (evalProg p env funEnv)

runTypeChecker :: TypeEnv -> FunEnv -> Program -> Either Err TypeEnv

runTypeChecker typeEnv funEnv p = runTypeMonad (typeCheckProg p funEnv typeEnv)

runProgram :: String -> Either Err Value

runProgram program = 
    case P.pProgram $ P.myLexer program of
    Left err -> do
        Left err;
    Right tree -> do 
        funEnv <- runTypeChecker initialTypeEnv initialFunEnv tree;
        finalVal <- runEvaluator initialEnv funEnv tree; 
        case finalVal of 
            (VClos s e env) ->  Left "Main evaluated to closure value, cannot be printed"
            otherwise -> do return $ finalVal 
main = do
    programSourceFile <- getArgs;
    program <- readFile $ head $ programSourceFile;
    case (runProgram program) of 
        Left err -> hPutStrLn stderr err
        Right res -> putStrLn (show res)
 