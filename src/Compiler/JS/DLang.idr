module Compiler.JS.DLang

import public Data.Vect
import public Data.NameMap

import public Core.Context
import public Core.Name
import public Core.TT

%default total

public export
data DTerm : List Name -> Type where
  DLocal :
    {name : _}
    -> (idx : Nat)
    -> IsVar name idx vars  -- we hope to erase this
    -> DTerm vars

  DRef : NameType -> (name : Name) -> DTerm vars
  DCall : (f : Name) -> (args : List (DTerm vars)) -> DTerm vars
  DApp : (f : DTerm vars) -> (args : List (DTerm vars)) -> DTerm vars
  DDelay : DTerm vars -> DTerm vars
  DForce : DTerm vars -> DTerm vars
  DConst : Constant -> DTerm vars
  DErased : DTerm vars

mutual
  public export
  data DCaseTree : List Name -> Type where
       DCase : {name : _} ->
              (idx : Nat) ->
              IsVar name idx vars ->
              (scTy : Term vars) -> List (DCaseAlt vars) ->
              DCaseTree vars
       DSTerm : DTerm vars -> DCaseTree vars
       DUnmatched : (msg : String) -> DCaseTree vars
       DImpossible : DCaseTree vars

  public export
  data DCaseAlt : List Name -> Type where
       DConCase : Name -> (tag : Int) -> (args : List Name) ->
                 DCaseTree (args ++ vars) -> DCaseAlt vars
       DDelayCase : (ty : Name) -> (arg : Name) ->
                   DCaseTree (ty :: arg :: vars) -> DCaseAlt vars
       DConstCase : Constant -> DCaseTree vars -> DCaseAlt vars
       DefaultCase : DCaseTree vars -> DCaseAlt vars

public export
record DDef where
  constructor MkDDef
  args : List Name
  body : DCaseTree args

record DCState where
  constructor MkDCState

record Env where
  constructor MkEnv

public export
data Failure = Debug String

record DC (a : Type) where
  constructor MkDC
  runDC : Env -> DCState -> Either Failure (DCState, List DDef, a)

Functor DC where
  map f (MkDC g) = MkDC $ \env, st => case g env st of
    Left fail => Left fail
    Right (st', cs, x) => Right (st', cs, f x)

Applicative DC where
  pure x = MkDC $ \env, st => Right (st, neutral, x)
  (<*>) (MkDC f) (MkDC g) = MkDC $ \env, st =>
    case f env st of
        Left fail => Left fail
        Right (st', cs', f') => case g env st' of
            Left fail => Left fail
            Right (st'', cs'', x'') => Right (st'', cs' <+> cs'', f' x'')

Monad DC where
  (>>=) (MkDC f) g = MkDC $ \env, st =>
    case f env st of
        Left fail => Left fail
        Right (st', cs, x) => case g x of
            MkDC h => case h env st' of
                Left fail => Left fail
                Right (st'', cs'', x'') => Right (st'', cs <+> cs'', x'')

getEnv : DC Env
getEnv = MkDC $ \env, st => Right (st, neutral, env)

throw : Failure -> DC a
throw err = MkDC $ \env, st => Left err

dcTm : Term vars -> DC (DTerm vars)
dcTm tm = ?rhs

export
defunctionalise : ClosedTerm -> Either Failure (List DDef, DTerm [])
defunctionalise tm =
  case runDC (dcTm tm) MkEnv MkDCState of
    Right (_, ddefs, dtm) => Right (ddefs, dtm)
    Left err => Left err
