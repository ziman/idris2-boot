module Compiler.JS.DLang

import public Data.Vect
import public Data.NameMap

import public Core.Context
import public Core.Name
import public Core.TT

%default total
%access public export

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
  data DCaseTree : List Name -> Type where
       DCase : {name : _} ->
              (idx : Nat) ->
              IsVar name idx vars ->
              (scTy : Term vars) -> List (DCaseAlt vars) ->
              DCaseTree vars
       DSTerm : DTerm vars -> DCaseTree vars
       DUnmatched : (msg : String) -> DCaseTree vars
       DImpossible : DCaseTree vars

  data DCaseAlt : List Name -> Type where
       DConCase : Name -> (tag : Int) -> (args : List Name) ->
                 DCaseTree (args ++ vars) -> DCaseAlt vars
       DDelayCase : (ty : Name) -> (arg : Name) ->
                   DCaseTree (ty :: arg :: vars) -> DCaseAlt vars
       DConstCase : Constant -> DCaseTree vars -> DCaseAlt vars
       DefaultCase : DCaseTree vars -> DCaseAlt vars

record DDef where
  constructor MkDDef
  args : List Name
  body : DCaseTree args
