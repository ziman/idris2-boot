module Compiler.JS.Javascript

import Data.NameMap
import Data.Vect
import System
import System.Info

import Core.Context
import Core.Directory
import Core.Name
import Core.Options
import Core.TT
import Utils.Hex

import public Compiler.Common

%default total

compile : Ref Ctxt Defs -> ClosedTerm -> Either String String
compile ctx tm = ?rhs

compileExpr :
    Ref Ctxt Defs -> (execDir : String)
    -> ClosedTerm -> (outfile : String)
    -> Core (Maybe String)
compileExpr ctx execDir tm outfile =
  case compile ctx tm of
    Left err => throw (InternalError err)  -- TODO
    Right src => do
      coreLift $ writeFile outfile src
      pure (Just src)

executeExpr :
    Ref Ctxt Defs -> (execDir : String)
    -> ClosedTerm -> Core ()
executeExpr ctx execDir tm = do
  fnameTmp <- coreLift tmpName
  compileExpr ctx execDir tm fnameTmp
  coreLift $ system ("node " ++ fnameTmp)
  pure ()

export
codegenJavascript : Codegen
codegenJavascript = MkCG compileExpr executeExpr

