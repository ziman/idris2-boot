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
import Text.Pretty

import Compiler.JS.DLang
import public Compiler.Common

%default total

compile : Ref Ctxt Defs -> ClosedTerm -> Either String Doc
compile ctx tm = ?rhs

compileExpr :
    Ref Ctxt Defs -> (execDir : String)
    -> ClosedTerm -> (outfile : String)
    -> Core (Maybe String)
compileExpr ctx execDir tm outfile =
  case compile ctx tm of
    Left err => throw (InternalError err)  -- TODO
    Right doc => do
      coreLift $ writeFile outfile (render "  " doc)
      pure (Just outfile)

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
