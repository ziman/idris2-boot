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

import Core.CompileExpr
import Compiler.CompileExpr

import public Compiler.Common

%default total

compile : Ref Ctxt Defs -> ClosedTerm -> Either String Doc
compile ctx tm = ?rhs

docDefs :: List CDef -> Doc
docDefs = ?rhs_docDefs

docMain :: CExpr [] -> Doc
docMain = ?rhs_docMain

-- Convert the name to scheme code
-- (There may be no code generated, for example if it's a constructor)
export
getCDef : {auto c : Ref Ctxt Defs} -> Defs -> Name -> Core CDef
getCDef defs n =
  lookupCtxtExact n (gamma defs) >>= \case
    Nothing => throw $ InternalError ("Compiling undefined name " ++ show n)
    Just d => case compexpr d of
      Nothing => throw $ InternalError ("No compiled definition for " ++ show n)
      Just cd => pure cd

compileExpr :
    Ref Ctxt Defs -> (execDir : String)
    -> ClosedTerm -> (outfile : String)
    -> Core (Maybe String)
compileExpr ctx execDir tmMain outfile = do
  defs <- get Ctxt
  (ns, tags) <- findUsedNames tm
  cdefs <- traverse (getDef defs) ns
  cmain <- compileExp tags tmMain
  rts <- readDataFile "javascript/support.js"

  let srcDoc =
        text rts
        $$ docDefs cdefs
        $$ docMain cmain

  Right () <- coreLift $ writeFile outfile (render "  " srcDoc)
     | Left err => throw (FileErr outfile err)
  coreLift $ chmod outfile 0o755
  pure ()

compileExpr : Ref Ctxt Defs -> (execDir : String) ->
              ClosedTerm -> (outfile : String) -> Core (Maybe String)
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
