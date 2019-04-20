## Elab commands

```idris
-- > :browse Pruviloj.Core
Names:
  Infer : Type
  MkInfer : (a : Type) -> a -> Infer
  andThen : Elab (List TTName) -> Elab a -> Elab (List a)
  applyAs : Raw -> Raw -> String -> Elab TTName
  bindPat : Elab ()
  both : Raw -> TTName -> TTName -> Elab ()
  construct : Elab (List TTName)
  equiv : Raw -> Elab TTName
  exact : Raw -> Elab ()
  forget : TT -> Elab Raw
  forget' : List TTName -> TT -> Elab Raw
  getTTType : Raw -> Elab TT
  goalType : Elab Raw
  headName : Raw -> Maybe TTName
  hypothesis : Elab ()
  inHole : TTName -> Elab a -> Elab (Maybe a)
  inferType : Elab () -> Elab (TT, TT)
  intros : Elab (List TTName)
  nameFrom : TTName -> Elab TTName
  newHole : String -> Raw -> Elab TTName
  refine : Raw -> Elab (List TTName)
  reflexivity : Elab ()
  remember : TTName -> Raw -> Elab TTName
  repeatUntilFail : Elab () -> Elab ()
  simple : m () -> m ()
  skip : Applicative f => f ()
  symmetry : Elab ()
  symmetryAs : Raw -> String -> Elab TTName
  try : Alternative f => f a -> f ()
  unproduct : Raw -> Elab ()
-- > :browse Language.Reflection.Elab.Tactics
  addImplementation : TTName -> TTName -> Elab ()
  apply : Raw -> List Bool -> Elab (List TTName)
  attack : Elab ()
  check : List (TTName, Binder TT) -> Raw -> Elab (TT, TT)
  claim : TTName -> Raw -> Elab ()
  compute : Elab ()
  converts : TT -> TT -> Elab ()
  convertsInEnv : List (TTName, Binder TT) -> TT -> TT -> Elab ()
  currentNamespace : Elab (List String)
  debug : Elab a
  debugMessage : List ErrorReportPart -> Elab a
  declareDatatype : TyDecl -> Elab ()
  declareType : TyDecl -> Elab ()
  defineDatatype : DataDefn -> Elab ()
  defineFunction : FunDefn Raw -> Elab ()
  fail : List ErrorReportPart -> Elab a
  fill : Raw -> Elab ()
  focus : TTName -> Elab ()
  forall : TTName -> Raw -> Elab ()
  gensym : String -> Elab TTName
  getEnv : Elab (List (TTName, Binder TT))
  getGoal : Elab (TTName, TT)
  getGuess : Elab TT
  getHoles : Elab (List TTName)
  getSourceLocation : Elab SourceLocation
  intro : TTName -> Elab ()
  intro' : Elab ()
  isTCName : TTName -> Elab Bool
  letbind : TTName -> Raw -> Raw -> Elab ()
  lookupArgs : TTName -> Elab (List (TTName, List FunArg, Raw))
  lookupArgsExact : TTName -> Elab (TTName, List FunArg, Raw)
  lookupDatatype : TTName -> Elab (List Datatype)
  lookupDatatypeExact : TTName -> Elab Datatype
  lookupFunDefn : TTName -> Elab (List (FunDefn TT))
  lookupFunDefnExact : TTName -> Elab (FunDefn TT)
  lookupTy : TTName -> Elab (List (TTName, NameType, TT))
  lookupTyExact : TTName -> Elab (TTName, NameType, TT)
  matchApply : Raw -> List Bool -> Elab (List TTName)
  metavar : TTName -> Elab ()
  normalise : List (TTName, Binder TT) -> TT -> Elab TT
  operatorFixity : String -> Elab Fixity
  patbind : TTName -> Elab ()
  patvar : TTName -> Elab ()
  resolveTC : TTName -> Elab ()
  rewriteWith : Raw -> Elab ()
  runElab : Raw -> Elab () -> Elab (TT, TT)
  search : Elab ()
  search' : Int -> List TTName -> Elab ()
  solve : Elab ()
  sourceLocation : Elab ()
  tryCatch : Elab a -> (Err -> Elab a) -> Elab a
  unfocus : TTName -> Elab ()
  whnf : TT -> Elab TT
```