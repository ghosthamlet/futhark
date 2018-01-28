{-# OPTIONS_GHC -Wall #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | Defunctionalization of typed, monomorphic Futhark programs without modules.
module Main where

import           Control.Monad.RWS
import           Data.List
import           Data.Loc
import qualified Data.Map.Strict as M
import qualified Data.Set as S
import           System.Environment (getArgs)

import           Futhark.Compiler
import           Futhark.MonadFreshNames
import           Futhark.Pipeline
import           Language.Futhark
import           Language.Futhark.Futlib.Prelude

-- | A static value stores additional information about the result of
-- defunctionalization of an expression, aside from the residual expression.
data StaticVal = Dynamic CompType
               | LambdaSV Pattern Exp Env
               | RecordSV [(Name, StaticVal)]
               | ArraySV StaticVal
  deriving (Show)

-- | Environment mapping variable names to their associated static value.
type Env = [(VName, StaticVal)]

emptyEnv :: Env
emptyEnv = []

extendEnv :: VName -> StaticVal -> Env -> Env
extendEnv vn sv = ((vn, sv) :)

combineEnv :: Env -> Env -> Env
combineEnv = (++)

-- | Restricts an environment to a given set of variable names.
-- Preserves the ordering of the mappings in the environment.
restrictEnv :: Names -> Env -> Env
restrictEnv names = filter ((`S.member` names) . fst)

-- | Defunctionalization monad.
newtype DefM a = DefM (RWS Env [Dec] VNameSource a)
  deriving (Functor, Applicative, Monad,
            MonadReader Env,
            MonadWriter [Dec],
            MonadFreshNames)

-- | Run a computation in the defunctionalization monad. Returns the result of
-- the computation, a new name source, and a list of lifted function declations.
runDefM :: VNameSource -> DefM a -> (a, VNameSource, [Dec])
runDefM src (DefM m) = runRWS m emptyEnv src

-- | Looks up the associated static value for a given name in the environment.
lookupVar :: VName -> DefM StaticVal
lookupVar x = do
  env <- ask
  case lookup x env of
    Just sv -> return sv
    Nothing -> error $ "Variable " ++ pretty x ++ " is out of scope."

-- | Defunctionalization of an expression. Returns the residual expression and
-- the associated static value in the defunctionalization monad.
defuncExp :: Exp -> DefM (Exp, StaticVal)
defuncExp expr = case expr of
  Literal{}           -> return (expr, Dynamic $ typeOf expr)

  Parens e loc        -> do (e', sv) <- defuncExp e
                            return (Parens e' loc, sv)

  QualParens qn e loc -> do (e', sv) <- defuncExp e
                            return (QualParens qn e' loc, sv)

  TupLit es loc       -> do (es', svs) <- unzip <$> mapM defuncExp es
                            return (TupLit es' loc, RecordSV $ zip fields svs)
    where fields = map (nameFromString . show) [(1 :: Int) ..]

  RecordLit fs loc    -> do (fs', names_svs) <- unzip <$> mapM defuncField fs
                            return (RecordLit fs' loc, RecordSV names_svs)
    where defuncField (RecordFieldExplicit vn e loc') = do
            (e', sv) <- defuncExp e
            return (RecordFieldExplicit vn e' loc', (vn, sv))
          defuncField (RecordFieldImplicit vn _ loc') = do
            sv <- lookupVar vn
            let tp' = typeFromSV sv
            return (RecordFieldImplicit vn (Info tp') loc', (baseName vn, sv))

  ArrayLit es tp loc  -> do (es', svs) <- unzip <$> mapM defuncExp es
                            case svs of
                              (sv : _) -> return (ArrayLit es' tp loc, ArraySV sv)
                              _ -> error "Empty array literal."

  Range{}             -> undefined
  Empty{}             -> undefined

  Var qn _ loc        -> do sv <- lookupVar (qualLeaf qn)
                            let tp' = typeFromSV sv
                            return (Var qn (Info ([], tp')) loc, sv)

  Ascript e0 _ _      -> defuncExp e0

  LetPat tps pat e1 e2 loc -> do
    unless (null tps) $
      error $ "Received a let-binding with type parameters, "
           ++ "but expected a monomorphic input program."
    (e1', sv1) <- defuncExp e1
    let env = matchPatternSV pat sv1
    (e2', sv2) <- local (env `combineEnv`) $ defuncExp e2
    return (LetPat tps pat e1' e2' loc, sv2)

  LetFun vn (tparams, pats, _, tp, e1) e2 loc -> do
    unless (null tparams) $
      error $ "Received a let-bound function with type parameters, "
           ++ "but expected a monomorphic input program."
    (e1', sv1) <- defuncExp $ Lambda [] pats e1 Nothing tp noLoc
    (e2', sv2) <- local (extendEnv vn sv1) $ defuncExp e2
    let t1 = vacuousShapeAnnotations $ typeOf e1'
    return (LetPat [] (Id vn (Info t1) noLoc) e1' e2' loc, sv2)

  If e1 e2 e3 tp loc -> do
    (e1', _ ) <- defuncExp e1
    (e2', sv) <- defuncExp e2
    (e3', _ ) <- defuncExp e3
    return (If e1' e2' e3' tp loc, sv)

  Apply e1 e2 d _ loc -> do
    (e1', sv1) <- defuncExp e1
    (e2', sv2) <- defuncExp e2
    case sv1 of
      LambdaSV pat e0 env0 -> do
        let env' = matchPatternSV pat sv2
        (e0', sv) <- local (const $ combineEnv env' env0) $ defuncExp e0
        fname <- qualName <$> liftFunDef env0 (typeOf e1') pat sv2 e0'

        let t1 = vacuousShapeAnnotations . toStruct $ typeOf e1'
            t2 = vacuousShapeAnnotations . toStruct $ typeOf e2'
            rettype = typeOf e0'
        return (Parens (Apply (Apply (Var fname (Info ([t1, t2], rettype)) loc)
                               e1' (Info Observe) (Info ([t2], rettype)) loc)
                        e2' d (Info ([], rettype)) loc) noLoc, sv)

      _ -> error $ "Application of an expression with static value " ++ show sv1
                ++ ", but a statically known function was expected."

  Negate e0 loc -> do (e0', sv) <- defuncExp e0
                      return (Negate e0' loc, sv)

  Lambda tparams pats e0 decl tp loc -> do
    unless (null tparams) $
      error $ "Received a lambda with type parameters, "
           ++ "but expected a monomorphic input program."
    -- Extract the first parameter of the lambda and "push" the
    -- remaining ones (if there are any) into the body of the lambda.
    let (pat, e0') = case pats of
          [] -> error "Received a lambda with no parameters."
          [pat'] -> (pat', e0)
          (pat' : pats') -> (pat', Lambda [] pats' e0 decl tp loc)

    env <- reader $ restrictEnv (freeVars expr)
    let fields = map (\(vn, sv) -> RecordFieldImplicit vn
                                   (Info $ typeFromSV sv) noLoc) env
    return (RecordLit fields loc, LambdaSV pat e0' env)

  DoLoop tparams pat e1 form e3 loc -> do
    unless (null tparams) $
      error $ "Received a loop with type parameters, "
           ++ "but expected a monomorphic input program."
    (e1', sv1) <- defuncExp e1
    let env1 = matchPatternSV pat sv1
    (form', env2) <- case form of
      For ident e2  -> do (e2', sv2) <- defuncExp e2
                          return (For ident e2', [(identName ident, sv2)])
      ForIn pat2 e2 -> do (e2', sv2) <- defuncExp e2
                          return (ForIn pat2 e2', matchPatternSV pat2 sv2)
      While e2      -> do (e2', _) <- defuncExp e2
                          return (While e2', [])
    (e3', sv) <- local ((env1 `combineEnv` env2) `combineEnv`) $ defuncExp e3
    return (DoLoop tparams pat e1' form' e3' loc, sv)

  BinOp qn (e1, d1) (e2, d2) t@(Info t') loc -> do
    (e1', _) <- defuncExp e1
    (e2', _) <- defuncExp e2
    return (BinOp qn (e1', d1) (e2', d2) t loc, Dynamic t')

  Project vn e0 _ loc -> do
    (e0', sv0) <- defuncExp e0
    case sv0 of
      RecordSV svs -> case lookup vn svs of
        Just sv -> return (Project vn e0' (Info $ typeFromSV sv) loc, sv)
        Nothing -> error "Invalid record projection."
      _ -> error $ "Projection of an expression with static value " ++ show sv0

  Index e0 idxs loc -> do (e0', sv0) <- defuncExp e0
                          idxs' <- mapM defuncDimIndex idxs
                          case sv0 of
                            ArraySV sv -> return (Index e0' idxs' loc, sv)
                            _ -> error $ "Indexing an expression with "
                                      ++ "static value " ++ show sv0

  Update e1 idxs e2 loc -> do (e1', sv) <- defuncExp e1
                              idxs' <- mapM defuncDimIndex idxs
                              (e2', _) <- defuncExp e2
                              return (Update e1' idxs' e2' loc, sv)

  _ -> error $ "defuncExp: unhandled case " ++ pretty expr


-- | Defunctionalize an indexing of a single array dimension.
defuncDimIndex :: DimIndexBase Info VName -> DefM (DimIndexBase Info VName)
defuncDimIndex (DimFix e1) = DimFix . fst <$> defuncExp e1
defuncDimIndex (DimSlice me1 me2 me3) =
  DimSlice <$> defunc' me1 <*> defunc' me2 <*> defunc' me3
    where defunc' Nothing  = return Nothing
          defunc' (Just e) = Just . fst <$> defuncExp e

-- | Lift a function to a top-level declaration.
liftFunDef :: Env -> CompType -> Pattern -> StaticVal -> Exp -> DefM VName
liftFunDef closure_env env_type pat pat_sv body = do
  fname <- newNameFromString "lifted"
  let params = [ buildEnvPattern closure_env env_type
               , updatePattern pat pat_sv ]
      rettype = vacuousShapeAnnotations $ toStruct $ typeOf body
      dec = ValDec ValBind
        { valBindEntryPoint = False
        , valBindName       = fname
        , valBindRetDecl    = Nothing
        , valBindRetType    = Info rettype
        , valBindTypeParams = []
        , valBindParams     = params
        , valBindBody       = body
        , valBindDoc        = Nothing
        , valBindLocation   = noLoc
        }
  tell [dec]
  return fname

-- | Given a closed over environment and the type of the record argument
-- containing the values for that environment, constructs a record pattern
-- that binds the closed over variables.
buildEnvPattern :: Env -> CompType -> Pattern
buildEnvPattern env (Record fs) = RecordPattern (map buildField env) noLoc
  where buildField (vn, _) =
          let vn' = baseName vn
          in case M.lookup vn' fs of
               Just t -> (vn', Id vn (Info $ vacuousShapeAnnotations t) noLoc)
               Nothing -> error $ "Variable " ++ pretty vn'
                               ++ " occurs in closed over environment, but"
                               ++ " it is missing from the environment record."
buildEnvPattern _ tp =
  error $ "Expected a record type for constructing the "
       ++ "environment pattern, but received type: " ++ pretty tp

-- | Compute the corresponding type for a given static value.
typeFromSV :: StaticVal -> CompType
typeFromSV (Dynamic tp)       = tp
typeFromSV (LambdaSV _ _ env) = typeFromEnv env
typeFromSV (RecordSV ls)      = Record . M.fromList $
                                map (\(vn, sv) -> (vn, typeFromSV sv)) ls
typeFromSV sv = error $ "typeFromSV: missing case for static value " ++ show sv

typeFromEnv :: Env -> CompType
typeFromEnv = Record . M.fromList .
              map (\(vn, sv) -> (baseName vn, typeFromSV sv))

-- | Match a pattern with its static value. Returns an environment with
-- the identifier components of the pattern mapped to the corresponding
-- subcomponents of the static value.
matchPatternSV :: PatternBase f VName -> StaticVal -> Env
matchPatternSV pat@(RecordPattern ps _) sv@(RecordSV ls) =
  let ps' = sortOn fst ps
      ls' = sortOn fst ls
  in if map fst ps' == map fst ls'
     then concat $ zipWith (\(_, p) (_, sv') -> matchPatternSV p sv')
                           ps' ls'
     else error $ "Record pattern " ++ pretty pat
                ++ "did not match record static value " ++ show sv
matchPatternSV (PatternParens pat _) sv = matchPatternSV pat sv
matchPatternSV (Id vn _ _) sv = [(vn, sv)]
matchPatternSV (Wildcard _ _) _ = []
matchPatternSV (PatternAscription pat _) sv = matchPatternSV pat sv
matchPatternSV pat sv = error $ "Tried to match pattern " ++ pretty pat
                             ++ "with static value " ++ show sv ++ "."

-- | Given a pattern and the static value for the defunctionalized argument,
-- update the pattern to reflect the changes in the types.
updatePattern :: Pattern -> StaticVal -> Pattern
updatePattern (TuplePattern ps loc) (RecordSV svs) =
  TuplePattern (zipWith updatePattern ps $ map snd svs) loc
updatePattern (RecordPattern ps loc) (RecordSV svs)  =
  RecordPattern (zipWith (\(n, p) (_, sv) -> (n, updatePattern p sv)) ps svs) loc
updatePattern (PatternParens pat loc) sv =
  PatternParens (updatePattern pat sv) loc
updatePattern (Id vn _ loc) sv =
  Id vn (Info . vacuousShapeAnnotations $ typeFromSV sv) loc
updatePattern (Wildcard _ loc) sv =
  Wildcard (Info . vacuousShapeAnnotations $ typeFromSV sv) loc
updatePattern (PatternAscription pat _) sv =
  updatePattern pat sv
updatePattern pat sv =
  error $ "Tried to update pattern " ++ pretty pat
       ++ "to reflect the static value " ++ show sv

-- | Compute the set of free variables of an expression.
freeVars :: Exp -> Names
freeVars expr = case expr of
  Literal _ _          -> S.empty
  Parens e _           -> freeVars e
  QualParens _ _ _     -> undefined  -- TODO
  TupLit es _          -> foldMap freeVars es
  RecordLit fs _       -> foldMap freeVarsField fs
    where freeVarsField (RecordFieldExplicit _ e _)  = freeVars e
          freeVarsField (RecordFieldImplicit vn _ _) = S.singleton vn
  ArrayLit es _ _      -> foldMap freeVars es
  Range e me incl _ _  -> freeVars e <> foldMap freeVars me <>
                          foldMap freeVars incl
  Empty _ _ _          -> S.empty
  Var qn _ _           -> S.singleton $ qualLeaf qn
  Ascript e _ _        -> freeVars e
  LetPat _ pat e1 e2 _ -> freeVars e1 <> (freeVars e2 S.\\ patternVars pat)
  LetFun vn (_, pats, _, _, e1) e2 _ ->
    (freeVars e1 `S.difference` foldMap patternVars pats) <>
    (freeVars e2 `S.difference` S.singleton vn)
  If e1 e2 e3 _ _           -> freeVars e1 <> freeVars e2 <> freeVars e3
  Apply e1 e2 _ _ _         -> freeVars e1 <> freeVars e2
  Negate e _                -> freeVars e
  Lambda _ pats e0 _ _ _    -> freeVars e0 S.\\ foldMap patternVars pats
  OpSection _ _ _ _ _       -> S.empty
  OpSectionLeft  _ e _ _ _  -> freeVars e
  OpSectionRight _ e _ _ _  -> freeVars e
  DoLoop _ pat e1 form e3 _ -> let (e2fv, e2ident) = formVars form
                               in freeVars e1 <> e2fv <>
                                  (freeVars e3 S.\\ (patternVars pat <> e2ident))
    where formVars (For ident e2) = (freeVars e2, S.singleton $ identName ident)
          formVars (ForIn p e2)   = (freeVars e2, patternVars p)
          formVars (While e2)     = (freeVars e2, S.empty)
  BinOp _ (e1, _) (e2, _) _ _ -> freeVars e1 `S.union` freeVars e2
  Project _ e _ _ -> freeVars e
  _ -> error $ "freeVars: unhandled case " ++ pretty expr

-- | Extract all the variable names bound in a pattern.
patternVars :: Pattern -> Names
patternVars (TuplePattern pats _)     = S.unions $ map patternVars pats
patternVars (RecordPattern fs _)      = S.unions $ map (patternVars . snd) fs
patternVars (PatternParens pat _)     = patternVars pat
patternVars (Id vn _ _)               = S.singleton vn
patternVars (Wildcard _ _)            = S.empty
patternVars (PatternAscription pat _) = patternVars pat

-- | Defunctionalize a top-level value binding. Returns the transformed result
-- as well as a function that extends the environment with a binding form the
-- bound name to the static value of the transformed body.
defuncValBind :: ValBind -> DefM (ValBind, Env -> Env)
defuncValBind valbind@(ValBind _ name _ rettype tparams params body _ _) = do
  unless (null tparams) $
    error $ "Received a top-level value declaration with type parameters, "
         ++ "but the defunctionalizer expects a monomorphic input program."
  let body' | null params = body
            | otherwise   = Lambda [] params body Nothing rettype noLoc
  (body'', sv) <- defuncExp body'
  let rettype' = vacuousShapeAnnotations . toStruct $ typeOf body''
  return ( valbind { valBindRetDecl = Nothing
                   , valBindRetType = Info rettype'
                   , valBindParams  = []
                   , valBindBody    = body''
                   }
         , extendEnv name sv)

defuncDecs :: [Dec] -> DefM [Dec]
defuncDecs [] = return []
defuncDecs (ValDec valbind : ds) = do
  (valbind', env) <- defuncValBind valbind
  ds' <- local env $ defuncDecs ds
  return $ ValDec valbind' : ds'
defuncDecs (dec : _) =
  error $ "Received declaration " ++ pretty dec
       ++ ", but can only handle value declarations at this point."

-- | Transform a list of top-level declarations. May produce new lifted function
-- definitions, which are placed in front of the resulting list of declarations.
transformProg :: MonadFreshNames m => [Dec] -> m [Dec]
transformProg decs = modifyNameSource $ \namesrc ->
  let (decs', namesrc', liftedDecs) = runDefM namesrc $ defuncDecs decs
  in (liftedDecs ++ decs', namesrc')


main :: IO ()
main = do
  [fp] <- getArgs
  let prelude = preludeBasis  -- or emptyBasis for smaller program.
  (_, (_, fileMod):_, namesrc) <-
    either (error . show) return =<<
    runFutharkM (readProgram False prelude mempty fp) False
  let decs = progDecs $ fileProg fileMod
      (decs', _, liftedDecs) = runDefM namesrc $ defuncDecs decs
  mapM_ (putStrLn . pretty) (liftedDecs ++ decs')
