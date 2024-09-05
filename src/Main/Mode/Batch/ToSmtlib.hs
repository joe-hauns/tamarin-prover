{-# LANGUAGE TypeFamilies       #-}

module Main.Mode.Batch.ToSmtlib (
    toSmtlib
  , toFolSignature
  , toFolProblem
  , Outputable(..)
  ) where

import Items.OpenTheoryItem
import TheoryObject
import Theory.Model
import Data.Maybe
import Data.List (intercalate,genericIndex,intersperse)
import Data.Functor
import Data.ByteString.Char8 (unpack)
import Theory
import Data.Set
import Control.Monad

data Smtlib = Smtlib
  deriving (Show)

toSmtlib :: FolSignature -> Smtlib
toSmtlib _ = Smtlib

class Outputable a where
  outputNice :: a -> IO ()

data FolSort = FolSortMsg
             | FolSortFact -- remove
             | FolSortNat
             | FolSortTemp
             | FolSortBool
             | FolSortRule
             | FolSortLin
             | FolSortPer
             | FolSortAct
  deriving (Show,Ord,Eq)

data FolFuncId = Cnt -- remoce
               | FSEq FolSort
               | FSLess
               | Label
               | End
               | MsgSymbol FunSym
               | FactSymbol FactTag
               | FolNatAdd
               | FolNatSucc
               | FolNatZero
               | FolPredPre
               | FolPredCon
               | FolPredAct
               | FolFuncPre
               | FolFuncCon
               | FolRule SupportedRule
               | FolFuncEquals
               | FolFuncFresh
               | FolFuncPub
  deriving (Show,Ord,Eq)

data FolTerm = FolApp FolFuncId [FolTerm]
             | FolVar FolVar
  deriving (Show)

data FolFormula =
    FolAtom FolTerm
  | FolBool !Bool
  | FolNot FolFormula
  | FolConn Connective FolFormula FolFormula
  | FolQua !Quantifier FolVar FolFormula
  deriving (Show)

data FolProblem = FolProblem {
    _fpSig     :: FolSignature
  , _fpRules   :: [SupportedRule]
  , _fpFormula :: [FolGoal]
  }
  deriving (Show)

data FolSignature = FolSignature {
    _fsigSorts :: [ FolSort ]
  , _fsigFuncs :: [ FolFuncId ]
  }
  deriving (Show)

sortName :: FolSort -> String
sortName FolSortMsg = "msg"
sortName FolSortFact = "fact"
sortName FolSortNat = "nat"
sortName FolSortTemp = "temp"
sortName FolSortBool = "bool"
sortName FolSortRule = "rule"
sortName FolSortLin = "lin"
sortName FolSortPer = "per"
sortName FolSortAct = "act"

instance Outputable FolSignature where
  outputNice (FolSignature sorts funcs) = do
    putStrLn "sorts: "
    forM_ sorts $ \s ->  do
      putStrLn $ "  " ++ show s
    putStrLn ""
    putStrLn "funcs:"
    forM_ funcs $ \f ->  do
      putStrLn $ "  " ++ folFuncName f ++ ": " ++ ty (folFuncSig f)
      where ty ([], r) = sortName r
            ty ([a], r) = sortName a ++ " -> " ++ sortName r
            ty (as, r) = "(" ++ intercalate ", " (sortName <$> as) ++ ") -> " ++ sortName r


instance Outputable FolSort where
  outputNice = putStr . sortName

instance Outputable FolFuncId where
  outputNice = putStr . folFuncName

instance Outputable FolGoal where
  outputNice (FolGoal name formula) = do
    putStr $ "goal " ++ name ++ ": "
    outputNice formula

instance Outputable SupportedRule where
  outputNice (SupportedRule name ps as cs) = do
    let name' = case name of Just n  -> " " ++ n ++ " "
                             Nothing -> ""
    putStr $  "rule" ++ name' ++ ": "
    outputFacts ps
    putStr  " --"
    outputFacts as
    putStr  "-> "
    outputFacts cs
      where outputFacts [] = putStr "[]"
            outputFacts fs  = do
              putStr "[ "
              sequence_ $ intersperse (putStr ", ") (outputNice . factT () <$> fs)
              putStr " ]"


timeVar :: FolTerm
timeVar = FolVar ("__time__", FolSortTemp)
-- TODO clean var name

(/\) :: FolFormula -> FolFormula  -> FolFormula
(/\) = FolConn And

(\/) :: FolFormula -> FolFormula  -> FolFormula
(\/) = FolConn Or

(<->) :: FolFormula -> FolFormula  -> FolFormula
(<->) = FolConn Iff

neg :: FolFormula -> FolFormula
neg = FolNot

($$) :: FolFuncId -> [FolTerm] -> FolTerm
($$) = FolApp

ex :: FolVar -> FolFormula -> FolFormula
ex = FolQua Ex

qMany :: Quantifier -> [FolVar] -> FolFormula -> FolFormula
qMany q [] = id
qMany q (v:vs) = FolQua q v . qMany q vs

ex' :: [FolVar] -> FolFormula -> FolFormula
ex' = qMany Ex

allQ' :: [FolVar] -> FolFormula -> FolFormula
allQ' = qMany All

allQ :: FolVar -> FolFormula -> FolFormula
allQ = FolQua All

aggregate :: a -> (a -> a -> a) -> [a] -> a
aggregate start _ []  = start
aggregate _ _ [x] = x
aggregate s op (x:xs) = op x (aggregate s op xs)

conj :: [FolFormula] -> FolFormula
conj = aggregate (FolBool True) (/\)

disj :: [FolFormula] -> FolFormula
disj = aggregate (FolBool False) (\/)

succT :: FolTerm -> FolTerm
succT t = FolNatSucc $$ [t]

addNat :: Int -> FolTerm  -> FolTerm
addNat i t
  | i == 0 = t
  | i > 0  = succT $ addNat (i - 1) t
  | otherwise  = error "trying to add negative natural number"

type FolVar = (String, FolSort)

ruleVars :: SupportedRule -> [FolVar]
ruleVars (SupportedRule _ ls as rs) = Data.Set.toList
                                    $ Data.Set.fromList
                                    $ (ls ++ as ++ rs) >>= vars . factT ()

vars :: FolTerm -> [FolVar]
vars (FolVar v) = [v]
vars (FolApp _ as) = as >>= vars

ruleTerm :: SupportedRule -> FolTerm
ruleTerm r = FolRule r $$ (FolVar <$> ruleVars r)

sumT :: [FolTerm] -> FolTerm
sumT = aggregate (FolNatZero$$[]) (\l r -> FolNatAdd$$[l,r])

equalsT :: FolTerm -> FolTerm -> FolTerm
equalsT l r = FolFuncEquals $$ [l, r]

translateRule :: SupportedRule -> FolFormula
translateRule rule@(SupportedRule _name ls as rs) =
  allQ' (ruleVars rule) (
      defFunAsSum pre ls
   /\ defFunAsSum con rs
   /\ defPredAsDisj (\x y -> FolAtom $ FolPredPre $$ [x, y]) (persistent ls)
   /\ defPredAsDisj (\x y -> FolAtom $ FolPredCon $$ [x, y]) (persistent rs)
   /\ defPredAsDisj (\x y -> FolAtom $ FolPredAct $$ [x, y]) (factT () <$> as)
  )
  where
    defPredAsDisj p items =
      let f = ("f", FolSortPer)
      in allQ f (p ruleT (FolVar f) <-> disj [ x ~~ FolVar f | x <- items ])
    defFunAsSum fun items =
      let f = ("f", FolSortLin)
      in allQ f (fun ruleT (FolVar f) ~~ sumT [ equalsT x (FolVar f) | x <- linear items ])
    facts mult s = [ factT () f | f <- s
                                , factMultiplicity f == mult ]
    linear = facts Linear
    persistent = facts Persistent
    pre s t = FolFuncPre $$ [s, t]
    con s t = FolFuncCon $$ [s, t]
    ruleT = ruleTerm rule
  --    neg (FolAtom (End$$[timeVar]))
  -- /\ conj [ ex "n" FolSortNat ( )  | f <- linear l ]
  -- -- todo clean var names
  --   where 
  --      facts mult s = [ factT () f | f <- s
  --                                  ,  factMultiplicity f == mult ]
  --      linear = facts Linear
  --      -- persistent = facts Persistent



instance Outputable FolProblem where
  outputNice (FolProblem sig rules goals) = do
    outputNice sig
    putStrLn ""
    putStrLn ""
    forM_ rules $ \rule -> do
      outputNice rule
      putStrLn ""
      outputNice (translateRule rule)
      putStrLn ""
    putStrLn ""
    putStrLn ""
    forM_ goals $ \goal -> do
      outputNice goal
      putStrLn ""

instance Outputable FolTerm where
  outputNice (FolVar (v, _)) = putStr v
  outputNice (FolApp f ts) = do
    outputNice f
    putStr "("
    sequence_ $ intersperse (putStr ",") (fmap outputNice ts)
    putStr ")"

instance Outputable FolFormula where
  outputNice (FolAtom t) = outputNice t
  outputNice (FolBool t) = putStr $ show t
  outputNice (FolNot t) = sequence_ [putStr "~", outputNice t]
  outputNice (FolConn c s t) = do
    putStr "("
    outputNice s
    putStr (case c of
      And -> " /\\ "
      Or -> " \\/ "
      Imp -> " -> "
      Iff -> " <-> ")
    outputNice t
    putStr ")"
  outputNice (FolQua q (v, s) f) = do
    putStr (case q of
      All -> "∀"
      Ex -> "∃")
    putStr $ v ++ ": "
    outputNice s
    putStr "("
    outputNice f
    putStr ")"

data SupportedRule = SupportedRule {
      _srName :: Maybe String
    , _srPrems :: [LNFact]
    , _srActs :: [LNFact]
    , _srConcls :: [LNFact]
    }
    deriving (Show,Eq,Ord)

folFuncSig :: FolFuncId -> ([FolSort], FolSort)
folFuncSig Cnt = ([FolSortTemp, FolSortFact], FolSortNat)
folFuncSig Label = ([FolSortTemp, FolSortFact], FolSortBool)
folFuncSig End = ([FolSortTemp], FolSortBool)
folFuncSig (MsgSymbol (NoEq (_name, (arity, _priv, _constr)))) = ([FolSortMsg | _ <- [1..arity]], FolSortMsg)
folFuncSig (MsgSymbol (AC _ac)) = ([FolSortMsg, FolSortMsg], FolSortMsg)
folFuncSig (MsgSymbol (C EMap)) = error "EMap message not supported (yet)"
folFuncSig (MsgSymbol List) = error "List message not supported (yet)"
folFuncSig (FactSymbol tag) = ([FolSortMsg | _ <- [1..factTagArity tag]], FolSortFact)
folFuncSig (FSEq s) = ([s, s], FolSortBool)
folFuncSig FSLess = ([FolSortTemp, FolSortTemp], FolSortBool)
folFuncSig FolNatSucc = ([FolSortNat], FolSortNat)
folFuncSig FolNatZero = ([], FolSortNat)
folFuncSig FolNatAdd = ([FolSortNat, FolSortNat], FolSortNat)
folFuncSig FolPredPre = ([FolSortRule, FolSortPer], FolSortBool)
folFuncSig FolPredCon = ([FolSortRule, FolSortPer], FolSortBool)
folFuncSig FolPredAct = ([FolSortRule, FolSortAct], FolSortBool)
folFuncSig FolFuncPre = ([FolSortRule, FolSortLin], FolSortNat)
folFuncSig FolFuncCon = ([FolSortRule, FolSortLin], FolSortNat)
folFuncSig (FolRule r) = (FolSortMsg <$ ruleVars r, FolSortRule)
folFuncSig FolFuncEquals = ([FolSortLin, FolSortLin], FolSortNat)
folFuncSig FolFuncFresh = ([FolSortNat], FolSortMsg)
folFuncSig FolFuncPub = ([FolSortNat], FolSortMsg)

folFuncName :: FolFuncId -> String
folFuncName FolNatSucc = "s"
folFuncName FolNatZero = "zero"
folFuncName Cnt = "cnt"
folFuncName Label = "label"
folFuncName End = "end"
folFuncName (FSEq _srt) = "="
folFuncName FSLess = "<"
folFuncName (MsgSymbol (NoEq (name, (_arity, _priv, _constr)))) = unpack name
folFuncName (MsgSymbol (AC ac)) = show ac
folFuncName (MsgSymbol (C EMap)) = show EMap
folFuncName (MsgSymbol List) = show List
folFuncName (FactSymbol tag) = factTagName tag
  where
    factTagName (ProtoFact _ name _) = name
    factTagName FreshFact = "Fr"
    factTagName OutFact  = "Out"
    factTagName InFact = "In"
    factTagName KUFact = "KU"
    factTagName KDFact = "KD"
    factTagName DedFact = "Ded"
    factTagName TermFact = "Term"
folFuncName FolNatAdd = "add"
folFuncName FolPredPre = "Pre"
folFuncName FolPredCon = "Con"
folFuncName FolPredAct = "Act"
folFuncName FolFuncPre = "pre"
folFuncName FolFuncCon = "con"
folFuncName (FolRule (SupportedRule (Just name) _ _ _)) = "r" ++ name
folFuncName (FolRule r@(SupportedRule Nothing _ _ _)) = show r
folFuncName FolFuncEquals = "equals"
folFuncName FolFuncFresh = "fresh"
folFuncName FolFuncPub = "pub"

assertEq :: (Show a, Eq a) => a -> a -> String -> Bool
assertEq l r name | l == r    = True
                  | otherwise = error ("expected " ++ name ++ " == " ++ show l ++ ". is: " ++ show r)

assertEmpty :: Show a => [a] -> String -> Bool
assertEmpty [] _name = True
assertEmpty xs name = error ("expected " ++ name ++ " to be empty. is: " ++ show xs)


toFolRules :: [TheoryItem OpenProtoRule p s] -> [SupportedRule]
toFolRules = mapMaybe toRule
  where toRule (RuleItem (OpenProtoRule
                 (Rule (ProtoRuleEInfo
                           name
                           attr -- <- _preAttributes 
                           restriction -- <- _preRestriction =
                           )
                       prems
                       concs
                       acts
                       newVars -- newVars
                       )
                   ruleAC -- ruleAC
                   ))
         |    assertEmpty attr "attr"
           && assertEmpty newVars "newVars"
           && assertEmpty ruleAC "ruleAC"
           && assertEmpty restriction "restriction"  = Just (SupportedRule name' prems acts concs)
           where name' = case name of
                    FreshRule -> Nothing
                    StandRule r -> Just r
        toRule (RuleItem r) = error ("unexpected rule" ++ show r)
        toRule _ = Nothing

-- TODO assertions of _options, etc
assertEmptyS x = assertEmpty (Data.Set.toList x)

getTag :: LNFact -> FactTag
getTag (Fact tag factAnnotations _factTerms)
 | assertEmptyS factAnnotations "factAnnotations" = tag

toFolSignature :: OpenTheory -> FolSignature
toFolSignature (Theory _name _inFile _heuristic _tactic signature _cache items _options _isSapic) = FolSignature {
    _fsigSorts = sorts
  , _fsigFuncs = [ Cnt, Label, End, FSLess ]
              ++ fmap FSEq sorts
              ++ fmap MsgSymbol (Data.Set.toList $ funSyms $ _sigMaudeInfo signature)

              ++ fmap FactSymbol (toList $ Data.Set.fromList (tags ++ [ FreshFact, OutFact, InFact, KUFact, KDFact, DedFact ]))
  }
 where tags = toFolRules items
          >>= (\(SupportedRule _name l p r) -> l ++ p ++ r)
          <&> getTag
       sorts = [ FolSortMsg, FolSortFact, FolSortNat, FolSortTemp, FolSortBool]


toFolProblem :: OpenTheory -> FolProblem
toFolProblem th = FolProblem (toFolSignature th) (toFolRules $ _thyItems th) (mapMaybe toFolGoal $ _thyItems th)

data FolGoal = FolGoal String FolFormula
  deriving (Show)

toFolGoal :: OpenTheoryItem -> Maybe FolGoal
toFolGoal (LemmaItem (Lemma name AllTraces formula _attributes _proof)) = Just (FolGoal name (toFolFormula [] formula))
toFolGoal _ = Nothing

type QuantScope = [FolVar]

toFolFormula :: QuantScope -> LNFormula -> FolFormula
toFolFormula qs (Ato a) = toFolAtom qs a
toFolFormula _ (TF x) = FolBool x
toFolFormula qs (Not x) = FolNot (toFolFormula qs x)
toFolFormula qs (Conn c l r) = FolConn c (toFolFormula qs l) (toFolFormula qs r)
toFolFormula qs (Qua q (v,s) f) = FolQua q (v, s') (toFolFormula ((v, s'):qs) f)
  where s' = toFolSort s

toFolSort :: LSort -> FolSort
toFolSort LSortPub   = undefined
toFolSort LSortFresh = undefined
toFolSort LSortMsg =  FolSortMsg
toFolSort LSortNode = FolSortTemp
toFolSort srt@LSortNat =  error $ "unexpected sort: " ++ show srt


class PVar a where
  type PVarCtx a

  varFromContext :: PVarCtx a -> a -> FolTerm

instance PVar (BVar LVar) where
  type PVarCtx (BVar LVar) = QuantScope

  varFromContext qs (Bound deBrujinIdx) = FolVar (qs `genericIndex` deBrujinIdx)
  varFromContext _ (Free v) = varFromContext () v

instance PVar LVar where
  type PVarCtx LVar = ()

  -- varFromContext () (LVar name sort _idx) = FolVar (name, (toFolSort sort))
  varFromContext () (LVar name LSortPub _idx) = FolFuncPub $$ [FolVar (name, FolSortNat)]
  varFromContext () (LVar name LSortFresh _idx) = FolFuncFresh $$ [FolVar (name, FolSortNat)]
  varFromContext () (LVar name sort _idx) = FolVar (name, toFolSort sort)

factT :: PVar v => PVarCtx v -> Fact (VTerm Name v) -> FolTerm
factT qs (Fact tag factAnnotations terms)
 | assertEmptyS factAnnotations "factAnnotations"
   = FolApp (FactSymbol tag) (toFolTerm qs <$> terms)
 | otherwise = undefined

sortOf :: FolTerm -> FolSort
sortOf (FolApp f _) = snd (folFuncSig f)
sortOf (FolVar (_, s)) = s

(~~) :: FolTerm -> FolTerm -> FolFormula
(~~) l r = FolAtom $ FolApp (FSEq (sortOf l)) [l, r]

labelT :: FolTerm -> FolTerm -> FolFormula
labelT l r = FolAtom $ FolApp Label [l, r]

toFolAtom :: (PVar v, Show v) => PVarCtx v -> ProtoAtom Unit2 (VTerm Name v) -> FolFormula
toFolAtom qs (Action term fact)  = labelT (toFolTerm qs term) (factT qs fact)
toFolAtom qs (EqE s t) = toFolTerm qs s ~~ toFolTerm qs t
toFolAtom qs (Less s t) = FolAtom $ FolApp FSLess $ toFolTerm qs <$> [s,t]
toFolAtom _ t@(Subterm _ _) = error $ "unsupported atom " ++ show t
toFolAtom _ t@(Last _) = error $ "unsupported atom " ++ show t
toFolAtom _ (Syntactic s) = error $ "unexpected syntactic sugar: " ++ show s

toFolTerm :: PVar v => PVarCtx v -> VTerm Name v -> FolTerm
toFolTerm _ (LIT (Con c)) = error $ "unexpected literal constant: " ++ show c
toFolTerm qs (LIT (Var v)) = varFromContext qs v
toFolTerm qs (FAPP f ts) = FolApp (MsgSymbol f) (toFolTerm qs <$> ts)
