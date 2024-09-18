{-# LANGUAGE TypeFamilies       #-}

module Main.Mode.Batch.ToSmtlib (
    toSmtlib
  , toFolSignature
  , toFolProblem
  , outputNice
  ) where

import Items.OpenTheoryItem
import TheoryObject
import Text.PrettyPrint
import Prelude hiding ((<>))
import Theory.Model
import Data.Maybe
import Data.List (intercalate,genericIndex,intersperse)
import Data.Functor
import Data.ByteString.Char8 (unpack)
import Theory
import Data.Set

data Smtlib = Smtlib
  deriving (Show)

toSmtlib :: FolSignature -> Smtlib
toSmtlib _ = Smtlib

data FolSort = FolSortMsg
             | FolSortNat
             | FolSortTemp
             | FolSortBool
             | FolSortRule
             | FolSortLin
             | FolSortPer
             | FolSortAct
  deriving (Show,Ord,Eq)

data FolFuncId = FSEq FolSort
               | FSLess
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
               | FolFuncState
               | FolPredState
               | FolPredLab
               | FolFuncTempSucc
  deriving (Show,Ord,Eq)

data FolTerm = FolApp FolFuncId [FolTerm]
             | FolVar FolVar
  deriving (Show)

data FolFormula =
    FolAtom FolTerm
  | FolBool !Bool
  | FolNot FolFormula
  | FolConn Connective FolFormula FolFormula
  | FolConnMultiline Connective [FolFormula]
  | FolQua !Quantifier FolVar FolFormula
  deriving (Show)

data FolProblem = FolProblem {
    _fpRules   :: [SupportedRule]
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
sortName FolSortNat = "nat"
sortName FolSortTemp = "temp"
sortName FolSortBool = "bool"
sortName FolSortRule = "rule"
sortName FolSortLin = "lin"
sortName FolSortPer = "per"
sortName FolSortAct = "act"

class ToDoc a where
  toDoc :: a -> Doc

instance ToDoc FolSort where
  toDoc = text . sortName

instance ToDoc FolFuncId where
  toDoc = text . folFuncName

instance ToDoc FolTerm where
  toDoc (FolVar (v, _)) = text v
  toDoc (FolApp f ts) = foldl1 (<>) $
    [ toDoc f, text "("]
    ++ intersperse (text ",") (fmap toDoc ts)
    ++ [ text ")" ]

instance ToDoc Quantifier where
  toDoc All = text "∀"
  toDoc Ex  = text "∃"

conStr :: Connective -> String
conStr And = "/\\"
conStr Or = "\\/"
conStr Imp = "->"
conStr Iff = "<->"

instance ToDoc Connective where
  toDoc = text . conStr

instance ToDoc FolFormula where
  toDoc (FolAtom t) = toDoc t
  toDoc (FolBool t) = text $ show t
  toDoc (FolNot t) = text "~" <> toDoc t
  toDoc (FolConnMultiline And []) = toDoc $ FolBool True
  toDoc (FolConnMultiline Or []) = toDoc $ FolBool False
  toDoc (FolConnMultiline c fs) = sep (zipWith (<+>) ops (toDoc <$> fs))
    where ops = text (' ' <$ conStr c) : repeat (toDoc c)

  toDoc (FolConn c s t) = text "(" <> toDoc s <+> toDoc c <+> toDoc t <> text ")"

  toDoc (FolQua q (v, s) f) = toDoc q <> text v <> text ":" <+> toDoc s <> text "(" <> toDoc f <> text ")"

instance ToDoc FolGoal where
  toDoc (FolGoal name formula) =
    text ("goal " ++ name ++ ":") <+> toDoc formula

instance ToDoc SupportedRule where
  toDoc (SupportedRule name ps as cs) =
    text ("rule" ++ name' ++ ": ")
      <> fToDoc ps <+> text "--" <> fToDoc as <> text "->" <+> fToDoc cs
      where fToDoc [] = text "[]"
            fToDoc fs  = foldl1 (<>) $
                 [text "[ "]
              ++ intersperse (text ", ") (toDoc . factT () <$> fs)
              ++ [text " ]"]
            name' = case name of Just n  -> " " ++ n ++ " "
                                 Nothing -> ""



instance ToDoc FolSignature where
  toDoc (FolSignature sorts funcs) = vcat [
      hsep (text "sorts: " : (toDoc <$> sorts))
    , text "funcs:" $$ nest 5 (vcat [
      text $ "  " ++ folFuncName f ++ ": " ++ ty (folFuncSig f) | f <- funcs
    ])
    ]
      where ty ([], r) = sortName r
            ty ([a], r) = sortName a ++ " -> " ++ sortName r
            ty (as, r) = "(" ++ intercalate ", " (sortName <$> as) ++ ") -> " ++ sortName r

instance ToDoc FolProblem where
  toDoc p = vcat $ intersperse (text "")
     [ text "signature:" $$ nest 5 (toDoc (folSignature p))
     , nestedforms "assumptions:" folAssumptions
     , nestedforms "goals:" folGoals
     ]
     where nestedforms title fs =  text title $$ nest 5
            (vcat $ intersperse (text "") [ t $$ nest 5 (toDoc f)  | (t, f) <- fs p ])


uniq :: (Ord a, Eq a) => [a] -> [a]
uniq = Data.Set.toList . Data.Set.fromList


folSignature :: FolProblem -> FolSignature
folSignature p = FolSignature (uniq $ forms >>= sorts) (uniq $ forms >>= funcs)
  where forms = (folAssumptions p ++ folGoals p) <&> snd

        sorts (FolAtom t) = sorts' t
        sorts (FolBool _) = [FolSortBool]
        sorts (FolNot f) = sorts f
        sorts (FolConn _ l r) = sorts l ++ sorts r
        sorts (FolConnMultiline _ fs) = sorts =<< fs
        sorts (FolQua _ _ f) = sorts f

        sorts' (FolVar (_, s)) = [s]
        sorts' (FolApp fid fs) = res:args ++  (sorts' =<< fs)
          where (args, res) = folFuncSig fid


        funcs (FolAtom t) = funcs' t
        funcs (FolBool _) = []
        funcs (FolNot f) = funcs f
        funcs (FolConn _ l r) = funcs l ++ funcs r
        funcs (FolConnMultiline _ fs) = funcs =<< fs
        funcs (FolQua _ _ f) = funcs f

        funcs' (FolVar _) = []
        funcs' (FolApp fid fs) = fid : (funcs' =<< fs)

folAssumptions :: FolProblem -> [(Doc, FolFormula)]
folAssumptions (FolProblem rules _) =
     [ (toDoc r, translateRule r) | r <- rules ]
  ++ [ (text "transition relation", transitionRelation)
     , (text "add def", addDef)
     -- , (text "add def", tempSuccDef)
     ]

addT :: FolTerm -> FolTerm -> FolTerm
addT l r = FolApp FolNatAdd [l, r]

zeroT :: FolTerm
zeroT =  FolApp FolNatZero []

oneT :: FolTerm
oneT = succT zeroT

succT :: FolTerm -> FolTerm
succT t =  FolApp FolNatSucc [t]

stateT :: FolTerm -> FolTerm -> FolTerm
stateT x y = FolApp FolFuncState [x, y]

preT :: FolTerm -> FolTerm -> FolTerm
preT x y = FolApp FolFuncPre [x, y]

conT :: FolTerm -> FolTerm -> FolTerm
conT x y = FolApp FolFuncCon [x, y]

sumT :: [FolTerm] -> FolTerm
sumT = aggregate zeroT addT

equalsT :: FolTerm -> FolTerm -> FolTerm
equalsT l r = FolApp FolFuncEquals [l, r]

ruleT :: SupportedRule -> FolTerm
ruleT r = FolApp (FolRule r) (FolVar <$> ruleVars r)

stateP :: FolTerm -> FolTerm -> FolFormula
stateP x y = FolAtom $ FolApp FolPredState [x, y]

preP :: FolTerm -> FolTerm -> FolFormula
preP x y = FolAtom $ FolApp FolPredPre [x, y]

conP :: FolTerm -> FolTerm -> FolFormula
conP x y = FolAtom $ FolApp FolPredCon [x, y]

actP :: FolTerm -> FolTerm -> FolFormula
actP x y = FolAtom $ FolApp FolPredAct [x, y]

labP :: FolTerm -> FolTerm -> FolFormula
labP x y = FolAtom $ FolApp FolPredLab [x, y]


addDef :: FolFormula
addDef = FolConnMultiline And [ allQ [x   ] ( addT x' zeroT      ~~ x')
                              , allQ [x, y] ( addT x' (succT y') ~~ succT (addT x' y'))   ]
  where x = ("x", FolSortNat)
        y = ("y", FolSortNat)
        x' = FolVar x
        y' = FolVar y

folGoals :: FolProblem -> [(Doc, FolFormula)]
folGoals (FolProblem _ goals) = [ (text name, form) | FolGoal name form <- goals ]


outputNice :: ToDoc a => a -> IO ()
outputNice = putStr . render . toDoc


(/\) :: FolFormula -> FolFormula  -> FolFormula
(/\) = FolConn And

(\/) :: FolFormula -> FolFormula  -> FolFormula
(\/) = FolConn Or

(<~>) :: FolFormula -> FolFormula  -> FolFormula
(<~>) = FolConn Iff

(~>) :: FolFormula -> FolFormula  -> FolFormula
(~>) = FolConn Imp

neg :: FolFormula -> FolFormula
neg = FolNot

qMany :: Quantifier -> [FolVar] -> FolFormula -> FolFormula
qMany q [] = id
qMany q (v:vs) = FolQua q v . qMany q vs

exQ :: [FolVar] -> FolFormula -> FolFormula
exQ = qMany Ex

allQ :: [FolVar] -> FolFormula -> FolFormula
allQ = qMany All

aggregate :: a -> (a -> a -> a) -> [a] -> a
aggregate start _ []  = start
aggregate _ _ [x] = x
aggregate s op (x:xs) = op x (aggregate s op xs)

mlConj :: [FolFormula] -> FolFormula
mlConj = FolConnMultiline And

mlDisj :: [FolFormula] -> FolFormula
mlDisj = FolConnMultiline Or

conj :: [FolFormula] -> FolFormula
conj = aggregate (FolBool True) (/\)

disj :: [FolFormula] -> FolFormula
disj = aggregate (FolBool False) (\/)

type FolVar = (String, FolSort)

ruleVars :: SupportedRule -> [FolVar]
ruleVars (SupportedRule _ ls as rs) = uniq
                                    $ (ls ++ as ++ rs) >>= vars . factT ()

vars :: FolTerm -> [FolVar]
vars (FolVar v) = [v]
vars (FolApp _ as) = as >>= vars

translateRule :: SupportedRule -> FolFormula
translateRule rule@(SupportedRule _name ls as rs) =
  allQ (ruleVars rule) $ mlConj [
     defFunAsSum preT ls
   , defFunAsSum conT rs
   , defPredAsDisj preP (persistent ls)
   , defPredAsDisj conP (persistent rs)
   , defPredAsDisj actP (factT () <$> as)
   ]
  where
    defPredAsDisj p items =
      let f = ("f", FolSortPer)
      in allQ [f] (p (ruleT rule) (FolVar f) <~> disj [ x ~~ FolVar f | x <- items ])
    defFunAsSum fun items =
      let f = ("f", FolSortLin)
      in allQ [f] (fun (ruleT rule) (FolVar f) ~~ sumT [ equalsT x (FolVar f) | x <- linear items ])
    facts mult s = [ factT () f | f <- s
                                , factMultiplicity f == mult ]
    linear = facts Linear
    persistent = facts Persistent

-- TODO remove ?
tempSucc :: FolTerm -> FolTerm
tempSucc t = FolApp FolFuncTempSucc [t]

transitionRelation :: FolFormula
transitionRelation = allQ [t] $ mlDisj [ end, ruleTransition, freshness]
   where t = ("t", FolSortTemp)
         t2 = ("t2", FolSortTemp)
         r = ("r", FolSortRule)
         n = ("n", FolSortNat)
         n' = FolVar n
         r' = FolVar r
         t' = FolVar t
         t2' = FolVar t2
         end = FolAtom $ FolApp End [FolVar t]
         ruleTransition = exQ [r] $ mlConj [
             let f = ("f", FolSortLin)
                 f' = FolVar f
             in allQ [f] (exQ [n] ((stateT f' t'           ~~ addT n' (preT r' f') )
                          /\ (stateT f' (tempSucc t') ~~ addT n' (conT r' f') )))
           , let f = ("f", FolSortPer)
                 f' = FolVar f
             in allQ [f] (( preP r' f' ~> stateP f' t' )
                     /\ ( stateP f' (tempSucc t') <~> ( stateP f' t' \/ conP r' f') ))
           , let f = ("f", FolSortAct)
                 f' = FolVar f
             in allQ [f] ( labP f' t' <~> actP r' f')
           ]
         freshness = exQ [n] $ mlConj [
             allQ [t2] (leqT t2' t' ~> (stateT t2' freshN ~~ zeroT))
           , stateT (tempSucc t') freshN ~~ oneT
           , let f = ("f", FolSortPer)
                 f' = FolVar f
             in allQ [f] (stateP (tempSucc t') f' <~> stateP t' f')
           , let f = ("f", FolSortLin)
                 f' = FolVar f
             in allQ [f] (( f' ~/~ freshN ) ~> (stateT (tempSucc t') f' ~~ stateT t' f'))
           , let f = ("f", FolSortAct)
                 f' = FolVar f
             in allQ [f] (neg (labP (tempSucc t') f'))
           ]
         leqT x y = exQ [diff] (addT x diff' ~~ y)
           where diff = ("diff", FolSortTemp)
                 diff' = FolVar diff
         freshN = FolApp (FactSymbol FreshFact) [FolApp FolFuncFresh [n']]


data SupportedRule = SupportedRule {
      _srName :: Maybe String
    , _srPrems :: [LNFact]
    , _srActs :: [LNFact]
    , _srConcls :: [LNFact]
    }
    deriving (Show,Eq,Ord)

folFuncSig :: FolFuncId -> ([FolSort], FolSort)
folFuncSig End = ([FolSortTemp], FolSortBool)
folFuncSig (MsgSymbol (NoEq (_name, (arity, _priv, _constr)))) = ([FolSortMsg | _ <- [1..arity]], FolSortMsg)
folFuncSig (MsgSymbol (AC _ac)) = ([FolSortMsg, FolSortMsg], FolSortMsg)
folFuncSig (MsgSymbol (C EMap)) = error "EMap message not supported (yet)"
folFuncSig (MsgSymbol List) = error "List message not supported (yet)"
folFuncSig (FactSymbol tag) = ([FolSortMsg | _ <- [1..factTagArity tag]], srt (factTagMultiplicity tag))
  where srt Persistent = FolSortPer
        srt Linear = FolSortLin
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
folFuncSig FolFuncState = ([FolSortLin, FolSortTemp], FolSortNat)
folFuncSig FolPredState = ([FolSortPer, FolSortTemp], FolSortBool)
folFuncSig FolPredLab = ([FolSortAct, FolSortTemp], FolSortBool)
folFuncSig FolFuncTempSucc = ([FolSortTemp], FolSortTemp)

folFuncName :: FolFuncId -> String
folFuncName FolNatSucc = "s"
folFuncName FolNatZero = "zero"
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
folFuncName FolFuncState = "state"
folFuncName FolPredState = "State"
folFuncName FolPredLab = "Lab"
folFuncName FolFuncTempSucc = "tempSucc" -- TODO remove (?)

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
  , _fsigFuncs = [ End, FSLess ]
              ++ fmap FSEq sorts
              ++ fmap MsgSymbol (Data.Set.toList $ funSyms $ _sigMaudeInfo signature)

              ++ fmap FactSymbol (toList $ Data.Set.fromList (tags ++ [ FreshFact, OutFact, InFact, KUFact, KDFact, DedFact ]))
  }
 where tags = toFolRules items
          >>= (\(SupportedRule _name l p r) -> l ++ p ++ r)
          <&> getTag
       sorts = [ FolSortMsg, FolSortPer, FolSortLin, FolSortNat, FolSortTemp, FolSortBool]


toFolProblem :: OpenTheory -> FolProblem
toFolProblem th = FolProblem (toFolRules $ _thyItems th) (mapMaybe toFolGoal $ _thyItems th)

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
  varFromContext () (LVar name LSortPub _idx) = FolApp FolFuncPub [FolVar (name, FolSortNat)]
  varFromContext () (LVar name LSortFresh _idx) = FolApp FolFuncFresh [FolVar (name, FolSortNat)]
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

(~/~) :: FolTerm -> FolTerm -> FolFormula
(~/~) l r = neg (l ~~ r)

-- TODO add def

toFolAtom :: (PVar v, Show v) => PVarCtx v -> ProtoAtom Unit2 (VTerm Name v) -> FolFormula
toFolAtom qs (Action term fact)  = FolAtom $ FolApp FolPredAct [ toFolTerm qs term, factT qs fact]
toFolAtom qs (EqE s t) = toFolTerm qs s ~~ toFolTerm qs t
toFolAtom qs (Less s t) = FolAtom $ FolApp FSLess $ toFolTerm qs <$> [s,t]
toFolAtom _ t@(Subterm _ _) = error $ "unsupported atom " ++ show t
toFolAtom _ t@(Last _) = error $ "unsupported atom " ++ show t
toFolAtom _ (Syntactic s) = error $ "unexpected syntactic sugar: " ++ show s

toFolTerm :: PVar v => PVarCtx v -> VTerm Name v -> FolTerm
toFolTerm _ (LIT (Con c)) = error $ "unexpected literal constant: " ++ show c
toFolTerm qs (LIT (Var v)) = varFromContext qs v
toFolTerm qs (FAPP f ts) = FolApp (MsgSymbol f) (toFolTerm qs <$> ts)
