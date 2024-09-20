{-# LANGUAGE TypeFamilies       #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use foldr" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

-- TODO equational theories
-- TODO import DH and so

module Main.Mode.Batch.ToSmtlib (
    toSmtlib
  , toFolProblem
  , outputNice
  , TempTranslation(..)
  ) where

import Items.OpenTheoryItem
import TheoryObject
import Text.PrettyPrint
import Prelude hiding ((<>))
import Theory.Model
import Data.Maybe
import Data.List (intercalate,genericIndex,intersperse)
import Data.Functor
import qualified Data.ByteString.Char8 as BS
import Theory
import Data.Set
import Term.SubtermRule 
import Control.Monad

data Smtlib = Smtlib
  deriving (Show)

toSmtlib :: FolSignature -> Smtlib
toSmtlib _ = Smtlib

data FolSort = FolSortMsg
             | FolSortNat
             | FolSortRat
             | FolSortTemp
             | FolSortBool
             | FolSortRule
             | FolSortLin
             | FolSortPer
             | FolSortAct
  deriving (Show,Ord,Eq)

data FolFactTag = FolFactUser Multiplicity String Int 
                | FolFactOut
                | FolFactIn
                | FolFactKnown
                | FolFactFresh
  deriving (Show,Ord,Eq)

folFactTagMultiplicity :: FolFactTag -> Multiplicity 
folFactTagMultiplicity (FolFactUser m _ _) = m
folFactTagMultiplicity FolFactOut = Linear
folFactTagMultiplicity FolFactIn = Linear
folFactTagMultiplicity FolFactKnown = Persistent
folFactTagMultiplicity FolFactFresh = Linear

folFactTagArity :: FolFactTag -> Int 
folFactTagArity (FolFactUser _ _ a) = a
folFactTagArity FolFactOut = 1
folFactTagArity FolFactIn = 1
folFactTagArity FolFactKnown = 1
folFactTagArity FolFactFresh = 1

unreachableErrMsg1 :: FactTag -> a
unreachableErrMsg1 f = error $ "unreachable. " ++ show f ++ " facts are not allowed in rule definition in input file."

toFolFactTag :: FactTag -> FolFactTag 
toFolFactTag (ProtoFact m s i) = FolFactUser m s i
toFolFactTag FreshFact  = FolFactFresh
toFolFactTag OutFact    = FolFactOut
toFolFactTag InFact     = FolFactIn
toFolFactTag f@KUFact   = unreachableErrMsg1 f
toFolFactTag f@KDFact   = unreachableErrMsg1 f
toFolFactTag f@DedFact  = unreachableErrMsg1 f
toFolFactTag f@TermFact = unreachableErrMsg1 f


type MsgFuncId = FunSym

-- folFuncTuple (MsgSymbol (NoEq (name, (arity, _priv, _constr)))) = 
--                    (unpack name, [FolSortMsg | _ <- [1..arity]], FolSortMsg)
-- folFuncTuple (MsgSymbol (AC ac)) = 
--                    (show ac, [FolSortMsg, FolSortMsg], FolSortMsg)
-- folFuncTuple (MsgSymbol (C EMap)) = error "EMap message not supported (yet)"
-- folFuncTuple (MsgSymbol List) = error "List message not supported (yet)"


msgFuncIdPrivacy :: MsgFuncId -> Privacy
msgFuncIdPrivacy (NoEq (_, (_, priv, _constr))) = priv
msgFuncIdPrivacy (AC ac) = Public
msgFuncIdPrivacy (C EMap) = Public

msgFuncIdName :: MsgFuncId -> String
msgFuncIdName (NoEq (name, (_, _, _constr))) = "u_" ++ BS.unpack name
msgFuncIdName (AC ac) = show ac
msgFuncIdName (C EMap) = "emap"


msgFuncIdArity :: MsgFuncId -> Int
msgFuncIdArity (NoEq (_, (arity, _, _constr))) = arity
msgFuncIdArity (AC _) = 2
msgFuncIdArity (C EMap) = 2

data FolFuncId = FolEq FolSort
               | FolTempLess TempTranslation
               | End TempTranslation
               | MsgSymbol MsgFuncId
               | FolFuncFact FolFactTag
               | FolFuncAct FolFactTag
               | FolNatAdd
               | FolNatSucc
               | FolNatZero
               | FolPredPre
               | FolPredCon
               | FolPredAct
               | FolFuncPre
               | FolFuncCon
               | FolFuncRule FolRule
               | FolFuncEquals
               | FolFuncFresh
               | FolFuncPub
               | FolFuncState TempTranslation
               | FolPredState TempTranslation
               | FolPredLab TempTranslation
               | FolFuncTempSucc
               | FolFuncTempZero
               | FolRatLiteral Rational
               | FolRatAdd
               | FolFuncLiteral NameId FolSort
  deriving (Show,Ord,Eq)

data FolTerm = FolApp FolFuncId [FolTerm]
             | FolVar FolVar
    deriving (Show,Eq,Ord)

data FolFormula =
    FolAtom FolTerm
  | FolBool !Bool
  | FolNot FolFormula
  | FolConn Connective FolFormula FolFormula
  | FolConnMultiline Connective [FolFormula]
  | FolQua !Quantifier FolVar FolFormula
  deriving (Show)

data FolProblem = FolProblem {
    _fpTemp    :: TempTranslation
  , _fpRules   :: [FolRule]
  , _fpFormula :: [FolGoal]
  , _fpMsgCons :: [FunSym]
  , _fpEq      :: [FolFormula]
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
sortName FolSortRat = "rat"
sortName FolSortTemp = "temp"
sortName FolSortBool = "bool"
sortName FolSortRule = "rule"
sortName FolSortLin = "lin"
sortName FolSortPer = "per"
sortName FolSortAct = "act"

data TempTranslation = TempRat | TempNat | TempAbstract
  deriving (Show,Ord,Eq)

tempSort :: TempTranslation -> FolSort
tempSort TempRat = FolSortRat
tempSort TempNat = FolSortNat
tempSort TempAbstract = FolSortTemp

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

instance ToDoc FolRule where
  toDoc (FolRule name ps as cs) =
    text ("rule " ++ name ++ ": ")
      <> fToDoc ps <+> text "--" <> fToDoc as <> text "->" <+> fToDoc cs
      where fToDoc [] = text "[]"
            fToDoc fs  = foldl1 (<>) $
                 [text "[ "]
              ++ intersperse (text ", ") (toDoc <$> fs)
              ++ [text " ]"]



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
folAssumptions (FolProblem temp rules _ msgSyms eq) =
     [ (toDoc r, translateRule r) | r <- rules ++ mdRules ]
  ++ [ (text "start condition", startCondition)
     , (text "transition relation", transitionRelation)
     , (text "addition definition", addDef)
     ]
  ++ [ (text "equation theory:", mlConj eq) ]
  where 
    mdRules :: [FolRule]
    mdRules = [
          FolRule "md0" [  factIn x ][         ][ factK x  ]
        , FolRule "md1" [  factK x  ][  actK x ][ factIn x ]
        , FolRule "md2" [           ][         ][ factK (pubVarT n) ]
        , FolRule "md3" [  factFresh (freshVarT n) ][         ][ factK (freshVarT n) ]
        ]
        ++ [ FolRule ("md4_" ++ folFuncName fun)
                     [ factK x | x <- xs ] [] [ factK (FolApp fun xs) ]
            | fun@(MsgSymbol s) <- fmap MsgSymbol msgSyms
            , msgFuncIdPrivacy s == Public
            , let arity = folFuncArity fun
            , let xs = [ FolVar ("x" ++ show i, FolSortMsg) | i <- [1 .. arity] ] ]
      where x  = FolVar ("x", FolSortMsg)
            ($$) f = FolApp (FolFuncFact f)
            n = FolVar ("n", FolSortNat)

    factIn    x = FolApp (FolFuncFact FolFactIn   ) [x]
    factOut   x = FolApp (FolFuncFact FolFactOut  ) [x]
    factK     x = FolApp (FolFuncFact FolFactKnown) [x]
    factFresh x = FolApp (FolFuncFact FolFactFresh) [x]
    actK      x = FolApp (FolFuncAct  FolFactKnown) [x]
    freshVarT x = FolApp FolFuncFresh [x]
    pubVarT x   = FolApp FolFuncPub [x]

    addDef :: FolFormula
    addDef = FolConnMultiline And [ allQ [x   ] ( addT x' zeroT      ~~ x')
                                  , allQ [x, y] ( addT x' (succT y') ~~ succT (addT x' y'))   ]
      where x = ("x", FolSortNat)
            y = ("y", FolSortNat)
            x' = FolVar x
            y' = FolVar y

    startCondition :: FolFormula
    startCondition = mlConj [ 
                         let f = ("f",FolSortLin) 
                             f' = FolVar f
                         in allQ [f] (stateT f' startTime ~~ zeroT)
                       , let f = ("f",FolSortPer) 
                             f' = FolVar f
                         in allQ [f] (FolNot $ stateP f' startTime)
                       ]

    transitionRelation :: FolFormula
    transitionRelation = allQ [t] $ mlDisj [ end, ruleTransition, freshness]
       where t = ("t", tempSort temp)
             t2 = ("t2", tempSort temp)
             r = ("r", FolSortRule)
             n = ("n", FolSortNat)
             n' = FolVar n
             r' = FolVar r
             t' = FolVar t
             t2' = FolVar t2
             end = FolAtom $ FolApp (End temp) [FolVar t]
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
               where diff = ("diff", tempSort temp)
                     diff' = FolVar diff
             freshN = factFresh (freshVarT n')

    translateRule :: FolRule -> FolFormula
    translateRule rule@(FolRule _name ls as rs) =
      allQ (ruleVars rule) $ mlConj [
         defFunAsSum preT ls
       , defPredAsDisj preP (persistent ls)
       , defPredAsDisj actP as
       , defPredAsDisj conP (persistent rs)
       , defFunAsSum conT rs
       ]
      where
        defPredAsDisj p items =
          let f = ("f", FolSortPer)
          in allQ [f] (p (ruleT rule) (FolVar f) <~> disj [ x ~~ FolVar f | x <- items ])
        defFunAsSum fun items =
          let f = ("f", FolSortLin)
          in allQ [f] (fun (ruleT rule) (FolVar f) ~~ sumT [ equalsT x (FolVar f) | x <- linear items ])
        facts mult s = [ f | f <- s
                           , factTermMultiplicity f == mult ]
        factTermMultiplicity (FolApp (FolFuncFact tag) _args)  = folFactTagMultiplicity tag
        factTermMultiplicity _ = error "unreachable"
        linear = facts Linear
        persistent = facts Persistent




    addT :: FolTerm -> FolTerm -> FolTerm
    addT l r = FolApp FolNatAdd [l, r]

    addQT :: FolTerm -> FolTerm -> FolTerm
    addQT l r = FolApp FolRatAdd [l, r]

    literalQT :: Rational -> FolTerm
    literalQT r = FolApp (FolRatLiteral r) []

    zeroT :: FolTerm
    zeroT =  FolApp FolNatZero []

    oneT :: FolTerm
    oneT = succT zeroT

    succT :: FolTerm -> FolTerm
    succT t =  FolApp FolNatSucc [t]

    stateT :: FolTerm -> FolTerm -> FolTerm
    stateT x y = FolApp (FolFuncState temp) [x, y]

    preT :: FolTerm -> FolTerm -> FolTerm
    preT x y = FolApp FolFuncPre [x, y]

    conT :: FolTerm -> FolTerm -> FolTerm
    conT x y = FolApp FolFuncCon [x, y]

    sumT :: [FolTerm] -> FolTerm
    sumT = aggregate zeroT addT

    equalsT :: FolTerm -> FolTerm -> FolTerm
    equalsT l r = FolApp FolFuncEquals [l, r]

    ruleT :: FolRule -> FolTerm
    ruleT r = FolApp (FolFuncRule r) (FolVar <$> ruleVars r)

    stateP :: FolTerm -> FolTerm -> FolFormula
    stateP x y = FolAtom $ FolApp (FolPredState temp) [x, y]

    preP :: FolTerm -> FolTerm -> FolFormula
    preP x y = FolAtom $ FolApp FolPredPre [x, y]

    conP :: FolTerm -> FolTerm -> FolFormula
    conP x y = FolAtom $ FolApp FolPredCon [x, y]

    actP :: FolTerm -> FolTerm -> FolFormula
    actP x y = FolAtom $ FolApp FolPredAct [x, y]

    labP :: FolTerm -> FolTerm -> FolFormula
    labP x y = FolAtom $ FolApp (FolPredLab temp) [x, y]

    tempSucc :: FolTerm -> FolTerm
    tempSucc t = case temp of 
                   TempAbstract -> FolApp FolFuncTempSucc [t]
                   TempNat -> succT t
                   TempRat -> addQT t (literalQT 1)

    startTime :: FolTerm
    startTime = case temp of 
                   TempAbstract -> FolApp FolFuncTempZero []
                   TempNat -> zeroT
                   TempRat -> literalQT 0

folGoals :: FolProblem -> [(Doc, FolFormula)]
folGoals (FolProblem _ _ goals _ _) = [ (text name, form) | FolGoal name form <- goals ]


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

(<~) :: FolFormula -> FolFormula  -> FolFormula
(<~) = flip (~>)

neg :: FolFormula -> FolFormula
neg = FolNot

qMany :: Quantifier -> [FolVar] -> FolFormula -> FolFormula
qMany _ [] = id
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

disj :: [FolFormula] -> FolFormula
disj = aggregate (FolBool False) (\/)

type FolVar = (String, FolSort)

ruleVars :: FolRule -> [FolVar]
ruleVars (FolRule _ ls as rs) = uniq $ (ls ++ as ++ rs) >>= varList

varList :: FolTerm -> [FolVar]
varList (FolVar v) = [v]
varList (FolApp _ as) = as >>= varList

varSet :: FolTerm -> [FolVar]
varSet = uniq . varList

data FolRule = FolRule {
      _frName   :: String
    , _frPrems  :: [FolTerm]
    , _frActs   :: [FolTerm]
    , _frConcls :: [FolTerm]
    }
    deriving (Show,Eq,Ord)


folFactTagName (FolFactUser _ name _) = "f_" ++ name
folFactTagName FolFactFresh = "Fr"
folFactTagName FolFactOut  = "Out"
folFactTagName FolFactIn = "In"
folFactTagName FolFactKnown = "K"

folFuncTuple :: FolFuncId -> (String, [FolSort], FolSort)
folFuncTuple (End temp) = ("end", [tempSort temp], FolSortBool)
folFuncTuple (MsgSymbol s) = (msgFuncIdName s, [FolSortMsg | _ <- [1..msgFuncIdArity s]], FolSortMsg)
folFuncTuple (FolFuncAct tag) = ("a_" ++ folFactTagName tag, [FolSortMsg | _ <- [1..folFactTagArity tag]], FolSortAct)
folFuncTuple (FolFuncFact tag) = (folFactTagName tag, [FolSortMsg | _ <- [1..folFactTagArity tag]], srt (folFactTagMultiplicity tag))
  where srt Persistent = FolSortPer
        srt Linear = FolSortLin
folFuncTuple (FolEq s) = ("=", [s, s], FolSortBool)
folFuncTuple (FolTempLess temp) = ("tempLess", [tempSort temp, tempSort temp], FolSortBool)
folFuncTuple FolNatSucc = ("s", [FolSortNat], FolSortNat)
folFuncTuple FolNatZero = ("0", [], FolSortNat)
folFuncTuple FolNatAdd = ("add", [FolSortNat, FolSortNat], FolSortNat)
folFuncTuple FolPredPre = ("Pre", [FolSortRule, FolSortPer], FolSortBool)
folFuncTuple FolPredCon = ("Con", [FolSortRule, FolSortPer], FolSortBool)
folFuncTuple FolPredAct = ("Act", [FolSortRule, FolSortAct], FolSortBool)
folFuncTuple FolFuncPre = ("pre", [FolSortRule, FolSortLin], FolSortNat)
folFuncTuple FolFuncCon = ("con", [FolSortRule, FolSortLin], FolSortNat)
folFuncTuple (FolFuncRule r) = (_frName r, FolSortMsg <$ ruleVars r, FolSortRule)
folFuncTuple FolFuncEquals = ("equals", [FolSortLin, FolSortLin], FolSortNat) 
folFuncTuple FolFuncFresh = ("fresh", [FolSortNat], FolSortMsg)
folFuncTuple FolFuncPub = ("pub", [FolSortNat], FolSortMsg)
folFuncTuple (FolFuncState temp) = ("state", [FolSortLin, tempSort temp], FolSortNat)
folFuncTuple (FolPredState temp) = ("State", [FolSortPer, tempSort temp], FolSortBool)
folFuncTuple (FolPredLab temp) = ("Lab", [FolSortAct, tempSort temp], FolSortBool)
folFuncTuple FolFuncTempSucc = ("t+1", [FolSortTemp], FolSortTemp)
folFuncTuple FolFuncTempZero = ("t0", [], FolSortTemp)
folFuncTuple FolRatAdd = ("+", [FolSortRat, FolSortRat], FolSortRat)
folFuncTuple (FolRatLiteral r) = (show r, [], FolSortRat)
folFuncTuple (FolFuncLiteral n srt) = ("l_" ++ getNameId n, [], srt)

folFuncName :: FolFuncId -> String
folFuncName f = let (n, _, _) = folFuncTuple f in n

folFuncSig :: FolFuncId -> ([FolSort], FolSort)
folFuncSig f = let (_, as, r) = folFuncTuple f in (as, r)

folFuncArity :: FolFuncId -> Int
folFuncArity = length . fst . folFuncSig

assertEq :: (Show a, Eq a) => a -> a -> String -> Bool
assertEq l r name | l == r    = True
                  | otherwise = error ("expected " ++ name ++ " == " ++ show l ++ ". is: " ++ show r)

assertEmpty :: Show a => [a] -> String -> Bool
assertEmpty [] _name = True
assertEmpty xs name = error ("expected " ++ name ++ " to be empty. is: " ++ show xs)


toFolRules :: TempTranslation -> [TheoryItem OpenProtoRule p s] -> [FolRule]
toFolRules temp = mapMaybe toRule
  where toRule (RuleItem (OpenProtoRule
                 (Rule (ProtoRuleEInfo
                           name
                           attr -- <- _preAttributes 
                           restriction -- <- _preRestriction =
                           )
                       prems
                       concs
                       acts
                       _newVars -- TODO: what are these used for?
                       )
                   ruleAC -- ruleAC
                   ))
         |    assertEmpty attr "attr"
           && assertEmpty ruleAC "ruleAC"
           && assertEmpty restriction "restriction"  
              = Just (FolRule name' 
                              (factT temp () <$> prems) 
                              ( actT temp () <$> acts) 
                              (factT temp () <$> concs))
           where name' = case name of
                    FreshRule -> "ruleFresh"
                    StandRule r -> "r_" ++ r
        toRule (RuleItem r) = error ("unexpected rule" ++ show r)
        toRule _ = Nothing

-- TODO assertions of _options, etc
assertEmptyS x = assertEmpty (Data.Set.toList x)

getTag :: LNFact -> FactTag
getTag (Fact tag factAnnotations _factTerms)
 | assertEmptyS factAnnotations "factAnnotations" = tag

infix 5 ~~
infixl 4 /\
infixl 3 \/
infixl 2 <~>
infixl 2 ~>
infixl 2 <~

toFolProblem :: TempTranslation -> OpenTheory -> FolProblem
toFolProblem temp th 
  = FolProblem temp 
               (toFolRules temp $ _thyItems th) 
               (mapMaybe (toFolGoal temp) $ _thyItems th)
               (Data.Set.toList $ funSyms $ _sigMaudeInfo $ _thySignature th)
               (userEq ++ builtinEqs)
     where 
       userEq = fmap (stRuleToFormula temp) 
              $ Data.Set.toList $ stRules 
              $ _sigMaudeInfo $ _thySignature th 
       builtinEqs = join [ builtinEq b | TranslationItem (SignatureBuiltin b) <- _thyItems th ]

       builtinEq str = universalClosure <$> (case str of 
                  "diffie-hellman" -> dh
                  "bilinear-pairing" -> dh ++ blp
                  _ -> error $ "unsupported builtin: " ++ str)
         where 
           dh = [
               (x ^ y) ^ z  ~~ x ^ (y * z)
             ,  x ^ one     ~~ x
             ,  x * y       ~~ y * x
             ,  (x * y) * z ~~ x * (y * z)
             ,  x * one     ~~ x
             ,  x * inv x   ~~ one
             ]
           blp = [
               pmult x (pmult y p) ~~ pmult (x*y) p
             , pmult one p           ~~ p
             , em p q              ~~ em q p
             , em (pmult x p) q    ~~ pmult x (em q p)
             ]

           x = FolVar ("x", FolSortMsg)
           y = FolVar ("y", FolSortMsg)
           z = FolVar ("z", FolSortMsg)
           p = FolVar ("p", FolSortMsg)
           q = FolVar ("q", FolSortMsg)
           (*) l r = FolApp (MsgSymbol (AC Mult)) [l,r]
           (^) l r = FolApp (MsgSymbol (NoEq expSym)) [l,r]
           inv t = FolApp (MsgSymbol (NoEq invSym)) [t]
           one = FolApp (MsgSymbol (NoEq oneSym)) []
           pmult l r = FolApp (MsgSymbol (NoEq pmultSym)) [l,r]
           em l r = FolApp (MsgSymbol (C EMap)) [l,r]



universalClosure :: FolFormula -> FolFormula
universalClosure f = allQ (Data.Set.toList $ freeVars f) f

freeVars :: FolFormula -> Set FolVar
freeVars (FolAtom t) = Data.Set.fromList $ varSet t
freeVars (FolConn _ l r) = freeVars l `union` freeVars r
freeVars (FolConnMultiline _ as) = Prelude.foldl union Data.Set.empty (fmap freeVars as)
freeVars (FolNot f) = freeVars f
freeVars (FolBool _) = Data.Set.empty
freeVars (FolQua _ v f) =  freeVars f \\ singleton v

stRuleToFormula :: TempTranslation -> CtxtStRule -> FolFormula
stRuleToFormula temp (CtxtStRule lhs (StRhs _pos rhs)) = universalClosure $ toFolTerm temp () lhs ~~ toFolTerm temp () rhs

-- TODO test file with non context rewrite rules

data FolGoal = FolGoal String FolFormula
  deriving (Show)

toFolGoal :: TempTranslation -> OpenTheoryItem -> Maybe FolGoal
toFolGoal temp (LemmaItem (Lemma name AllTraces formula _attributes _proof)) = Just (FolGoal name (toFolFormula temp [] formula))
toFolGoal _ _ = Nothing


type QuantScope = [FolVar]

toFolFormula :: TempTranslation -> QuantScope -> LNFormula -> FolFormula
toFolFormula temp qs (Ato a) = toFolAtom temp qs a
toFolFormula _ _ (TF x) = FolBool x
toFolFormula temp qs (Not x) = FolNot (toFolFormula temp qs x)
toFolFormula temp qs (Conn c l r) = FolConn c (toFolFormula temp qs l) (toFolFormula temp qs r)
toFolFormula temp qs (Qua q (v,s) f) = FolQua q (v, s') (toFolFormula temp ((v, s'):qs) f)
  where s' = toFolSort temp s

toFolSort :: TempTranslation -> LSort -> FolSort
toFolSort _ LSortPub   = error $ "unreachable"
toFolSort _ LSortFresh = error $ "unreachable"
toFolSort _ LSortMsg =  FolSortMsg
toFolSort temp LSortNode = tempSort temp
toFolSort _ srt@LSortNat =  error $ "unexpected sort: " ++ show srt

class PVar a where
  type PVarCtx a

  varFromContext :: TempTranslation -> PVarCtx a -> a -> FolTerm

instance PVar (BVar LVar) where
  type PVarCtx (BVar LVar) = QuantScope

  varFromContext _ qs (Bound deBrujinIdx) = FolVar (qs `genericIndex` deBrujinIdx)
  varFromContext temp _ (Free v) = varFromContext temp () v

instance PVar LVar where
  type PVarCtx LVar = ()

  varFromContext temp () (LVar n sort idx) 
    = case sort of 
        LSortPub   -> FolApp FolFuncPub   [FolVar (name, FolSortNat)]
        LSortFresh -> FolApp FolFuncFresh [FolVar (name, FolSortNat)]
        _          -> FolVar (name, toFolSort temp sort)
      where name = if idx  == 0 then "v_" ++ n else "v_" ++ n ++ "_" ++ show idx



factOrActT :: PVar v => (FolFactTag -> FolFuncId) -> TempTranslation -> PVarCtx v -> Fact (VTerm Name v) -> FolTerm
factOrActT toFuncId temp qs (Fact tag factAnnotations terms)
 | assertEmptyS factAnnotations "factAnnotations"
   = FolApp (toFuncId (toFolFactTag tag)) (toFolTerm temp qs <$> terms)
 | otherwise = error "unreachable"

factT :: PVar v => TempTranslation -> PVarCtx v -> Fact (VTerm Name v) -> FolTerm
factT = factOrActT FolFuncFact

actT :: PVar v => TempTranslation -> PVarCtx v -> Fact (VTerm Name v) -> FolTerm
actT = factOrActT FolFuncAct

sortOf :: FolTerm -> FolSort
sortOf (FolApp f _) = snd (folFuncSig f)
sortOf (FolVar (_, s)) = s

(~~) :: FolTerm -> FolTerm -> FolFormula
(~~) l r = FolAtom $ FolApp (FolEq (sortOf l)) [l, r]

(~/~) :: FolTerm -> FolTerm -> FolFormula
(~/~) l r = neg (l ~~ r)

toFolAtom :: (PVar v, Show v) => TempTranslation -> PVarCtx v -> ProtoAtom Unit2 (VTerm Name v) -> FolFormula
toFolAtom temp qs (Action term fact)  = FolAtom $ FolApp FolPredAct [ toFolTerm temp qs term, actT temp qs fact]
toFolAtom temp qs (EqE s t) = toFolTerm temp qs s ~~ toFolTerm temp qs t
toFolAtom temp qs (Less s t) = FolAtom $ FolApp (FolTempLess temp) $ toFolTerm temp qs <$> [s,t]
toFolAtom _ _ t@(Subterm _ _) = error $ "unsupported atom " ++ show t
toFolAtom _ _ t@(Last _) = error $ "unsupported atom " ++ show t
toFolAtom _ _ (Syntactic s) = error $ "unexpected syntactic sugar: " ++ show s

toFolTerm :: PVar v => TempTranslation -> PVarCtx v -> VTerm Name v -> FolTerm
toFolTerm temp _ (LIT (Con (Name tag id))) 
  = case tag of 
     FreshName -> FolApp FolFuncFresh [FolApp (FolFuncLiteral id FolSortNat) []]
     PubName   -> FolApp FolFuncPub   [FolApp (FolFuncLiteral id FolSortNat) []]
     NodeName  -> FolApp (FolFuncLiteral id (tempSort temp)) []
     NatName   -> FolApp (FolFuncLiteral id FolSortNat     ) []
-- toFolTerm _ _ (LIT (Con c)) = error $ "unexpected literal constant: " ++ show c
toFolTerm temp qs (LIT (Var v)) = varFromContext temp qs v
toFolTerm temp qs (FAPP f ts) = FolApp (MsgSymbol f) (toFolTerm temp qs <$> ts)
