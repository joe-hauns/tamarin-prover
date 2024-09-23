{-# LANGUAGE TypeFamilies       #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use foldr" #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Main.Mode.Batch.ToSmtlib (
    toSmtlib
  , toFolProblem
  , outputNice
  , outputSmt
  , TempTranslation(..)
  , ToSmt(..)
  ) where

import Items.OpenTheoryItem
import TheoryObject
-- import Text.PrettyPrint
import Prettyprinter
import Prelude hiding ((<>))
import Theory.Model
import Control.Exception
import Data.Maybe
import Term.Builtin.Signature
import Data.List (intercalate,genericIndex,intersperse)
import Data.Functor
import qualified Data.ByteString.Char8 as BS
import Theory
import Data.Set hiding (filter)
import Term.SubtermRule
import Control.Monad

data FolIdent = FolIdentUserMsg String
              | FolIdentUserFact String
              | FolIdentUserAction String
              | FolIdentUserLiteral String
              | FolIdentUserRule String
              | FolIdentUserVar String
              | FolIdentAC String
              | FolIdentEmap
              | FolIdentBuiltin String 
              | FolIdentBuiltinRuleFresh
              | FolIdentBuiltinRuleMd Int 
              | FolIdentBuiltinRuleMdPubMessage FolIdent
              | FolIdentEq
              | FolIdentBool
              | FolIdentSort String 
    deriving (Show,Eq,Ord)
-- type FolIdent = String

identToStr :: FolIdent -> String
-- user defined symbols start with $
identToStr (FolIdentUserMsg s) = "$" ++ s
identToStr (FolIdentUserFact s) = "$" ++ s ++ "$f"
identToStr (FolIdentUserAction s) = "$" ++ s ++ "$a"
identToStr (FolIdentUserLiteral s) = "$" ++ s ++ "$l"
identToStr (FolIdentUserRule s) = "$" ++ s ++ "$r"
identToStr (FolIdentUserVar s) = "$" ++ s
-- translation builtins start with @
identToStr (FolIdentBuiltin s) = "@" ++ s
identToStr (FolIdentSort s)  = "@" ++ s
identToStr (FolIdentAC s) = "@" ++ s ++ "@ac"
identToStr FolIdentEmap = "@emap"
identToStr FolIdentBuiltinRuleFresh = "@fresh@r"
identToStr (FolIdentBuiltinRuleMd i) = "@md@" ++ show i
identToStr (FolIdentBuiltinRuleMdPubMessage id) = "@md" ++ identToStr id
-- smtlib builtins
identToStr FolIdentEq = "="
identToStr FolIdentBool = "Bool"

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
toFolFactTag KUFact     = FolFactKnown
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

msgFuncIdName :: MsgFuncId -> FolIdent
msgFuncIdName (NoEq (name, (_, _, _constr))) = FolIdentUserMsg $ BS.unpack name
msgFuncIdName (AC ac) = FolIdentAC $ show ac
msgFuncIdName (C EMap) = FolIdentEmap

msgFuncIdArity :: MsgFuncId -> Int
msgFuncIdArity (NoEq (_, (arity, _, _constr))) = arity
msgFuncIdArity (AC _) = 2
msgFuncIdArity (C EMap) = 2

data FolFuncId = FolEq FolSort
               | FolTempLess
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
               | FolFuncVarFresh
               | FolFuncVarPub
               | FolFuncVarNat
               | FolFuncState TempTranslation
               | FolPredState TempTranslation
               | FolPredLab TempTranslation
               | FolFuncTempSucc
               | FolFuncTempZero
               | FolFuncStringLiteral NameId FolSort
  deriving (Show,Ord,Eq)

data FolTerm = FolApp FolFuncId [FolTerm]
             | FolVar FolVar
    deriving (Show,Eq,Ord)


folApp :: FolFuncId -> [FolTerm] -> FolTerm
folApp f as | argSorts == expArgSorts = FolApp f as
            | otherwise = error $ "trying to apply " ++ show (toDoc f) ++ ": " ++ show expArgSorts
             ++ " to args " ++ intercalate "," (show . toDoc <$> as) ++ " (sorts: " ++ show argSorts ++ ")"
  where expArgSorts = fst . folFuncSig $ f
        argSorts    = sortOf <$> as

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
  , _fpRestr   :: [FolRestriction]
  , _fpGoal    :: FolGoal
  , _fpMsgCons :: [FunSym]
  , _fpEq      :: [FolFormula]
  }
  deriving (Show)

data FolRestriction = FolRestriction String FolFormula
  deriving (Show)

data FolSignature = FolSignature {
    _fsigSorts :: [ FolSort ]
  , _fsigFuncs :: [ FolFuncId ]
  }
  deriving (Show)

sortName :: FolSort -> FolIdent
sortName FolSortMsg = FolIdentSort "msg"
sortName FolSortNat = FolIdentSort "nat"
sortName FolSortTemp = FolIdentSort "temp"
sortName FolSortBool = FolIdentBool
sortName FolSortRule = FolIdentSort "rule"
sortName FolSortLin = FolIdentSort "lin"
sortName FolSortPer = FolIdentSort "per"
sortName FolSortAct = FolIdentSort "act"

sortDescription :: FolSort -> Doc ann
sortDescription FolSortMsg = pretty "messages"
sortDescription FolSortNat = pretty "natural numbers"
sortDescription FolSortTemp = pretty "abstract time point datatype (debugging purpose of the translation only)"
sortDescription FolSortBool = pretty "built-in bool sort"
sortDescription FolSortRule = pretty "rule sort"
sortDescription FolSortLin = pretty "linear facts"
sortDescription FolSortPer = pretty "persisten facts"
sortDescription FolSortAct = pretty "actions (facts used as labels for rewrites)"

data TempTranslation = TempNat | TempAbstract
  deriving (Show,Ord,Eq)

tempSort :: TempTranslation -> FolSort
tempSort TempNat = FolSortNat
tempSort TempAbstract = FolSortTemp

class ToSmt a where
  toSmt :: a -> Doc b

instance ToSmt FolSort where
  toSmt = pretty . identToStr . sortName

instance ToSmt FolFuncId where
  toSmt = pretty . identToStr . folFuncName

instance ToSmt FolTerm where
  toSmt (FolVar (v, _)) = pretty $ identToStr $ FolIdentUserVar v 
  toSmt (FolApp f ts) = parens $ toSmt f <+> align (hsep $ fmap toSmt ts)

instance ToSmt Quantifier where
  toSmt All = pretty "forall"
  toSmt Ex  = pretty "exists"

instance ToSmt Connective where
  toSmt And = pretty "and"
  toSmt Or  = pretty "or"
  toSmt Imp = pretty "=>"
  toSmt Iff = pretty "="

instance ToSmt Bool where
  toSmt True  = pretty "true"
  toSmt False = pretty "false"

collectQPrefix q f
  = case f of
     (FolQua q' v f') | q' == q ->
        let (vs, f'') = collectQPrefix q f'
        in (v:vs, f'')
     _ -> ([], f)

instance ToSmt FolFormula where
  toSmt (FolAtom t) = toSmt t
  toSmt (FolBool t) = toSmt t
  toSmt (FolNot t) = parens $ pretty "not" <+> toSmt t
  toSmt (FolConnMultiline And []) = toSmt $ FolBool True
  toSmt (FolConnMultiline Or []) = toSmt $ FolBool False
  toSmt (FolConnMultiline c fs) = parens $ toSmt c <+> align (sep $ toSmt <$> fs)

  toSmt (FolConn c s t) = parens $ hsep [toSmt c, toSmt s, toSmt t]

  toSmt f@(FolQua q _ _) = parens $ hsep [toSmt q, qvars, toSmt f']
    where (vs, f') = collectQPrefix q f
          qvars = parens $ align $ vsep [ parens $ hsep [toSmt' v, toSmt s] | (v, s) <- vs ]
          toSmt' = pretty . identToStr . FolIdentUserVar

instance ToSmt FolRule where
  toSmt (FolRule name ps as cs) =
    pretty ("rule " ++ identToStr name ++ ":")
      -- <> fToSmt ps <+> pretty "--" <> fToSmt as <> pretty "->" <+> fToSmt cs
      -- where fToSmt [] = pretty "[]"
      --       fToSmt fs  = sep $
      --            [pretty "[ "]
      --         ++ intersperse (pretty ", ") (toSmt <$> fs)
      --         ++ [pretty " ]"]


isBuiltinSmtSort :: FolSort -> Bool
isBuiltinSmtSort FolSortBool = True
isBuiltinSmtSort _ = False

isBuiltinSmtFun :: FolFuncId -> Bool
isBuiltinSmtFun (FolEq _)         = True
isBuiltinSmtFun _                 = False

isConstructor :: FolFuncId -> Bool
--
isConstructor FolFuncTempSucc = True
isConstructor FolFuncTempZero = True
isConstructor (MsgSymbol _)   = True
isConstructor (FolFuncFact _) = True
isConstructor (FolFuncAct _)  = True
isConstructor FolNatSucc      = True
isConstructor FolNatZero      = True
isConstructor (FolFuncRule _) = True
isConstructor FolFuncVarFresh = True
isConstructor FolFuncVarPub   = True
isConstructor FolFuncVarNat   = True
--
isConstructor (FolEq _)                  = False
isConstructor FolTempLess                = False
isConstructor (End _)                    = False
isConstructor (FolFuncState _)           = False
isConstructor (FolPredState _)           = False
isConstructor (FolFuncStringLiteral _ _) = False
isConstructor FolNatAdd                  = False
isConstructor FolPredPre                 = False
isConstructor FolPredCon                 = False
isConstructor FolPredAct                 = False
isConstructor FolFuncPre                 = False
isConstructor FolFuncCon                 = False
isConstructor FolFuncEquals              = False
isConstructor (FolPredLab _)             = False

folFuncDom = snd . folFuncSig
parH = parens . hsep
smtItem s as = parens $ hsep (pretty s : as)
instance ToSmt FolSignature where
  toSmt (FolSignature sorts funcs) = vcat $ intersperse emptyDoc [
      vcat [ smtItem "declare-sort" [ toSmt s, pretty "0" ] 
             <+> pretty ";-" <+> sortDescription s  | s <- sorts, not (isBuiltinSmtSort s) ]
    , vcat [ smtItem "declare-const" [ toSmt f, toSmt a ]
                   | f <- funcs
                   , let (as, a) = folFuncSig f
                   , as == []
                   , not (isBuiltinSmtFun f)]
    , vcat [ smtItem "declare-fun" [ toSmt f, parens $ hsep $ fmap toSmt as, toSmt a ]
                   | f <- funcs
                   , let (as, a) = folFuncSig f
                   , as /= []
                   , not (isBuiltinSmtFun f)]
    , vcat [ parens $ pretty "declare-datatypes" <+> align (vsep 
                [ parens $ align $ sep [ parH [toSmt s, pretty "0"] | s <- iSorts ]
                , parens $ align $ vsep $ intersperse emptyDoc [ sortConstructors s i | (s, i) <- zip iSorts [0..] ]
                ]) ]
    ]
     where isInductive s = [] /= [ f | f <- funcs
                                     , isConstructor f
                                     , folFuncDom f == s
                                     ]
           iSorts = filter isInductive sorts
           sortConstructors s i = align $ vsep $
                [ pretty ";-" <+>  toSmt s <> pretty ":" <+> sortDescription s ] 
             ++ [ ctorEntry f i j | (f, j) <- zip ctors [0..]]
               where ctors = filter isConstructor $ filter (\f -> folFuncDom f == s) funcs
           ctorEntry f i j  = parH $ [ toSmt f ] ++ [ parH [dtor i j k, toSmt a]  | (a,k) <- zip as [0..] ]
             where (as, _) = folFuncSig f
                   -- dtor i j  = toSmt f <> pretty "_" <> pretty (i::Int)
                   dtor i j k = pretty "dtor_" <> pretty (i::Int) 
                                 <> pretty "_" <> pretty (j::Int)
                                 <> pretty "_" <> pretty (k::Int)



  --     hsep (pretty "sorts: " : (toSmt <$> sorts))
  --   , vcat [ pretty "funcs:"
  --          , nest 5 (vcat [ pretty $ "  " ++ folFuncName f ++ ": " ++ ty (folFuncSig f) | f <- funcs
  --          ])
  --     ]
  --   
  --     where ty ([], r) = sortName r
  --           ty ([a], r) = sortName a ++ " -> " ++ sortName r
  --           ty (as, r) = "(" ++ intercalate ", " (sortName <$> as) ++ ") -> " ++ sortName r

instance ToSmt FolProblem where
  toSmt p = vcat $ intersperse emptyDoc
     [ toSmt (folSignature p)
     , vcat $ intersperse emptyDoc (assm <$> folAssumptions p)
     , vsep [ titleComment "goal" gName
            , smtItem "assert" [ goalToF tq goal]
            ]
     , vsep [ tqComment tq 
            , smtItem "check-sat" []
            ]
     ]
     where (gName, goal, tq) = folGoal p
           titleComment tit name = pretty ";-" <+> pretty tit <> pretty ":" <+> name
           assm (t, f) = vcat [ titleComment "assumption" t
                              , smtItem "assert" [toSmt f] ]
           goalToF AllTraces f = smtItem "not" [ toSmt f ]
           goalToF ExistsTrace f = toSmt f
           tqComment AllTraces = pretty ";- all-traces problem. unsat means the all-traces lemma holds. sat means it does not hold."
           tqComment ExistsTrace = pretty ";- exists-trace problem. sat means the exists-trace lemma holds. unsat means it does not hold."


class ToDoc a where
  toDoc :: a -> Doc b

instance ToDoc FolSort where
  toDoc = pretty . identToStr . sortName

instance ToDoc FolFuncId where
  toDoc = pretty . identToStr . folFuncName

instance ToDoc FolTerm where
  toDoc (FolVar (v, _)) = pretty v
  toDoc (FolApp f []) = toDoc f
  toDoc (FolApp f ts) = foldl1 (<>) $
    [ toDoc f, pretty "("]
    ++ intersperse (pretty ",") (fmap toDoc ts)
    ++ [ pretty ")" ]

instance ToDoc Quantifier where
  toDoc All = pretty "∀"
  toDoc Ex  = pretty "∃"

instance ToDoc Connective where
  toDoc = pretty . conStr

instance ToDoc FolFormula where
  toDoc (FolAtom t) = toDoc t
  toDoc (FolBool t) = pretty $ show t
  toDoc (FolNot t) = pretty "~" <> toDoc t
  toDoc (FolConnMultiline And []) = toDoc $ FolBool True
  toDoc (FolConnMultiline Or []) = toDoc $ FolBool False
  toDoc (FolConnMultiline c fs) = sep (zipWith (<+>) ops (toDoc <$> fs))
    where ops = pretty (' ' <$ conStr c) : repeat (toDoc c)

  toDoc (FolConn c s t) = pretty "(" <> toDoc s <+> toDoc c <+> toDoc t <> pretty ")"

  toDoc (FolQua q (v, s) f) = toDoc q <> pretty v <> pretty ":" <+> toDoc s <> pretty "(" <> toDoc f <> pretty ")"

instance ToDoc FolGoal where
  toDoc (FolGoal name formula tq) =
    pretty ("goal (" ++ show tq ++ ")" ++ name ++ ":") <+> toDoc formula

instance ToDoc FolRule where
  toDoc (FolRule name _ _ _) =
    pretty ("rule " ++ identToStr name)
      -- <> fToDoc ps <+> pretty "--" <> fToDoc as <> pretty "->" <+> fToDoc cs
      -- where fToDoc [] = pretty "[]"
      --       fToDoc fs  = foldl1 (<>) $
      --            [pretty "[ "]
      --         ++ intersperse (pretty ", ") (toDoc <$> fs)
      --         ++ [pretty " ]"]



instance ToDoc FolSignature where
  toDoc (FolSignature sorts funcs) = vcat [
      hsep (pretty "sorts: " : (toDoc <$> sorts))
    , vcat [ pretty "funcs:",  nest 5 (vcat [
      pretty $ "  " ++ identToStr (folFuncName f) ++ ": " ++ ty (folFuncSig f) | f <- funcs
    ])]
    ]
      where ty ([], r) = sname r
            ty ([a], r) = sname a ++ " -> " ++ sname r
            ty (as, r) = "(" ++ intercalate ", " (sname <$> as) ++ ") -> " ++ sname r
            sname = identToStr . sortName

instance ToDoc FolProblem where
  toDoc p = vcat $ intersperse (pretty "") 
     [ vcat [ pretty "signature:", nest 5 (toDoc (folSignature p)) ]
     , nestedforms "assumptions:" folAssumptions
     , toDoc (_fpGoal p)
     ]
     where nestedforms title fs =  vcat [
               pretty title
             , nest 5 (vcat $ intersperse (pretty "") [ vcat [ t, nest 5 (toDoc f) ]  | (t, f) <- fs p ]) ]


uniq :: (Ord a, Eq a) => [a] -> [a]
uniq = Data.Set.toList . Data.Set.fromList

conStr :: Connective -> String
conStr And = "/\\"
conStr Or = "\\/"
conStr Imp = "->"
conStr Iff = "<->"

folSignature :: FolProblem -> FolSignature
folSignature p = FolSignature (uniq $ forms >>= sorts) (uniq $ forms >>= funcs)
  where forms = (snd <$> folAssumptions p) ++ [(\(_,x,_) -> x) $ folGoal p]

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

folAssumptions :: FolProblem -> [(Doc ann, FolFormula)]
folAssumptions (FolProblem temp rules rs _ msgSyms eq) =
     [ (toDoc r, translateRule r) | r <- rules ++ mdRules ]
  ++ [ (pretty "start condition", startCondition)
     , (pretty "transition relation", transitionRelation)
     , (pretty "addition definition", addDef)
     ]
  ++ [ (pretty "equation theory:", mlConj eq) ]
  ++ [ (pretty $ "restriction " ++ r, f) | (FolRestriction r f) <- rs ]
  where
    mdRules :: [FolRule]
    mdRules = [
          FolRule (FolIdentBuiltinRuleMd 0) [  factOut x ] [         ] [ factK x  ]
        , FolRule (FolIdentBuiltinRuleMd 1) [  factK x   ] [  actK x ] [ factIn x ]
        , FolRule (FolIdentBuiltinRuleMd 2) [            ] [         ] [ factK (pubVarT fr) ]
        , FolRule (FolIdentBuiltinRuleMd 3) [  factFresh (freshVarT fr) ] [         ] [ factK (freshVarT fr) ]
        ]
        ++ [ FolRule (FolIdentBuiltinRuleMdPubMessage (folFuncName fun))
                     [ factK x | x <- xs ] [] [ factK (folApp fun xs) ]
            | fun@(MsgSymbol s) <- fmap MsgSymbol msgSyms
            , msgFuncIdPrivacy s == Public
            , let arity = folFuncArity fun
            , let xs = [ FolVar ("x" ++ show i, FolSortMsg) | i <- [1 .. arity] ] ]
      where x  = FolVar ("x", FolSortMsg)
            fr = FolVar ("fr", FolSortNat)

    factIn    x = folApp (FolFuncFact FolFactIn   ) [x]
    factOut   x = folApp (FolFuncFact FolFactOut  ) [x]
    factK     x = folApp (FolFuncFact FolFactKnown) [x]
    factFresh x = folApp (FolFuncFact FolFactFresh) [x]
    actK      x = folApp (FolFuncAct  FolFactKnown) [x]
    freshVarT x = folApp FolFuncVarFresh [x]
    pubVarT x   = folApp FolFuncVarPub [x]

    addDef :: FolFormula
    addDef = FolConnMultiline And [ allQ [x   ] ( addT x zeroT      ~~ x)
                                  , allQ [x, y] ( addT x (succT y) ~~ succT (addT x y))   ]
      where x = FolVar ("x", FolSortNat)
            y = FolVar ("y", FolSortNat)

    startCondition :: FolFormula
    startCondition = mlConj [
                         allQ [fl] (stateT fl startTime ~~ zeroT)
                       , allQ [fp] (FolNot $ stateP fp startTime)
                       ]
                       where fl  = FolVar ("f",FolSortLin)
                             fp  = FolVar ("f",FolSortPer)

    x_l = FolVar ("l", FolSortLin)
    x_p = FolVar ("p", FolSortPer)
    x_a = FolVar ("a", FolSortAct)

    transitionRelation :: FolFormula
    transitionRelation = allQ [t] $ mlDisj [ end t, ruleTransition, freshness]
       where t = FolVar ("t", tempSort temp)
             t2 = FolVar ("t2", tempSort temp)
             r = FolVar ("r", FolSortRule)
             n = FolVar ("n", FolSortNat)
             end x = FolAtom $ folApp (End temp) [x]
             ruleTransition = exQ [r] $ mlConj [
                 allQ [x_l] (exQ [n] ((stateT x_l t    ~~ addT n (preT r x_l) )
                                   /\ (stateT x_l (tempSucc t) ~~ addT n (conT r x_l) )))
               , allQ [x_p] (( preP r x_p ~> stateP x_p t )
                         /\ ( stateP x_p (tempSucc t) <~> ( stateP x_p t \/ conP r x_p) ))
               , allQ [x_a] ( labP x_a t <~> actP r x_a)
               ]
             freshness = exQ [n] $ mlConj [
                 allQ [t2] (leqT t2 t ~> (stateT freshN t2 ~~ zeroT))
               , stateT freshN (tempSucc t) ~~ oneT
               , allQ [x_p] (stateP x_p (tempSucc t) <~> stateP x_p t)
               , allQ [x_l] (( x_l ~/~ freshN ) ~> (stateT x_l (tempSucc t) ~~ stateT x_l t))
               , allQ [x_a] (neg (labP x_a (tempSucc t)))
               ]
             leqT x y = exQ [diff] (addT x diff ~~ y)
               where diff = FolVar ("diff", tempSort temp)
             freshN = factFresh (freshVarT n)

    translateRule :: FolRule -> FolFormula
    translateRule rule@(FolRule _name ls as rs) =
      allQ (FolVar <$> ruleVars rule) $ mlConj [
         defFunAsSumOfLinearFacts preT ls
       , defPredAsDisj preP (persistent ls) FolSortPer
       , defPredAsDisj actP as              FolSortAct
       , defPredAsDisj conP (persistent rs) FolSortPer
       , defFunAsSumOfLinearFacts conT rs
       ]
      where
        defPredAsDisj p items srt =
          allQ [f] (p (ruleT rule) f <~> disj [ x ~~ f | x <- items ])
            where f = FolVar ("x_v", srt)
        defFunAsSumOfLinearFacts fun items =
          allQ [f] (fun (ruleT rule) f ~~ sumT [ equalsT x f | x <- linear items ])
            where f = FolVar ("f_v", FolSortLin)
        facts mult s = [ f | f <- s
                           , factTermMultiplicity f == mult ]
        factTermMultiplicity (FolApp (FolFuncFact tag) _args)  = folFactTagMultiplicity tag
        factTermMultiplicity _ = error "unreachable"
        linear = facts Linear
        persistent = facts Persistent




    addT :: FolTerm -> FolTerm -> FolTerm
    addT = fun2 FolNatAdd

    zeroT :: FolTerm
    zeroT =  folApp FolNatZero []

    oneT :: FolTerm
    oneT = succT zeroT

    succT :: FolTerm -> FolTerm
    succT t =  folApp FolNatSucc [t]

    stateT :: FolTerm -> FolTerm -> FolTerm
    stateT x y = folApp (FolFuncState temp) [x, y]

    preT :: FolTerm -> FolTerm -> FolTerm
    preT x y = folApp FolFuncPre [x, y]

    conT :: FolTerm -> FolTerm -> FolTerm
    conT x y = folApp FolFuncCon [x, y]

    sumT :: [FolTerm] -> FolTerm
    sumT = aggregate zeroT addT

    equalsT :: FolTerm -> FolTerm -> FolTerm
    equalsT l r = folApp FolFuncEquals [l, r]

    ruleT :: FolRule -> FolTerm
    ruleT r = folApp (FolFuncRule r) (FolVar <$> ruleVars r)

    stateP :: FolTerm -> FolTerm -> FolFormula
    stateP x y = FolAtom $ folApp (FolPredState temp) [x, y]

    preP :: FolTerm -> FolTerm -> FolFormula
    preP x y = FolAtom $ folApp FolPredPre [x, y]

    conP :: FolTerm -> FolTerm -> FolFormula
    conP x y = FolAtom $ folApp FolPredCon [x, y]

    actP :: FolTerm -> FolTerm -> FolFormula
    actP x y = FolAtom $ folApp FolPredAct [x, y]

    labP :: FolTerm -> FolTerm -> FolFormula
    labP x y = FolAtom $ folApp (FolPredLab temp) [x, y]

    tempSucc :: FolTerm -> FolTerm
    tempSucc t = case temp of
                   TempAbstract -> folApp FolFuncTempSucc [t]
                   TempNat -> succT t

    startTime :: FolTerm
    startTime = case temp of
                   TempAbstract -> folApp FolFuncTempZero []
                   TempNat -> zeroT

folGoal :: FolProblem -> (Doc ann, FolFormula, TraceQuantifier)
folGoal (FolProblem _ _ _ (FolGoal name form tq) _ _) = (pretty name, form, tq)


outputSmt :: ToSmt a => a -> IO ()
outputSmt = putStr . show . toSmt

outputNice :: ToDoc a => a -> IO ()
outputNice = putStr . show . toDoc


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

qMany :: Quantifier -> [FolTerm] -> FolFormula -> FolFormula
qMany _ [] = id
qMany q (v:vs) = FolQua q (unFolVar v) . qMany q vs

allQ :: [FolTerm] -> FolFormula -> FolFormula
allQ = qMany All

exQ :: [FolTerm] -> FolFormula -> FolFormula
exQ = qMany Ex

unFolVar :: FolTerm -> FolVar
unFolVar (FolVar v) = v
unFolVar _ = undefined

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
      _frName   :: FolIdent
    , _frPrems  :: [FolTerm]
    , _frActs   :: [FolTerm]
    , _frConcls :: [FolTerm]
    }
    deriving (Show,Eq,Ord)

folFactTagName (FolFactUser _ name _) = name
folFactTagName FolFactFresh = "Fr"
folFactTagName FolFactOut  = "Out"
folFactTagName FolFactIn = "In"
folFactTagName FolFactKnown = "K"

folFuncTuple :: FolFuncId -> (FolIdent, [FolSort], FolSort)
folFuncTuple (End temp) = (FolIdentBuiltin "end", [tempSort temp], FolSortBool)
folFuncTuple (MsgSymbol s) = (msgFuncIdName s, [FolSortMsg | _ <- [1..msgFuncIdArity s]], FolSortMsg)
folFuncTuple (FolFuncAct tag) = (FolIdentUserAction $ folFactTagName tag, [FolSortMsg | _ <- [1..folFactTagArity tag]], FolSortAct)
folFuncTuple (FolFuncFact tag) = (FolIdentUserFact $ folFactTagName tag, [FolSortMsg | _ <- [1..folFactTagArity tag]], srt (folFactTagMultiplicity tag))
  where srt Persistent = FolSortPer
        srt Linear = FolSortLin
folFuncTuple (FolEq s) = (FolIdentEq, [s, s], FolSortBool)
folFuncTuple FolTempLess = (FolIdentBuiltin "tempLess", [FolSortTemp, FolSortTemp], FolSortBool)
folFuncTuple FolNatSucc = (FolIdentBuiltin "s", [FolSortNat], FolSortNat)
folFuncTuple FolNatZero = (FolIdentBuiltin "zero", [], FolSortNat)
folFuncTuple FolNatAdd = (FolIdentBuiltin "add", [FolSortNat, FolSortNat], FolSortNat)
folFuncTuple FolPredPre = (FolIdentBuiltin "Pre", [FolSortRule, FolSortPer], FolSortBool)
folFuncTuple FolPredCon = (FolIdentBuiltin "Con", [FolSortRule, FolSortPer], FolSortBool)
folFuncTuple FolPredAct = (FolIdentBuiltin "Act", [FolSortRule, FolSortAct], FolSortBool)
folFuncTuple FolFuncPre = (FolIdentBuiltin "pre", [FolSortRule, FolSortLin], FolSortNat)
folFuncTuple FolFuncCon = (FolIdentBuiltin "con", [FolSortRule, FolSortLin], FolSortNat)
folFuncTuple (FolFuncRule r) = (_frName r, snd <$> ruleVars r, FolSortRule)
folFuncTuple FolFuncEquals = (FolIdentBuiltin "equals", [FolSortLin, FolSortLin], FolSortNat)
folFuncTuple FolFuncVarFresh = (FolIdentBuiltin "fresh", [FolSortNat], FolSortMsg)
folFuncTuple FolFuncVarPub = (FolIdentBuiltin "pub", [FolSortNat], FolSortMsg)
folFuncTuple FolFuncVarNat = (FolIdentBuiltin "nat", [FolSortNat], FolSortMsg)
folFuncTuple (FolFuncState temp) = (FolIdentBuiltin "state", [FolSortLin, tempSort temp], FolSortNat)
folFuncTuple (FolPredState temp) = (FolIdentBuiltin "State", [FolSortPer, tempSort temp], FolSortBool)
folFuncTuple (FolPredLab temp) = (FolIdentBuiltin "Lab", [FolSortAct, tempSort temp], FolSortBool)
folFuncTuple FolFuncTempSucc = (FolIdentBuiltin "t+1", [FolSortTemp], FolSortTemp)
folFuncTuple FolFuncTempZero = (FolIdentBuiltin "t0", [], FolSortTemp)
folFuncTuple (FolFuncStringLiteral n srt) = (FolIdentUserLiteral $ getNameId n, [], srt)

folFuncName :: FolFuncId -> FolIdent
folFuncName f = let (n, _, _) = folFuncTuple f in n

folFuncSig :: FolFuncId -> ([FolSort], FolSort)
folFuncSig f = let (_, as, r) = folFuncTuple f in (as, r)

folFuncArity :: FolFuncId -> Int
folFuncArity = length . fst . folFuncSig

-- assertEq :: (Show a, Eq a) => a -> a -> String -> Bool
-- assertEq l r name | l == r    = True
--                   | otherwise = error ("expected " ++ name ++ " == " ++ show l ++ ". is: " ++ show r)

assertEmpty :: Show a => [a] -> String -> Bool
assertEmpty [] _name = True
assertEmpty xs name = error ("expected " ++ name ++ " to be empty. is: " ++ show xs)

unsupportedNonEmpty :: Show a => [a] -> String -> Bool
unsupportedNonEmpty [] _name = True
unsupportedNonEmpty xs name = error ("unsupported file: " ++ name)


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
                       _newVars
                       )
                   ruleAC -- ruleAC
                   ))
         |    unsupportedNonEmpty attr ("translating rules with attributes (e.g.: " ++ show name ++ ") is not supported")
           && assertEmpty ruleAC "ruleAC"
           && assertEmpty restriction "restriction"
              = Just (FolRule name'
                              (factT temp () <$> prems)
                              ( actT temp () <$> acts)
                              (factT temp () <$> concs))
           where name' = case name of
                    FreshRule -> FolIdentBuiltinRuleFresh 
                    StandRule r -> FolIdentUserRule $ r
        toRule (RuleItem r) = error ("unexpected rule" ++ show r)
        toRule _ = Nothing

assertEmptyS x = assertEmpty (Data.Set.toList x)

getTag :: LNFact -> FactTag
getTag (Fact tag factAnnotations _factTerms)
 | assertEmptyS factAnnotations "factAnnotations" = tag

infix 5 ~~
infixl 4 /\
infixl 3 \/
infixl 2 <~>
infixl 2 ~>

fun1 :: FolFuncId -> FolTerm -> FolTerm
fun1 f a0       = folApp f [a0]
fun2 :: FolFuncId -> FolTerm -> FolTerm -> FolTerm
fun2 f a0 a1    = folApp f [a0, a1]
fun3 :: FolFuncId -> FolTerm -> FolTerm -> FolTerm -> FolTerm
fun3 f a0 a1 a2 = folApp f [a0, a1, a2]

toFolProblem :: TempTranslation -> OpenTheory -> [FolProblem]
toFolProblem temp th
  = fmap (\goal -> FolProblem temp
               (toFolRules temp $ _thyItems th)
               (mapMaybe (toFolRestriction temp) $ _thyItems th)
               goal 
               (Data.Set.toList $ funSyms $ _sigMaudeInfo $ _thySignature th)
               (userEq ++ builtinEqs))
          (mapMaybe (toFolGoal temp) $ _thyItems th)
     where
       userEq = fmap (stRuleToFormula temp)
              $ Data.Set.toList $ stRules
              $ _sigMaudeInfo $ _thySignature th
       builtinEqs = join [ builtinEq b | TranslationItem (SignatureBuiltin b) <- _thyItems th ]

       builtinEq str = universalClosure <$> (case str of
                  "hashing" -> []
                  "asymmetric-encryption" -> asym
                  "signing" -> signing
                  "revealing-signing" -> revSigning
                  "symmetric-encryption" -> sym
                  "diffie-hellman" -> dh
                  "bilinear-pairing" -> dh ++ blp
                  "xor" -> xor
                  "multiset" -> multiset
                  "natural-numbers" -> natNum
                  _ -> error $ "unsupported builtin: " ++ str)
         where
           x = FolVar ("x", FolSortMsg)
           y = FolVar ("y", FolSortMsg)
           z = FolVar ("z", FolSortMsg)

           sk = FolVar ("sk", FolSortMsg)
           m = FolVar ("m", FolSortMsg)
           pk l = folApp (MsgSymbol (NoEq pkSym)) [l]
           true = folApp (MsgSymbol (NoEq trueSym)) []

           asym = [ adec (aenc m (pk sk)) sk ~~ m ]
             where
               adec = fun2 (MsgSymbol (NoEq adecSym))
               aenc = fun2 (MsgSymbol (NoEq aencSym))

           signing =  [ verify (sign m sk) m (pk sk) ~~ true ]
             where
               sign = fun2 (MsgSymbol (NoEq signSym))
               verify = fun3 (MsgSymbol (NoEq verifySym))

           revSigning =  [
               revealVerify (revealSign m sk) m (pk sk) ~~ true
             , getMessage (revealSign m sk) ~~ m
             ]
             where
               revealSign = fun2 (MsgSymbol (NoEq revealSignSym))
               revealVerify a0 a1 a2 = folApp (MsgSymbol (NoEq revealVerifySym)) [a0, a1, a2]
               getMessage l = folApp (MsgSymbol (NoEq extractMessageSym)) [l]


           sym = [ sdec (senc m k) k ~~ m ]
             where k = FolVar ("k", FolSortMsg)
                   sdec = fun2 (MsgSymbol (NoEq sdecSym))
                   senc = fun2 (MsgSymbol (NoEq sencSym))

           dh = ac (*) ++ [
               (x ^ y) ^ z  ~~ x ^ (y * z)
             ,  x ^ one     ~~ x
             ,  x * one     ~~ x
             ,  x * inv x   ~~ one
             ]
           (*) = fun2 (MsgSymbol (AC Mult))
           (^) = fun2 (MsgSymbol (NoEq expSym))
           inv t = folApp (MsgSymbol (NoEq invSym)) [t]
           one = folApp (MsgSymbol (NoEq oneSym)) []

           blp = [
               pmult x (pmult y p) ~~ pmult (x*y) p
             , pmult one p           ~~ p
             , em p q              ~~ em q p
             , em (pmult x p) q    ~~ pmult x (em q p)
             ]
             where
               p = FolVar ("p", FolSortMsg)
               q = FolVar ("q", FolSortMsg)
               pmult = fun2 (MsgSymbol (NoEq pmultSym))
               em = fun2 (MsgSymbol (C EMap))

           ac (<>) = [
                 x <> y        ~~ y <> x
               , x <> (y <> z) ~~ (x <> y) <> z
             ]
           xor = ac (<+>) ++ [
               x <+> zero      ~~ x
             , x <+> x         ~~ zero
             ]
           infix 6 <+>
           (<+>) = fun2 (MsgSymbol (AC Xor))
           zero = folApp (MsgSymbol (NoEq zeroSym)) []

           multiset = ac union
           union = fun2 (MsgSymbol (AC Union))

           natNum = ac (%+) ++ [
               allQ [n] $ exQ [m,o] $ nat n ~~ nat m %+ nat o
             , allQ [m,o] $ exQ [n] $ nat n ~~ nat m %+ nat o
             ]
             where
               nat t = folApp FolFuncVarNat [t]
               (%+) = fun2 (MsgSymbol (AC NatPlus))
               n = FolVar ("n", FolSortNat)
               m = FolVar ("m", FolSortNat)
               o = FolVar ("o", FolSortNat)


universalClosure :: FolFormula -> FolFormula
universalClosure f = allQ (fmap FolVar $ Data.Set.toList $ freeVars f) f

freeVars :: FolFormula -> Set FolVar
freeVars (FolAtom t) = Data.Set.fromList $ varSet t
freeVars (FolConn _ l r) = freeVars l `union` freeVars r
freeVars (FolConnMultiline _ as) = Prelude.foldl union Data.Set.empty (fmap freeVars as)
freeVars (FolNot f) = freeVars f
freeVars (FolBool _) = Data.Set.empty
freeVars (FolQua _ v f) =  freeVars f \\ singleton v

stRuleToFormula :: TempTranslation -> CtxtStRule -> FolFormula
stRuleToFormula temp (CtxtStRule lhs (StRhs _pos rhs)) = universalClosure $ toFolTerm temp () lhs ~~ toFolTerm temp () rhs

data FolGoal = FolGoal String FolFormula TraceQuantifier
  deriving (Show)

toFolGoal :: TempTranslation -> OpenTheoryItem -> Maybe FolGoal
toFolGoal temp (LemmaItem (Lemma name tq formula _attributes _proof)) = Just (FolGoal name (toFolFormula temp [] formula) tq)
toFolGoal _ _ = Nothing

toFolRestriction :: TempTranslation -> OpenTheoryItem -> Maybe FolRestriction
toFolRestriction temp (RestrictionItem (Restriction name formula)) = Just (FolRestriction name (toFolFormula temp [] formula))
toFolRestriction _ _ = Nothing


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
toFolSort _ LSortNat   = error $ "unreachable"
toFolSort _ LSortMsg =  FolSortMsg
toFolSort temp LSortNode = tempSort temp
-- toFolSort _ srt@LSortNat = error $ "unexpected sort: " ++ show srt

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
        LSortPub   -> folApp FolFuncVarPub   [FolVar (name, FolSortNat)]
        LSortFresh -> folApp FolFuncVarFresh [FolVar (name, FolSortNat)]
        LSortNat   -> folApp FolFuncVarNat   [FolVar (name, FolSortNat)]
        _          -> FolVar (name, toFolSort temp sort)
      where name = if idx  == 0 then n else n ++ "." ++ show idx



factOrActT :: PVar v => (FolFactTag -> FolFuncId) -> TempTranslation -> PVarCtx v -> Fact (VTerm Name v) -> FolTerm
factOrActT toFuncId temp qs (Fact tag factAnnotations terms)
 | assertEmptyS factAnnotations "factAnnotations"
   = folApp (toFuncId (toFolFactTag tag)) (toFolTerm temp qs <$> terms)
 | otherwise = error "unreachable"

factT :: PVar v => TempTranslation -> PVarCtx v -> Fact (VTerm Name v) -> FolTerm
factT = factOrActT FolFuncFact

actT :: PVar v => TempTranslation -> PVarCtx v -> Fact (VTerm Name v) -> FolTerm
actT = factOrActT FolFuncAct

sortOf :: FolTerm -> FolSort
sortOf (FolApp f _) = snd (folFuncSig f)
sortOf (FolVar (_, s)) = s

(~~) :: FolTerm -> FolTerm -> FolFormula
(~~) l r = FolAtom $ folApp (FolEq (sortOf l)) [l, r]

(~/~) :: FolTerm -> FolTerm -> FolFormula
(~/~) l r = neg (l ~~ r)

toFolAtom :: (PVar v, Show v) => TempTranslation -> PVarCtx v -> ProtoAtom Unit2 (VTerm Name v) -> FolFormula
toFolAtom temp qs (Action term fact)  = FolAtom $ folApp (FolPredLab temp) [actT temp qs fact,  toFolTerm temp qs term]
toFolAtom temp qs (EqE s t) = toFolTerm temp qs s ~~ toFolTerm temp qs t
toFolAtom TempAbstract qs (Less s t) = FolAtom $ folApp FolTempLess $ toFolTerm TempAbstract qs <$> [s,t]
toFolAtom temp@TempNat qs (Less s t) = exQ [d] (succT (addT (toFolTerm temp qs s) d)  ~~ toFolTerm temp qs t)
  where d = FolVar ("d_", FolSortNat)
        addT  = fun2 FolNatAdd
        succT = fun1 FolNatSucc
toFolAtom _ _ t@(Subterm _ _) = error $ "unsupported atom " ++ show t
toFolAtom _ _ t@(Last _) = error $ "unsupported atom " ++ show t
toFolAtom _ _ (Syntactic s) = error $ "unexpected syntactic sugar: " ++ show s

toFolTerm :: PVar v => TempTranslation -> PVarCtx v -> VTerm Name v -> FolTerm
toFolTerm temp _ (LIT (Con (Name tag id)))
  = case tag of
     FreshName -> folApp FolFuncVarFresh [folApp (FolFuncStringLiteral id FolSortNat) []]
     PubName   -> folApp FolFuncVarPub   [folApp (FolFuncStringLiteral id FolSortNat) []]
     NodeName  -> folApp (FolFuncStringLiteral id (tempSort temp)) []
     NatName   -> folApp (FolFuncStringLiteral id FolSortNat     ) []
-- toFolTerm _ _ (LIT (Con c)) = error $ "unexpected literal constant: " ++ show c
toFolTerm temp qs (LIT (Var v)) = varFromContext temp qs v
toFolTerm temp qs (FAPP f ts)
  = case f of
      AC _ -> let op l r = folApp (MsgSymbol f) [l, r]
              in foldl1 op (toFolTerm temp qs <$> ts)
      _    -> folApp (MsgSymbol f) (toFolTerm temp qs <$> ts)
