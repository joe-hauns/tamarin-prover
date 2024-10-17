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
import Data.List (intercalate,genericIndex,intersperse,sortBy,groupBy)
import Data.Functor
import Debug.Trace
import qualified Data.ByteString.Char8 as BS
import Theory
import Data.Set hiding (filter)
import Term.SubtermRule
import Control.Monad
import qualified Data.ByteString.Base64 as B64

data FolIdent = FolIdentUserMsg String
              | FolIdentUserFact String
              | FolIdentUserAction String
              | FolIdentUserLiteral String
              | FolIdentUserRule String
              | FolIdentUserVar String
              | FolIdentAC String
              | FolIdentEmap
              | FolIdentTranslationBuiltin String 
              | FolIdentBuiltinRuleFresh
              | FolIdentBuiltinIntrRule IntrRuleACInfo Int
              | FolIdentInd FolIdent
              | FolIdentEq
              | FolIdentBool
              | FolIdentSort String 
    deriving (Show,Eq,Ord)
-- type FolIdent = String


--
userChar :: String
userChar = "$"
--
builtinChar :: String
builtinChar = "%"
--
identToStr :: FolIdent -> String
identToStr (FolIdentUserMsg s)     = userChar ++ s
identToStr (FolIdentUserFact s)    = userChar ++ s ++ userChar ++ "f"
identToStr (FolIdentUserAction s)  = userChar ++ s ++ userChar ++ "a"
identToStr (FolIdentUserLiteral s) = userChar ++ (BS.unpack . B64.encode . BS.pack) s ++ userChar ++ "l"
identToStr (FolIdentUserRule s)    = userChar ++ s ++ userChar ++ "r"
identToStr (FolIdentUserVar s)     = userChar ++ s
--
identToStr (FolIdentTranslationBuiltin s) = builtinChar ++ s
identToStr (FolIdentSort s)  = builtinChar ++ s
identToStr (FolIdentAC s) = builtinChar ++ s ++ builtinChar  ++ "ac"
identToStr FolIdentEmap = builtinChar ++ "emap"
identToStr FolIdentBuiltinRuleFresh = builtinChar ++ "fresh" ++ builtinChar ++ "r"
--
identToStr (FolIdentBuiltinIntrRule rule idx) = builtinChar ++ intercalate builtinChar ("md":(
   case rule of 
    (ConstrRule name) -> ["constr-rule", BS.unpack name]
    (DestrRule name i b0 b1) -> ["destr-rule", BS.unpack name, show i, show b0, show b1, show idx]-- show i, show b0, show b1]
    CoerceRule -> ["coerce"]
    IRecvRule -> ["i-recv"]
    ISendRule -> ["i-send"]
    IEqualityRule -> ["i-equality"]
    PubConstrRule -> ["pub-constr"]
    NatConstrRule -> ["nat-constr"]
    FreshConstrRule -> ["fresh-constr"]
  ))
--
identToStr (FolIdentInd id) = identToStr id ++ builtinChar  ++ "ind"
-- smtlib builtins
identToStr FolIdentEq = "="
identToStr FolIdentBool = "Bool"

data Smtlib = Smtlib
  deriving (Show)

toSmtlib :: FolSignature -> Smtlib
toSmtlib _ = Smtlib

data FolSort = FolSortMsg FolMsgType
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
                | FolFactK
                | FolFactKU
                | FolFactKD
                | FolFactFresh
  deriving (Show,Ord,Eq)

folFactTagMultiplicity :: FolFactTag -> Multiplicity
folFactTagMultiplicity (FolFactUser m _ _) = m
folFactTagMultiplicity FolFactOut = Linear
folFactTagMultiplicity FolFactIn = Linear
folFactTagMultiplicity FolFactK  = Persistent
folFactTagMultiplicity FolFactKD = Persistent
folFactTagMultiplicity FolFactKU = Persistent
folFactTagMultiplicity FolFactFresh = Linear

folFactTagArity :: FolFactTag -> Int
folFactTagArity (FolFactUser _ _ a) = a
folFactTagArity FolFactOut = 1
folFactTagArity FolFactIn = 1
folFactTagArity FolFactK  = 1
folFactTagArity FolFactKD = 1
folFactTagArity FolFactKU = 1
folFactTagArity FolFactFresh = 1

unreachableErrMsg1 :: FactTag -> a
unreachableErrMsg1 f = error $ "unreachable. " ++ show f ++ " facts are not allowed in rule definition in input file."

toFolFactTag :: FactTag -> FolFactTag
toFolFactTag (ProtoFact m s i) = FolFactUser m s i
toFolFactTag FreshFact  = FolFactFresh
toFolFactTag OutFact    = FolFactOut
toFolFactTag InFact     = FolFactIn
toFolFactTag KUFact     = FolFactKU
toFolFactTag KDFact     = FolFactKD
-- toFolFactTag f@KDFact   = unsupportedFile $ "unexpected fact in rule or formula: " ++ show f
toFolFactTag f@DedFact  = unreachableErrMsg1 f
toFolFactTag f@TermFact = unreachableErrMsg1 f

type MsgFuncId = FunSym

unsupportedFile :: String -> a
unsupportedFile msg = error ("unsupported file: " ++ msg)

msgFuncIdPrivacy :: MsgFuncId -> Privacy
msgFuncIdPrivacy (NoEq (_, (_, priv, _constr))) = priv
msgFuncIdPrivacy (AC _) = Public
msgFuncIdPrivacy (C EMap) = Public
msgFuncIdPrivacy s@List = unsupportedFile ("sort " ++ show s ++ " is not supported")

folMsgTypeWrapIdent :: FolMsgType -> FolIdent -> FolIdent
folMsgTypeWrapIdent FolMsgTypeInd = FolIdentInd 
folMsgTypeWrapIdent FolMsgTypeModE = id 

msgFuncIdName :: FolMsgType -> MsgFuncId -> FolIdent
msgFuncIdName ty m  = folMsgTypeWrapIdent ty $ msgFuncIdName' m
  where
    msgFuncIdName' (NoEq (name, (_, _, _constr))) = FolIdentUserMsg $ BS.unpack name
    msgFuncIdName' (AC ac) = FolIdentAC $ show ac
    msgFuncIdName' (C EMap) = FolIdentEmap
    msgFuncIdName' s@List = unsupportedFile ("sort " ++ show s ++ " is not supported")

msgFuncIdArity :: MsgFuncId -> Int
msgFuncIdArity (NoEq (_, (arity, _, _constr))) = arity
msgFuncIdArity (AC _) = 2
msgFuncIdArity (C EMap) = 2

data FolMsgType = FolMsgTypeInd | FolMsgTypeModE
  deriving (Show,Ord,Eq)
  -- TODO remove
msgTypeToSort ty = FolSortMsg ty

folSortMsgModE = FolSortMsg FolMsgTypeModE
folSortMsgInd = FolSortMsg FolMsgTypeInd

data FolVarType = FolVarPub | FolVarNat | FolVarFresh
    deriving (Show,Eq,Ord)

data FolFuncId = FolEq FolSort
               | FolTempLess
               | End TempTranslation
               | FolFuncMsg FolMsgType MsgFuncId
               | FolFuncMsgToClass
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
               | FolFuncVar FolMsgType FolVarType
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
folApp (FolEq (FolSortMsg FolMsgTypeInd)) args = error $ "unreachable, trying to create an equality between msg terms: " ++ intercalate ", " (fmap (show . toDoc) args) ++ ". should be done by creating an equality between there eq classes (use: " ++ show FolFuncMsgToClass ++ ")"
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
    _fpName    :: String
  , _fpTemp    :: TempTranslation
  , _fpRules   :: [FolRule]
  , _fpRestr   :: [FolRestriction]
  , _fpGoal    :: FolGoal
  , _fpMsgCons :: [FunSym]
  , _fpEq      :: [(FolTerm, FolTerm)]
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
sortName (FolSortMsg ty) = folMsgTypeWrapIdent ty $ FolIdentSort "msg"
sortName FolSortNat = FolIdentSort "nat"
sortName FolSortTemp = FolIdentSort "temp"
sortName FolSortBool = FolIdentBool
sortName FolSortRule = FolIdentSort "rule"
sortName FolSortLin = FolIdentSort "lin"
sortName FolSortPer = FolIdentSort "per"
sortName FolSortAct = FolIdentSort "act"

sortDescription :: FolSort -> Doc ann
sortDescription (FolSortMsg FolMsgTypeInd ) = pretty "message term algebra"
sortDescription (FolSortMsg FolMsgTypeModE) = pretty "message equivalence classes modulo E"
sortDescription FolSortNat = pretty "natural numbers"
sortDescription FolSortTemp = pretty "abstract time point datatype"
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
  toSmt (FolVar (v, _)) = pretty $ identToStr v 
  toSmt (FolApp f []) = toSmt f
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
          qvars = parens $ align $ vsep [ parens $ hsep [pretty . identToStr $ v, toSmt s] | (v, s) <- vs ]

instance ToSmt FolRule where
  toSmt (FolRule name _ _ _) =
    pretty ("rule " ++ identToStr name ++ ":")

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
isConstructor (FolFuncMsg FolMsgTypeInd _)   = True
isConstructor (FolFuncVar FolMsgTypeInd _) = True
isConstructor (FolFuncFact _) = True
isConstructor (FolFuncAct _)  = True
isConstructor FolNatSucc      = True
isConstructor FolNatZero      = True
isConstructor (FolFuncRule _) = True
-- isConstructor FolFuncVarFresh = True
-- isConstructor FolFuncVarPub   = True
-- isConstructor FolFuncVarNat   = True
--
isConstructor (FolFuncVar FolMsgTypeModE _) = False
isConstructor (FolFuncMsg FolMsgTypeModE _) = False
isConstructor FolFuncMsgToClass                 = False
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

smtItem s as = parens $ hsep (pretty s : as)
instance ToSmt FolSignature where
  toSmt (FolSignature sorts funcs) = vcat $ intersperse emptyDoc [
      vcat [ smtItem "declare-sort" [ toSmt s, pretty "0" ] 
             <+> pretty ";-" <+> sortDescription s  | s <- sorts
                                                    , not $ isBuiltinSmtSort s 
                                                    , not $ isInductive s]
   , vcat [ parens $ pretty "declare-datatypes" <+> align (vsep 
                [ parens $ align $ sep [ parH [toSmt s, pretty "0"] | s <- iSorts ]
                , parens $ align $ vsep $ intersperse emptyDoc [ sortConstructors s i | (s, i) <- zip iSorts [0..] ]
                ]) ]
    , vcat [ smtItem "declare-const" [ toSmt f, toSmt a ]
                   | f <- funcs
                   , let (as, a) = folFuncSig f
                   , as == []
                   , not (isBuiltinSmtFun f)
                   , not (isConstructor f) 
                   ]
    , vcat [ smtItem "declare-fun" [ toSmt f, parens $ hsep $ fmap toSmt as, toSmt a ]
                   | f <- funcs
                   , let (as, a) = folFuncSig f
                   , as /= []
                   , not (isBuiltinSmtFun f)
                   , not (isConstructor f) 
                   ]
     ]
     where isInductive s = [] /= [ f | f <- funcs
                                     , isConstructor f
                                     , folFuncRange f == s
                                     ]
           parH = parens . hsep
           iSorts = filter isInductive sorts
           sortConstructors s i = parens $ align $ vsep $
                [ pretty ";-" <+>  toSmt s <> pretty ":" <+> sortDescription s ] 
             ++ [ ctorEntry f i j | (f, j) <- zip ctors [0..]]
               where ctors = filter isConstructor $ filter (\f -> folFuncRange f == s) funcs
           ctorEntry f i j  = parH $ [ toSmt f ] ++ [ parH [dtor f i j k, toSmt a]  | (a,k) <- zip as [0..] ]
             where (as, _) = folFuncSig f
                   -- dtor i j  = toSmt f <> pretty "_" <> pretty (i::Int)
                   dtor f i j k = pretty "un" <> toSmt f <> pretty userChar <> pretty (k::Int)
                                 -- <> pretty "_" <> pretty (j::Int)
                                 -- <> pretty "_" <> pretty (k::Int)



  --     hsep (pretty "sorts: " : (toSmt <$> sorts))
  --   , vcat [ pretty "funcs:"
  --          , nest 5 (vcat [ pretty $ "  " ++ folFuncName f ++ ": " ++ ty (folFuncSig f) | f <- funcs
  --          ])
  --     ]
  --   
  --     where ty ([], r) = sortName r
  --           ty ([a], r) = sortName a ++ " -> " ++ sortName r
  --           ty (as, r) = "(" ++ intercalate ", " (sortName <$> as) ++ ") -> " ++ sortName r


commentOut :: Doc ann -> Doc ann
commentOut doc = align $ vsep (fmap (pretty ";-" <+>) (layoutLines doc))
  where 
    layoutLines :: Doc ann -> [Doc ann]
    layoutLines d = fmap pretty (lines (show d))

instance ToSmt FolProblem where
  toSmt p = vcat $ intersperse emptyDoc
     [ pretty ";-" <+> pretty "Problem:" <+> pretty (_fpName p)
     , smtItem "set-logic" [ pretty "UFDT" ]
     , toSmt (folSignature p)
     , vcat $ intersperse emptyDoc (assm <$> folAssumptions p)
     , vsep [ titleComment "goal" gName
            , smtItem "assert" [ goalToF tq goal]
            ]
     , vsep [ tqComment tq 
            , smtItem "check-sat" []
            ]
     ]
     where (gName, goal, tq) = folGoal p
           titleComment tit name = commentOut( pretty tit <> pretty ":" <+> name)
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
  toDoc (FolVar (v, _)) = pretty $ identToStr v
  toDoc (FolApp (FolEq _) [l, r]) = toDoc l <+> pretty "=" <+> toDoc r
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

  toDoc (FolQua q (v, s) f) = toDoc q <> pretty (identToStr v) <> pretty ":" <+> toDoc s <> pretty "(" <> toDoc f <> pretty ")"

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
folAssumptions (FolProblem _name temp rules rs _ msgSyms eqs) =
     [ (pretty "start condition", startCondition)
     , (pretty "transition relation", transitionRelation)
     , (pretty "addition definition", addDef)
     , (pretty "equals definition", 
        let x = FolVar (FolIdentTranslationBuiltin "x", FolSortLin)
            y = FolVar (FolIdentTranslationBuiltin "y", FolSortLin)
        in allQ [x,y] (mlConj [ equalsT x x ~~ oneT 
                              , x ~/~ y ~> equalsT x y ~~ zeroT]))
     ]
  ++ (case temp of 
           TempAbstract -> [ (pretty "less definition", 
             let x = FolVar (FolIdentTranslationBuiltin "x", FolSortTemp)
                 y = FolVar (FolIdentTranslationBuiltin "y", FolSortTemp)
                 (<) l r = FolAtom $ folApp FolTempLess [l, r]
                 zero = folApp FolFuncTempZero []
                 s x = folApp FolFuncTempSucc [x]
             in allQ [x,y] $ mlConj [
                 (zero < s x) <~> FolBool True
               , (x < zero) <~> FolBool False
               , (s x < s y) <~> (x < y)
             ])  ]
           _ -> [  ]
     )
  ++ [ (pretty "message surjectivity", eqClassSurj) ]
  ++ [ (vsep [ pretty "equational theory"
             , pretty "  " <> align (vcat [ toDoc (l ~~~ r) | (l,r) <- eqs]) ]
       , (allQ [m0, m1] (m0 ~~~ m1 <~> mlDisj (
                     [ exQ xs $ mlConj [m0 ~~~ t, m1 ~~~ t] | (fModE, _) <- allMsgSyms 
                                                             , let xs = argVars fModE 
                                                             , let t = folApp fModE xs ]
                  ++ [ exQ vs $ mlConj [m0 ~~~ l, m1 ~~ r] | (l,r) <- eqs
                                                      , let vs = fmap FolVar (uniq $ [l,r] >>= varList)
                                                      ]
                                              )))
       ) 
  ]
  ++ [ (pretty $ "inductivity link", indLink) ]
  ++ [ (align $ vsep [ toDoc r, 
                       hsep (toDoc <$> ls) <+> pretty "--[" 
                                           <+> hsep (toDoc <$> as) 
                                           <+> pretty "]->" 
                                           <+> hsep (toDoc <$> rs) 
                     ], translateRule r) | r@(FolRule _name ls as rs) <- rules ]
  ++ [ (pretty $ "restriction " ++ r, f) | (FolRestriction r f) <- rs ]
  where
    m0 = FolVar (FolIdentTranslationBuiltin "m0", folSortMsgModE)
    m1 = FolVar (FolIdentTranslationBuiltin "m1", folSortMsgModE)

    factIn    x = folApp (FolFuncFact FolFactIn   ) [x]
    factOut   x = folApp (FolFuncFact FolFactOut  ) [x]
    factK     x = folApp (FolFuncFact FolFactKU) [x]
    factFresh x = folApp (FolFuncFact FolFactFresh) [x]
    actK      x = folApp (FolFuncAct  FolFactK ) [x]
    freshVarT x = folApp (FolFuncVar FolMsgTypeModE FolVarFresh) [x]
    pubVarT x   = folApp (FolFuncVar FolMsgTypeModE FolVarPub) [x]

    addDef :: FolFormula
    addDef = FolConnMultiline And [ allQ [x   ] ( addT x zeroT     ~~ x)
                                  , allQ [x, y] ( addT x (succT y) ~~ succT (addT x y))   ]
      where x = FolVar (FolIdentTranslationBuiltin "x", FolSortNat)
            y = FolVar (FolIdentTranslationBuiltin "y", FolSortNat)

    startCondition :: FolFormula
    startCondition = mlConj [
                         allQ [fl] (stateT fl startTime ~~ zeroT)
                       , allQ [fp] (FolNot $ stateP fp startTime)
                       ]
                       where fl  = FolVar (FolIdentTranslationBuiltin "f",FolSortLin)
                             fp  = FolVar (FolIdentTranslationBuiltin "f",FolSortPer)


    x_l = FolVar (FolIdentTranslationBuiltin "l", FolSortLin)
    x_p = FolVar (FolIdentTranslationBuiltin "p", FolSortPer)
    x_a = FolVar (FolIdentTranslationBuiltin "a", FolSortAct)

    allMsgSyms = [ (FolFuncVar FolMsgTypeModE vty, FolFuncVar FolMsgTypeInd vty) | vty <- [ FolVarFresh, FolVarPub, FolVarNat ] ]
              ++ [ (FolFuncMsg FolMsgTypeModE m  , FolFuncMsg FolMsgTypeInd m  ) | m <- msgSyms]

    argVarsPref prefix f = [ FolVar (FolIdentTranslationBuiltin $ prefix ++ show i, s) | (s, i) <- folFuncDom f `zip` [1..] ]
    argVars = argVarsPref "x"

    indLink = mlConj ( uncurry eqClassIndLink <$> allMsgSyms )
      where eqClassIndLink fModE fInd = universalClosure $ 
               msgToClass (folApp fInd xs) ~~ folApp fModE xs'
                where xs  = argVars fInd 
                      xs' = [ case x of 
                                FolVar (_, FolSortMsg FolMsgTypeInd) -> msgToClass x 
                                FolVar (_, FolSortNat) -> x
                                _ -> error "this is unreachable" | x <- xs ]
    
    eqClassSurj = allQ [m] $ mlDisj [ exQ xs ( m ~~~ folApp f xs ) | (f, _) <- allMsgSyms
                                                                   , let xs = argVars f ]
      where m = FolVar (FolIdentTranslationBuiltin "m", folSortMsgModE)

    transitionRelation :: FolFormula
    transitionRelation = allQ [t] $ mlDisj [ neg $ lessT temp t (endT temp), ruleTransition, freshness]
       where t = FolVar (FolIdentTranslationBuiltin "t", tempSort temp)
             t2 = FolVar (FolIdentTranslationBuiltin "t2", tempSort temp)
             r = FolVar (FolIdentTranslationBuiltin "r", FolSortRule)
             n = FolVar (FolIdentTranslationBuiltin "n", FolSortNat)
             ruleTransition = exQ [r] $ mlConj [
                 allQ [x_l] (exQ [n] (mlConj [ 
                                     stateT x_l t    ~~ addT n (preT r x_l)
                                   , stateT x_l (tempSucc t) ~~ addT n (conT r x_l) ]))
               , allQ [x_p] $ mlConj [
                            preP r x_p ~> stateP x_p t
                         ,  stateP x_p (tempSucc t) <~> ( stateP x_p t \/ conP r x_p) ]
               , allQ [x_a] ( labP x_a t <~> actP r x_a)
               ]
             freshness = exQ [n] $ mlConj [
                 allQ [t2] (leqT t2 t ~> (stateT freshN t2 ~~ zeroT))
               , stateT freshN (tempSucc t) ~~ oneT
               , allQ [x_p] (stateP x_p (tempSucc t) <~> stateP x_p t)
               , allQ [x_l] (( x_l ~/~ freshN ) ~> (stateT x_l (tempSucc t) ~~ stateT x_l t))
               , allQ [x_a] (neg (labP x_a t))
               ]
             leqT x y = case temp of
                          TempNat      -> exQ [diff] (addT x diff ~~ y)
                          TempAbstract -> mlDisj [FolAtom (folApp FolTempLess [x, y]), x ~~ y]
               where diff = FolVar (FolIdentTranslationBuiltin "diff", tempSort temp)
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
            where f = FolVar (FolIdentTranslationBuiltin "x", srt)
        defFunAsSumOfLinearFacts fun items =
          allQ [f] (fun (ruleT rule) f ~~ sumT [ equalsT x f | x <- linear items ])
            where f = FolVar (FolIdentTranslationBuiltin "x", FolSortLin)
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
folGoal (FolProblem _ _ _ _ (FolGoal name form tq) _ _) = (pretty name, form, tq)


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

type FolVar = (FolIdent, FolSort)

ruleVars :: FolRule -> [FolVar]
ruleVars (FolRule _ ls as rs) = uniq $ (ls ++ as ++ rs) >>= varList

varList :: FolTerm -> [FolVar]
varList (FolVar v) = [v]
varList (FolApp _ as) = uniq $ as >>= varList

-- varSet :: FolTerm -> Set FolVar
-- varSet (FolVar v) = Data.Set.fromList $ [v]
-- varSet (FolApp _ as) = Data.Set.fromList as >>= varSet
--
data FolRule = FolRule {
      _frName   :: FolIdent
    , _frPrems  :: [FolTerm]
    , _frActs   :: [FolTerm]
    , _frConcls :: [FolTerm]
    }
    deriving (Show,Eq,Ord)

class ToFolIdent a where
  toFolIdent :: a -> FolIdent
 
instance ToFolIdent (IntrRuleACInfo, Int) where 
  toFolIdent = uncurry FolIdentBuiltinIntrRule
 
instance ToFolIdent ProtoRuleEInfo where 
  toFolIdent (ProtoRuleEInfo name attr restriction) 
        | unsupportedNonEmpty attr ("translating rules with attributes (e.g.: " ++ show name ++ ") is not supported")
        && assertEmpty restriction "restriction"
    = case name of
                    FreshRule -> FolIdentBuiltinRuleFresh 
                    StandRule r -> FolIdentUserRule $ r

folFactTagName :: FolFactTag -> String
folFactTagName (FolFactUser _ name _) = name
folFactTagName FolFactFresh = "Fr"
folFactTagName FolFactOut   = "Out"
folFactTagName FolFactIn    = "In"
folFactTagName FolFactK     = "K"
folFactTagName FolFactKU    = "KU"
folFactTagName FolFactKD    = "KD"

folFuncTuple :: FolFuncId -> (FolIdent, [FolSort], FolSort)
folFuncTuple (End temp) = (FolIdentTranslationBuiltin "end", [], tempSort temp)
folFuncTuple (FolFuncMsg ty s) = (msgFuncIdName ty s, [msgSort | _ <- [1..msgFuncIdArity s]], msgSort)
  where msgSort = msgTypeToSort ty
folFuncTuple FolFuncMsgToClass = (FolIdentTranslationBuiltin "class", [folSortMsgInd], folSortMsgModE)
folFuncTuple (FolFuncAct tag) = (FolIdentUserAction $ folFactTagName tag, [folSortMsgModE | _ <- [1..folFactTagArity tag]], FolSortAct)
folFuncTuple (FolFuncFact tag) = (FolIdentUserFact $ folFactTagName tag, [folSortMsgModE | _ <- [1..folFactTagArity tag]], srt (folFactTagMultiplicity tag))
  where srt Persistent = FolSortPer
        srt Linear = FolSortLin
folFuncTuple (FolEq s) = (FolIdentEq, [s, s], FolSortBool)
folFuncTuple FolTempLess = (FolIdentTranslationBuiltin "tempLess", [FolSortTemp, FolSortTemp], FolSortBool)
folFuncTuple FolNatSucc = (FolIdentTranslationBuiltin "s", [FolSortNat], FolSortNat)
folFuncTuple FolNatZero = (FolIdentTranslationBuiltin "zero", [], FolSortNat)
folFuncTuple FolNatAdd = (FolIdentTranslationBuiltin "add", [FolSortNat, FolSortNat], FolSortNat)
folFuncTuple FolPredPre = (FolIdentTranslationBuiltin "Pre", [FolSortRule, FolSortPer], FolSortBool)
folFuncTuple FolPredCon = (FolIdentTranslationBuiltin "Con", [FolSortRule, FolSortPer], FolSortBool)
folFuncTuple FolPredAct = (FolIdentTranslationBuiltin "Act", [FolSortRule, FolSortAct], FolSortBool)
folFuncTuple FolFuncPre = (FolIdentTranslationBuiltin "pre", [FolSortRule, FolSortLin], FolSortNat)
folFuncTuple FolFuncCon = (FolIdentTranslationBuiltin "con", [FolSortRule, FolSortLin], FolSortNat)
folFuncTuple (FolFuncRule r) = (_frName r, snd <$> ruleVars r, FolSortRule)
folFuncTuple FolFuncEquals = (FolIdentTranslationBuiltin "equals", [FolSortLin, FolSortLin], FolSortNat)
folFuncTuple (FolFuncVar msgTy varTy) = (folMsgTypeWrapIdent msgTy $ ident varTy, [FolSortNat], FolSortMsg msgTy)
  where ident FolVarPub   = FolIdentTranslationBuiltin "pub"
        ident FolVarFresh = FolIdentTranslationBuiltin "fresh"
        ident FolVarNat   = FolIdentTranslationBuiltin "nat"
folFuncTuple (FolFuncState temp) = (FolIdentTranslationBuiltin "state", [FolSortLin, tempSort temp], FolSortNat)
folFuncTuple (FolPredState temp) = (FolIdentTranslationBuiltin "State", [FolSortPer, tempSort temp], FolSortBool)
folFuncTuple (FolPredLab temp) = (FolIdentTranslationBuiltin "Label", [FolSortAct, tempSort temp], FolSortBool)
folFuncTuple FolFuncTempSucc = (FolIdentTranslationBuiltin "t+1", [FolSortTemp], FolSortTemp)
folFuncTuple FolFuncTempZero = (FolIdentTranslationBuiltin "t0", [], FolSortTemp)
folFuncTuple (FolFuncStringLiteral n srt) = (FolIdentUserLiteral $ getNameId n, [], srt)

folFuncName :: FolFuncId -> FolIdent
folFuncName f = let (n, _, _) = folFuncTuple f in n

folFuncSig :: FolFuncId -> ([FolSort], FolSort)
folFuncSig f = let (_, as, r) = folFuncTuple f in (as, r)

folFuncRange :: FolFuncId -> FolSort
folFuncRange = snd . folFuncSig

folFuncDom :: FolFuncId -> [FolSort]
folFuncDom = fst . folFuncSig

folFuncArity :: FolFuncId -> Int
folFuncArity = length . fst . folFuncSig

assertEmpty :: Show a => [a] -> String -> Bool
assertEmpty [] _name = True
assertEmpty xs name = error ("expected " ++ name ++ " to be empty. is: " ++ show xs)

unsupportedNonEmpty :: Show a => [a] -> String -> Bool
unsupportedNonEmpty [] _ = True
unsupportedNonEmpty _ msg = unsupportedFile msg


toFolRule :: ToFolIdent info => TempTranslation -> Rule info -> FolRule
toFolRule temp (Rule info prems concs acts _newVars) 
  = FolRule (toFolIdent info)
        (factT temp () <$> prems)
        ( actT temp () <$> acts)
        (factT temp () <$> concs)

-- :: TempTranslation -> [TheoryItem OpenProtoRule p s] -> [FolRule]

toFolRules :: TempTranslation -> [TheoryItem OpenProtoRule p s] -> [FolRule]
toFolRules temp = mapMaybe toRule
  where toRule (RuleItem (OpenProtoRule rule ruleAC)) | assertEmpty ruleAC "ruleAC" = Just (toFolRule temp rule)
        toRule (RuleItem r) = error ("unexpected rule" ++ show r)
        toRule _ = Nothing

assertEmptyS x = assertEmpty (Data.Set.toList x)

getTag :: LNFact -> FactTag
getTag (Fact tag _ _factTerms) = tag

infix 5 ~~
infixl 4 /\
infixl 3 \/
infixl 2 <~>
infixl 2 ~>
infix 5 ~~~
infix 5 ~/~

-- TODO remove
(~~~) :: FolTerm -> FolTerm -> FolFormula
(~~~) l r = l ~~  r

fun1 :: FolFuncId -> FolTerm -> FolTerm
fun1 f a0       = folApp f [a0]
fun2 :: FolFuncId -> FolTerm -> FolTerm -> FolTerm
fun2 f a0 a1    = folApp f [a0, a1]
fun3 :: FolFuncId -> FolTerm -> FolTerm -> FolTerm -> FolTerm
fun3 f a0 a1 a2 = folApp f [a0, a1, a2]

toFolProblem :: TempTranslation -> OpenTranslatedTheory -> [FolProblem]
toFolProblem temp th
  = fmap (\goal -> FolProblem 
               (_thyName th)
               temp
               ((toFolRules temp $ _thyItems th) ++ (toFolRule temp <$> builtinRules )) 
               (mapMaybe (toFolRestriction temp) $ _thyItems th)
               goal 
               (Data.Set.toList $ funSyms $ _sigMaudeInfo $ _thySignature th)
               (userEq ++ builtinEqs))
          (mapMaybe (toFolGoal temp) $ _thyItems th)
     where
       builtinRules = [ Rule (info, i) ls as rs nv
                    | let gs = groupBy (\l r -> _rInfo l == _rInfo r) 
                               $ sortBy (\l r -> _rInfo l `compare` _rInfo r) 
                               $ (_thyCache th) 
                    , g <- trace ("grouping: " ++ show [ _rInfo x | g <- gs, x <- g ]) gs
                    , (i, Rule info ls as rs nv) <- zip [(0 :: Int)..] g 
                    ]

       infix 5 ~~~
       (~~~) l r = (l,r)

       userEq = fmap (stRuleToFormula temp)
              $ Data.Set.toList $ stRules
              $ _sigMaudeInfo $ _thySignature th

       stRuleToFormula temp (CtxtStRule lhs (StRhs _pos rhs)) = toFolTerm temp () lhs ~~~ toFolTerm temp () rhs

       builtinEqs = join [
           if enableDH   sig then dh else []
         , if enableBP   sig then dh ++ blp else []
         , if enableMSet sig then multiset else []
         , if enableXor  sig then xor else []
         , if enableNat  sig then error "unsupported builtin: natural-numbers" else []
         ] 
         where
           sig = _sigMaudeInfo $ _thySignature th

           x = FolVar (FolIdentTranslationBuiltin "x", folSortMsgModE)
           y = FolVar (FolIdentTranslationBuiltin "y", folSortMsgModE)
           z = FolVar (FolIdentTranslationBuiltin "z", folSortMsgModE)

           sk = FolVar (FolIdentTranslationBuiltin "sk", folSortMsgModE)
           m = FolVar (FolIdentTranslationBuiltin "m", folSortMsgModE)
           pk l = folApp (FolFuncMsg FolMsgTypeModE (NoEq pkSym)) [l]
           true = folApp (FolFuncMsg FolMsgTypeModE (NoEq trueSym)) []

           dh = ac (*) ++ [
               (x ^ y) ^ z  ~~~ x ^ (y * z)
             ,  x ^ one     ~~~ x
             ,  x * one     ~~~ x
             ,  x * inv x   ~~~ one
             ]
           (*) = fun2 (FolFuncMsg FolMsgTypeModE (AC Mult))
           (^) = fun2 (FolFuncMsg FolMsgTypeModE (NoEq expSym))
           inv t = folApp (FolFuncMsg FolMsgTypeModE (NoEq invSym)) [t]
           one = folApp (FolFuncMsg FolMsgTypeModE (NoEq oneSym)) []

           blp = [
               pmult x (pmult y p) ~~~ pmult (x*y) p
             , pmult one p         ~~~ p
             , em p q              ~~~ em q p
             , em (pmult x p) q    ~~~ pmult x (em q p)
             ]
             where
               p = FolVar (FolIdentTranslationBuiltin "p", folSortMsgModE)
               q = FolVar (FolIdentTranslationBuiltin "q", folSortMsgModE)
               pmult = fun2 (FolFuncMsg FolMsgTypeModE (NoEq pmultSym))
               em = fun2 (FolFuncMsg FolMsgTypeModE (C EMap))

           ac (<>) = [
                 x <> y        ~~~ y <> x
               , x <> (y <> z) ~~~ (x <> y) <> z
             ]
           xor = ac (<+>) ++ [
               x <+> zero      ~~~ x
             , x <+> x         ~~~ zero
             ]
           infix 6 <+>
           (<+>) = fun2 (FolFuncMsg FolMsgTypeModE (AC Xor))
           zero = folApp (FolFuncMsg FolMsgTypeModE (NoEq zeroSym)) []

           multiset = ac union
           union = fun2 (FolFuncMsg FolMsgTypeModE (AC Union))

existentialClosure :: FolFormula -> FolFormula
existentialClosure f = exQ (fmap FolVar $ Data.Set.toList $ freeVars f) f

universalClosure :: FolFormula -> FolFormula
universalClosure f = allQ (fmap FolVar $ Data.Set.toList $ freeVars f) f

freeVars :: FolFormula -> Set FolVar
freeVars (FolAtom t) = Data.Set.fromList $ varList t
freeVars (FolConn _ l r) = freeVars l `union` freeVars r
freeVars (FolConnMultiline _ as) = Prelude.foldl union Data.Set.empty (fmap freeVars as)
freeVars (FolNot f) = freeVars f
freeVars (FolBool _) = Data.Set.empty
freeVars (FolQua _ v f) =  freeVars f \\ singleton v

data FolGoal = FolGoal String FolFormula TraceQuantifier
  deriving (Show)

toFolGoal :: TempTranslation -> TheoryItem r p s -> Maybe FolGoal
toFolGoal temp (LemmaItem (Lemma name tq formula _attributes _proof)) = Just (FolGoal name (toFolFormula temp [] formula) tq)
toFolGoal _ _ = Nothing

toFolRestriction :: TempTranslation -> TheoryItem r p s -> Maybe FolRestriction
toFolRestriction temp (RestrictionItem (Restriction name formula)) = Just (FolRestriction name (toFolFormula temp [] formula))
toFolRestriction _ _ = Nothing


type QuantScope = [(String, LSort)]

toFolFormula :: TempTranslation -> QuantScope -> LNFormula -> FolFormula
toFolFormula temp qs (Ato a) = toFolAtom temp qs a
toFolFormula _ _ (TF x) = FolBool x
toFolFormula temp qs (Not x) = FolNot (toFolFormula temp qs x)
toFolFormula temp qs (Conn c l r) = FolConn c (toFolFormula temp qs l) (toFolFormula temp qs r)
toFolFormula temp qs (Qua q (v,s) f) = case s of 
      LSortNode ->  guardedQ q var' (lessT temp (FolVar var') (endT temp)) f'
      _         ->  FolQua q var' f'
  where s' = toFolSort temp s
        var' = (FolIdentUserVar v, s')
        f' = toFolFormula temp ((v, s):qs) f

guardedQ :: Quantifier -> FolVar -> FolFormula -> FolFormula -> FolFormula
guardedQ All v f1 f2 = FolQua All v (f1 ~> f2)
guardedQ Ex  v f1 f2 = FolQua Ex  v (f1 /\ f2)

endT temp = folApp (End temp) []

lessT temp x y = case temp of
            TempNat      -> exQ [diff] (folApp FolNatAdd [x, folApp FolNatSucc [diff]] ~~ y)
            TempAbstract -> FolAtom (folApp FolTempLess [x, y])
  where diff = FolVar (FolIdentTranslationBuiltin "diff", tempSort temp)

toFolSort :: TempTranslation -> LSort -> FolSort
toFolSort _ LSortPub   = FolSortNat
toFolSort _ LSortFresh = FolSortNat
toFolSort _ LSortNat   = FolSortNat
toFolSort _ LSortMsg   = folSortMsgModE
toFolSort temp LSortNode = tempSort temp
-- toFolSort _ srt@LSortNat = error $ "unexpected sort: " ++ show srt

class PVar a where
  type PVarCtx a

  varFromContext :: TempTranslation -> PVarCtx a -> a -> FolTerm

instance PVar (BVar LVar) where
  type PVarCtx (BVar LVar) = QuantScope

  varFromContext temp qs (Bound deBrujinIdx) = lvarToFolVar temp v
    where v = qs `genericIndex` deBrujinIdx
          
  varFromContext temp _ (Free v) = varFromContext temp () v

lvarToFolVar :: TempTranslation -> (String, LSort) -> FolTerm
lvarToFolVar temp (name, sort) =
     case sort of
        LSortPub   -> folApp (FolFuncVar FolMsgTypeModE FolVarPub)   [FolVar (FolIdentUserVar name, FolSortNat)]
        LSortFresh -> folApp (FolFuncVar FolMsgTypeModE FolVarFresh) [FolVar (FolIdentUserVar name, FolSortNat)]
        LSortNat   -> folApp (FolFuncVar FolMsgTypeModE FolVarNat)   [FolVar (FolIdentUserVar name, FolSortNat)]
        _   -> FolVar (FolIdentUserVar name, toFolSort temp sort)

instance PVar LVar where
  type PVarCtx LVar = ()

  varFromContext temp () (LVar n sort idx)
    = lvarToFolVar temp (name, sort)
    -- = case sort of
    --     LSortPub   -> folApp FolFuncVarPub   [FolVar (name, FolSortNat)]
    --     LSortFresh -> folApp FolFuncVarFresh [FolVar (name, FolSortNat)]
    --     LSortNat   -> folApp FolFuncVarNat   [FolVar (name, FolSortNat)]
    --     LSortMsg   -> FolVar (name, toFolSort temp sort)
      where name = if idx  == 0 then n else n ++ "." ++ show idx



factOrActT :: PVar v => (FolFactTag -> FolFuncId) -> TempTranslation -> PVarCtx v -> Fact (VTerm Name v) -> FolTerm
factOrActT toFuncId temp qs (Fact tag _annot terms) = folApp (toFuncId (toFolFactTag tag)) (toFolTerm temp qs <$> terms)

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

-- TODO axiomatise
msgToClass :: FolTerm -> FolTerm
msgToClass = fun1 FolFuncMsgToClass

toFolAtom :: (PVar v, Show v) => TempTranslation -> PVarCtx v -> ProtoAtom Unit2 (VTerm Name v) -> FolFormula
toFolAtom temp qs (Action time act)  = FolAtom $ folApp (FolPredLab temp) [actT temp qs act,  toFolTerm temp qs time]
toFolAtom temp qs (EqE s t) = case sortOf s' of 
                               (FolSortMsg FolMsgTypeModE) -> s' ~~~ t'
                               _          -> s' ~~ t'
   where s' = toFolTerm temp qs s
         t' = toFolTerm temp qs t
toFolAtom TempAbstract qs (Less s t) = FolAtom $ folApp FolTempLess $ toFolTerm TempAbstract qs <$> [s,t]
toFolAtom temp@TempNat qs (Less s t) = exQ [d] (succT (addT (toFolTerm temp qs s) d)  ~~ toFolTerm temp qs t)
  where d = FolVar (FolIdentTranslationBuiltin "d", FolSortNat)
        addT  = fun2 FolNatAdd
        succT = fun1 FolNatSucc
toFolAtom _ _ t@(Subterm _ _) = unsupportedFile $ "unsupported atom " ++ show t
toFolAtom _ _ t@(Last _)      = unsupportedFile $ "unsupported atom " ++ show t
toFolAtom _ _ (Syntactic s) = error $ "unexpected syntactic sugar: " ++ show s

toFolTerm :: PVar v => TempTranslation -> PVarCtx v -> VTerm Name v -> FolTerm
toFolTerm temp _ (LIT (Con (Name tag id)))
  = case tag of
     FreshName -> folApp (FolFuncVar FolMsgTypeModE FolVarFresh) [folApp (FolFuncStringLiteral id FolSortNat) []]
     PubName   -> folApp (FolFuncVar FolMsgTypeModE FolVarPub)   [folApp (FolFuncStringLiteral id FolSortNat) []]
     NodeName  -> folApp (FolFuncStringLiteral id (tempSort temp)) []
     NatName   -> folApp (FolFuncStringLiteral id FolSortNat     ) []
-- toFolTerm _ _ (LIT (Con c)) = error $ "unexpected literal constant: " ++ show c
toFolTerm temp qs (LIT (Var v)) = varFromContext temp qs v
toFolTerm temp qs (FAPP f ts) 
  = case f of
      AC _ -> let op l r = folApp (FolFuncMsg FolMsgTypeModE f) [l, r]
              in foldl1 op (toFolTerm temp qs <$> ts)
      _    -> folApp (FolFuncMsg FolMsgTypeModE f) (toFolTerm temp qs <$> ts)
-- toFolTerm temp qs (FAPP f ts)
--   = case f of
--       AC _ -> let op l r = folApp (MsgSymbol f) [l, r]
--               in foldl1 op (toFolTerm temp qs <$> ts)
--       _    -> folApp (MsgSymbol f) (toFolTerm temp qs <$> ts)
