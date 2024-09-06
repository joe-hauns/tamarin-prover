{-# LANGUAGE TypeFamilies       #-}

module Main.Mode.Batch.ToSmtlib (
    toSmtlib
  , toFolSignature
  , toFolProblem
  , Outputable(..)
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
import Control.Monad


data Output = Output {
      _io       :: IO ()
    , _ioIndent :: Int
    }



-- oprint :: Output -> String -> Output 
-- oprint (Output io ind) s = (Output (io >> putStr s) ind + length s)
--
-- oprint :: Output -> String -> Output 
-- oprint (Output io ind) s = (Output (io >> putStr s) ind + length s)

-- (>>>) :: Output -> IO () -> Output 
-- (Output io ind) act 

-- instance Functor NiceIO where 
--   fmap f (NiceIO x y) = (NiceIO (fmap f x) y)
--
-- instance Applicative NiceIO where 
--   pure x = (NiceIO (return x) 0)
--   -- (<*>) :: NiceIO (a -> b) -> NiceIO a -> NiceIO b
--   -- (<*>) (NiceIO f i) (NiceIO a i') = (NiceIO (f <*> a) i + j)
--   liftA2 f (NiceIO l li) (NiceIO r ri) = undefined
--
--
-- bla :: NiceIO String = do 
--   return ""
--   return "bla"

-- instance Monad NiceIO where 
--   (>>=) (NiceIO x y) f = 
--       let x' = x >>= (\v -> _nio (f v))
--       in (NiceIO x' y)

data Smtlib = Smtlib
  deriving (Show)

toSmtlib :: FolSignature -> Smtlib
toSmtlib _ = Smtlib

class Outputable a where
  oNice :: a -> IO ()

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
sortName FolSortNat = "nat"
sortName FolSortTemp = "temp"
sortName FolSortBool = "bool"
sortName FolSortRule = "rule"
sortName FolSortLin = "lin"
sortName FolSortPer = "per"
sortName FolSortAct = "act"

instance Outputable FolSignature where
  oNice (FolSignature sorts funcs) = do
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
    where ops = (text $ const ' ' <$> (conStr c)) : repeat (toDoc c)

  toDoc (FolConn c s t) = text "(" <> toDoc s <+> toDoc c <+> toDoc t <> text ")"

  toDoc (FolQua q (v, s) f) = toDoc q <> text v <> text ":" <+> toDoc s <> text "(" <> toDoc f <> text ")"

instance ToDoc FolGoal where
  toDoc (FolGoal name formula) = 
    (text $ "goal " ++ name ++ ":") <+> toDoc formula

instance ToDoc SupportedRule where
  toDoc (SupportedRule name ps as cs) = 
    (text $  "rule" ++ name' ++ ": ")
      <> fToDoc ps <+> text "--" <> fToDoc as <> text "->" <+> fToDoc cs
      where fToDoc [] = text "[]"
            fToDoc fs  = foldl1 (<>) $
                 [text "[ "] 
              ++ intersperse (text ", ") (toDoc . factT () <$> fs)
              ++ [text " ]"]
            name' = case name of Just n  -> " " ++ n ++ " "
                                 Nothing -> ""



-- instance ToDoc FolSort where
--   toDoc = text . show

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
  toDoc (FolProblem sig rules goals) = vcat $
        [ toDoc sig
        , text ""
        ]
     ++ [ vcat [ toDoc r $$ nest 5 (toDoc $ translateRule r), text ""] | r <- rules]
     ++ [ text ""
        , text "" 
        , toDoc transitionRelation
        , text ""
        , text ""
        ]
     ++ [ toDoc g | g <- goals ]

-----------------------------


outputNice :: ToDoc a => a -> IO ()
outputNice = putStr . render . toDoc

instance Outputable FolSort where
  oNice = putStr . sortName

instance Outputable FolFuncId where
  oNice = putStr . folFuncName

instance Outputable FolGoal where
  oNice (FolGoal name formula) = do
    putStr $ "goal " ++ name ++ ": "
    oNice formula

instance Outputable SupportedRule where
  oNice (SupportedRule name ps as cs) = do
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
              sequence_ $ intersperse (putStr ", ") (oNice . factT () <$> fs)
              putStr " ]"


timeVar :: FolTerm
timeVar = FolVar ("__time__", FolSortTemp)
-- TODO clean var name

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

($$$) :: FolFuncId -> [FolTerm] -> FolTerm
($$$) = FolApp

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

mlConj :: [FolFormula] -> FolFormula
mlConj = FolConnMultiline And

mlDisj :: [FolFormula] -> FolFormula
mlDisj = FolConnMultiline Or

conj :: [FolFormula] -> FolFormula
conj = aggregate (FolBool True) (/\)

disj :: [FolFormula] -> FolFormula
disj = aggregate (FolBool False) (\/)

succT :: FolTerm -> FolTerm
succT t = FolNatSucc $$$ [t]

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
ruleTerm r = FolRule r $$$ (FolVar <$> ruleVars r)

sumT :: [FolTerm] -> FolTerm
sumT = aggregate (FolNatZero$$$[]) (\l r -> FolNatAdd$$$[l,r])

equalsT :: FolTerm -> FolTerm -> FolTerm
equalsT l r = FolFuncEquals $$$ [l, r]

translateRule :: SupportedRule -> FolFormula
translateRule rule@(SupportedRule _name ls as rs) =
  allQ' (ruleVars rule) $ mlConj [
     defFunAsSum pre ls
   , defFunAsSum con rs
   , defPredAsDisj (\x y -> FolAtom $ FolPredPre $$$ [x, y]) (persistent ls)
   , defPredAsDisj (\x y -> FolAtom $ FolPredCon $$$ [x, y]) (persistent rs)
   , defPredAsDisj (\x y -> FolAtom $ FolPredAct $$$ [x, y]) (factT () <$> as)
   ]
  where
    defPredAsDisj p items =
      let f = ("f", FolSortPer)
      in allQ f (p ruleT (FolVar f) <~> disj [ x ~~ FolVar f | x <- items ])
    defFunAsSum fun items =
      let f = ("f", FolSortLin)
      in allQ f (fun ruleT (FolVar f) ~~ sumT [ equalsT x (FolVar f) | x <- linear items ])
    facts mult s = [ factT () f | f <- s
                                , factMultiplicity f == mult ]
    linear = facts Linear
    persistent = facts Persistent
    pre s t = FolFuncPre $$$ [s, t]
    con s t = FolFuncCon $$$ [s, t]
    ruleT = ruleTerm rule

tempSucc :: FolTerm -> FolTerm
tempSucc t = FolFuncTempSucc $$$ [t]

transitionRelation :: FolFormula
transitionRelation = allQ t $ mlDisj [ end, ruleTransition, freshness]
   where t = ("t", FolSortTemp)
         t2 = ("t2", FolSortTemp)
         r = ("r", FolSortRule)
         n = ("n", FolSortNat)
         n' = FolVar n
         r' = FolVar r
         t' = FolVar t
         t2' = FolVar t2
         end = FolAtom $ End $$$ [FolVar t]
         ruleTransition = ex r $ mlConj [ 
             let f = ("f", FolSortLin)
                 f' = FolVar f
             in allQ f (ex n ((stateF f' t'           ~~ addF n' (preF r' f') )
                          /\ (stateF f' (tempSucc t') ~~ addF n' (conF r' f') )))
           , let f = ("f", FolSortPer)
                 f' = FolVar f
             in allQ f (( preP r' f' ~> stateP f' t' ) 
                     /\ ( stateP f' (tempSucc t') <~> ( stateP f' t' \/ conP r' f') ))
           , let f = ("f", FolSortAct)
                 f' = FolVar f
             in allQ f ( labP f' t' <~> actP r' f')
           ]
         freshness = ex n $ mlConj [
             allQ t2 (leqT t2' t' ~> (stateF t2' freshN ~~ zero))
           , stateF (tempSucc t') freshN ~~ one
           , let f = ("f", FolSortPer)
                 f' = FolVar f
             in allQ f (stateP (tempSucc t') f' <~> stateP t' f')
           , let f = ("f", FolSortLin)
                 f' = FolVar f
             in allQ f (( f' ~/~ freshN ) ~> (stateF (tempSucc t') f' ~~ stateF t' f'))
           , let f = ("f", FolSortAct)
                 f' = FolVar f
             in allQ f (neg (labP (tempSucc t') f'))
           ]
         leqT x y = ex diff (addF x diff' ~~ y)
           where diff = ("diff", FolSortTemp)
                 diff' = FolVar diff
         freshN = FactSymbol FreshFact $$$ [FolFuncFresh $$$ [n']]
         stateF x y = FolFuncState $$$ [x, y]
         stateP x y = FolAtom $ FolPredState $$$ [x, y]
         zero =  FolNatZero $$$ []
         one =  FolNatSucc $$$ [FolNatZero $$$ []]
         preP x y = FolAtom $ FolPredPre $$$ [x, y]
         conP x y = FolAtom $ FolPredCon $$$ [x, y]
         actP x y = FolAtom $ FolPredAct $$$ [x, y]
         labP x y = FolAtom $ FolPredLab $$$ [x, y]
         preF x y = FolFuncPre $$$ [x, y]
         conF x y = FolFuncCon $$$ [x, y]
         addF x y = FolNatAdd $$$ [x, y]



instance Outputable FolProblem where
  oNice (FolProblem sig rules goals) = do
    oNice sig
    putStrLn ""
    putStrLn ""
    forM_ rules $ \rule -> do
      oNice rule
      putStrLn ""
      putStr "  "
      oNice (translateRule rule)
      putStrLn ""
      putStrLn ""
    putStrLn ""
    putStrLn ""
    oNice transitionRelation
    putStrLn ""
    putStrLn ""
    forM_ goals $ \goal -> do
      oNice goal
      putStrLn ""

instance Outputable FolTerm where
  oNice (FolVar (v, _)) = putStr v
  oNice (FolApp f ts) = do
    oNice f
    putStr "("
    sequence_ $ intersperse (putStr ",") (fmap oNice ts)
    putStr ")"

instance Outputable Connective where
  oNice And = putStr "/\\"
  oNice Or = putStr "\\/"
  oNice Imp = putStr "->"
  oNice Iff = putStr "<->"

instance Outputable FolFormula where
  oNice (FolAtom t) = oNice t
  oNice (FolBool t) = putStr $ show t
  oNice (FolNot t) = sequence_ [putStr "~", oNice t]
  oNice (FolConnMultiline c fs) = do
    putStr "("
    sequence_ [ do oNice f; putStrLn "" | f <- fs]
    putStr ")"
    oNice c


  oNice (FolConn c s t) = do
    putStr "("
    oNice s
    putStr " "
    oNice c
    putStr " "
    oNice t
    putStr ")"

  oNice (FolQua q (v, s) f) = do
    putStr (case q of
      All -> "∀"
      Ex -> "∃")
    putStr $ v ++ ": "
    oNice s
    putStr "("
    oNice f
    putStr ")"

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
  varFromContext () (LVar name LSortPub _idx) = FolFuncPub $$$ [FolVar (name, FolSortNat)]
  varFromContext () (LVar name LSortFresh _idx) = FolFuncFresh $$$ [FolVar (name, FolSortNat)]
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
toFolAtom qs (Action term fact)  = FolAtom $ FolPredAct $$$ [ toFolTerm qs term, factT qs fact]
toFolAtom qs (EqE s t) = toFolTerm qs s ~~ toFolTerm qs t
toFolAtom qs (Less s t) = FolAtom $ FolApp FSLess $ toFolTerm qs <$> [s,t]
toFolAtom _ t@(Subterm _ _) = error $ "unsupported atom " ++ show t
toFolAtom _ t@(Last _) = error $ "unsupported atom " ++ show t
toFolAtom _ (Syntactic s) = error $ "unexpected syntactic sugar: " ++ show s

toFolTerm :: PVar v => PVarCtx v -> VTerm Name v -> FolTerm
toFolTerm _ (LIT (Con c)) = error $ "unexpected literal constant: " ++ show c
toFolTerm qs (LIT (Var v)) = varFromContext qs v
toFolTerm qs (FAPP f ts) = FolApp (MsgSymbol f) (toFolTerm qs <$> ts)
