{-# LANGUAGE TemplateHaskell       #-}

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
             | FolSortFact
             | FolSortNat
             | FolSortTemp
             | FolSortBool
  deriving (Show,Ord,Eq)

data FolFuncId = Cnt
               | FSEq FolSort
               | FSLess
               | Label
               | End
               | MsgSymbol FunSym
               | FactSymbol FactTag
  deriving (Show,Ord,Eq)

data FolTerm = FolApp FolFuncId [FolTerm]
             | FolVar String FolSort
  deriving (Show)

data FolFormula = 
    FolAtom FolTerm
  | FolBool !Bool
  | FolNot FolFormula
  | FolConn Connective FolFormula FolFormula
  | FolQua !Quantifier String FolSort FolFormula
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

instance Outputable FolProblem where
  outputNice (FolProblem sig rules goals) = do 
    outputNice sig
    putStrLn ""
    putStrLn ""
    putStrLn ""
    forM_ goals $ \goal -> do
       outputNice goal
       putStrLn ""

instance Outputable FolTerm where
  outputNice (FolVar v _) = putStr v
  outputNice (FolApp f ts) = do 
    outputNice f
    putStr "("
    let acts :: [IO ()] = (intersperse (putStr ",") (fmap outputNice ts))
    forM_ acts id
    putStr ")"

instance Outputable FolFormula where
  outputNice (FolAtom t) = outputNice t
  outputNice (FolBool t) = putStr $ show t
  outputNice (FolNot t) = putStr "~"
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
  outputNice (FolQua q v s f) = do
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
    deriving (Show)

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

folFuncName :: FolFuncId -> String
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

type QuantScope = [(String, FolSort)]

toFolFormula :: QuantScope -> LNFormula -> FolFormula 
toFolFormula qs (Ato a) = FolAtom (toFolAtom qs a)
toFolFormula qs (TF x) = FolBool x
toFolFormula qs (Not x) = FolNot (toFolFormula qs x)
toFolFormula qs (Conn c l r) = FolConn c (toFolFormula qs l) (toFolFormula qs r)
toFolFormula qs (Qua q (v,s) f) = FolQua q v s' (toFolFormula ((v, s'):qs) f)
  where s' = toFolSort s

toFolSort :: LSort -> FolSort
toFolSort LSortPub   = undefined
toFolSort LSortFresh = undefined
toFolSort LSortMsg =  FolSortMsg
toFolSort LSortNode = FolSortTemp
toFolSort srt@LSortNat =  error $ "unexpected sort: " ++ show srt

factT :: QuantScope -> Fact (VTerm Name (BVar LVar)) -> FolTerm
factT qs (Fact tag factAnnotations terms) 
 | assertEmptyS factAnnotations "factAnnotations" 
   = FolApp (FactSymbol tag) (toFolTerm qs <$> terms)
 | otherwise = undefined

sortOf :: FolTerm -> FolSort 
sortOf (FolApp f _) = snd (folFuncSig f)
sortOf (FolVar _ s) = s

eqT :: FolTerm -> FolTerm -> FolTerm
eqT l r = FolApp (FSEq (sortOf l)) [l, r]

cntT :: FolTerm -> FolTerm -> FolTerm
cntT l r = FolApp Cnt [l, r]

labelT :: FolTerm -> FolTerm -> FolTerm
labelT l r = FolApp Label [l, r]

toFolAtom :: QuantScope -> ProtoAtom Unit2 (VTerm Name (BVar LVar)) -> FolTerm
toFolAtom qs (Action term fact)  =
       labelT (toFolTerm qs term) (factT qs fact)
toFolAtom qs (EqE s t) = eqT (toFolTerm qs s) (toFolTerm qs t)
toFolAtom qs (Less s t) = FolApp FSLess $ toFolTerm qs <$> [s,t]
toFolAtom qs t@(Subterm _ _) = error $ "unsupported atom " ++ show t
toFolAtom qs t@(Last _) = error $ "unsupported atom " ++ show t
toFolAtom qs (Syntactic s) = error $ "unexpected syntactic sugar: " ++ show s

toFolTerm :: QuantScope -> VTerm Name (BVar LVar) -> FolTerm
toFolTerm qs (LIT (Con c)) = error $ "unexpected literal constant: " ++ show c
toFolTerm qs (LIT (Var (Bound deBrujinIdx))) = FolVar v s
     where (v, s) = qs `genericIndex` deBrujinIdx
toFolTerm qs (LIT (Var (Free (LVar name sort _idx)))) = FolVar name (toFolSort sort)
toFolTerm qs (FAPP f ts) = FolApp (MsgSymbol f) (toFolTerm qs <$> ts)
