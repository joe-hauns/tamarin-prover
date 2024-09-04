{-# LANGUAGE TemplateHaskell       #-}

module Main.Mode.Batch.ToSmtlib (
    toSmtlib
  , toFolSignature
  , Outputable(..)
  ) where

import Items.OpenTheoryItem
import TheoryObject
import Theory.Model
import Theory.Model.Atom (Unit2(..))
import Data.Maybe
import Data.List (intercalate)
import Data.Functor
import Data.ByteString.Char8 (unpack)
import Theory
import Data.Set
import Control.Monad

data Smtlib = Smtlib
  deriving (Show)

toSmtlib :: FolSignature temp -> Smtlib
toSmtlib _ = Smtlib

class Outputable a where
  outputNice :: a -> IO ()

data FolSort temp = MsgSort
                  | FactSort
                  | Nat
                  | Temp
                  | BoolSort
  deriving (Show)

data FolFuncId temp = Cnt
                  | Label
                  | End
                  | MsgSymbol FunSym
                  | FactSymbol FactTag
  deriving (Show,Ord,Eq)

data FolTerm = FolApp (FolFuncId TempNat) [FolTerm]
  deriving (Show)

-- TODO get rid of temp

data FolFormula = 
    FolAtom FolTerm
  | FolBool !Bool
  | FolNot FolFormula
  | FolConn Connective FolFormula FolFormula
  | FolQua !Quantifier String (FolSort TempNat) FolFormula
  deriving (Show)

data FolProblem temp = FolProblem {
    _fpSig     :: FolSignature temp
  , _fpRules   :: [SupportedRule]
  , _fpFormula :: [FolGoal]
  }
  deriving (Show)

data FolSignature temp = FolSignature {
    _fsigSorts :: [ FolSort temp ]
  , _fsigFuncs :: [ FolFuncId temp ]
  }
  deriving (Show)

instance Outputable (FolSignature temp) where
  outputNice (FolSignature sorts funcs) = do
    putStrLn "sorts: "
    forM_ sorts $ \s ->  do
      putStrLn $ "  " ++ show s
    putStrLn ""
    putStrLn "funcs:"
    forM_ funcs $ \f ->  do
      putStrLn $ "  " ++ folFuncName f ++ ": " ++ ty (folFuncSig f)
      where ty ([], r) = show r
            ty ([a], r) = show a ++ " -> " ++ show r
            ty (as, r) = "(" ++ intercalate ", " (show <$> as) ++ ") -> " ++ show r


data TempQ = TempQ
  deriving (Show)

data TempNat = TempNat
  deriving (Show)

data SupportedRule = SupportedRule {
      _srName :: Maybe String
    , _srPrems :: [LNFact]
    , _srActs :: [LNFact]
    , _srConcls :: [LNFact]
    }
    deriving (Show)

folFuncSig :: FolFuncId temp -> ([FolSort temp], FolSort temp)
folFuncSig Cnt = ([Temp, FactSort], Nat)
folFuncSig Label = ([Temp, FactSort], BoolSort)
folFuncSig End = ([Temp], BoolSort)
folFuncSig (MsgSymbol (NoEq (_name, (arity, _priv, _constr)))) = ([MsgSort | _ <- [1..arity]], MsgSort)
folFuncSig (MsgSymbol (AC _ac)) = ([MsgSort, MsgSort], MsgSort)
folFuncSig (MsgSymbol (C EMap)) = error "EMap message not supported (yet)"
folFuncSig (MsgSymbol List) = error "List message not supported (yet)"
folFuncSig (FactSymbol tag) = ([MsgSort | _ <- [1..factTagArity tag]], FactSort)

folFuncName :: FolFuncId temp -> String
folFuncName Cnt = "cnt"
folFuncName Label = "label"
folFuncName End = "end"
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

toFolSignature :: OpenTheory -> FolSignature TempNat
toFolSignature (Theory _name _inFile _heuristic _tactic signature _cache items _options _isSapic) = FolSignature {
    _fsigSorts = [ MsgSort, FactSort, Nat, Temp, BoolSort]
  , _fsigFuncs = [ Cnt, Label, End ]
              ++ fmap MsgSymbol (Data.Set.toList $ funSyms $ _sigMaudeInfo signature)

              ++ fmap FactSymbol (toList $ Data.Set.fromList (tags ++ [ FreshFact, OutFact, InFact, KUFact, KDFact, DedFact ]))
  }
 where tags = toFolRules items
          >>= (\(SupportedRule _name l p r) -> l ++ p ++ r)
          <&> getTag


toFolProblem :: OpenTheory -> FolProblem TempNat
toFolProblem th = FolProblem (toFolSignature th) (toFolRules $ _thyItems th) (mapMaybe toFolGoal $ _thyItems th)

data FolGoal = FolGoal String FolFormula 
  deriving (Show)

toFolGoal :: OpenTheoryItem -> Maybe FolGoal
toFolGoal (LemmaItem (Lemma name AllTraces formula _attributes _proof)) = Just (FolGoal name (toFolFormula formula))

toFolFormula :: LNFormula -> FolFormula 
toFolFormula (Ato a) = FolAtom (toFolAtom a)
toFolFormula (TF x) = FolBool x
toFolFormula (Not x) = FolNot (toFolFormula x)
toFolFormula (Conn c l r) = FolConn c (toFolFormula l) (toFolFormula r)
toFolFormula (Qua q (v,s) f) = FolQua q v (toFolSort s) (toFolFormula f)
  where toFolSort LSortPub   = undefined
        toFolSort LSortFresh = undefined
        toFolSort LSortMsg =  MsgSort
        toFolSort srt@LSortNode =  error $ "unexpected sort: " ++ show srt
        toFolSort LSortNat =  Nat

toFolAtom :: ProtoAtom Unit2 (VTerm Name (BVar LVar)) -> FolTerm
toFolAtom (Action term (Fact tag factAnnotations terms)) 
 | assertEmptyS factAnnotations "factAnnotations" = FolApp (FactSymbol tag) (toFolTerm <$> terms)
 | otherwise = undefined
toFolAtom (EqE s t) = undefined
toFolAtom (Subterm s t) = undefined
toFolAtom (Less s t) = undefined
toFolAtom (Last t) = undefined
toFolAtom (Syntactic s) = error $ "unexpected syntactic sugar: " ++ show s

toFolTerm :: VTerm Name (BVar LVar) -> FolTerm
toFolTerm = undefined
