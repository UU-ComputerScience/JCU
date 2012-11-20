module Models where

import Language.UHC.JS.ECMA.String
import Language.UHC.JS.Primitives
import Language.UHC.JS.Types

import Data.List (find)

import ParseLib.Abstract
import qualified Language.Prolog.NanoProlog.NanoProlog as NP
import Language.Prolog.NanoProlog.ParserUUTC


type ProofResult = String -- I want to make an enum of this

data ProofTreeNode
  = Node
  {  term  :: String
  ,  mcid  :: String
  ,  childTerms   :: [ProofTreeNode]
  ,  proofResult  :: ProofResult
  }

data Rule
  = Rule
  {  id    :: Int
  ,  ro    :: Int
  ,  rule  :: JSString
  }

data JSRulePtr
type JSRule = JSPtr JSRulePtr

instance FromJS JSRule (IO Rule) where
  fromJS = jsRuleToRule

jsRuleToRule :: JSRule -> IO Rule
jsRuleToRule ptr = do
  id    <- getAttr "id"   ptr
  ro    <- getAttr "ro"   ptr
  rule  <- getAttr "rule" ptr
  return $ Rule id ro rule

proofTreeNode :: ProofTreeNode
proofTreeNode = Node "" "" [] ""

foreign import js "%1.rule"
  getRule :: JSRule -> JSString

hasValidTermSyntax :: String -> Bool
hasValidTermSyntax term = maybe False (const True) (tryParseTerm term)

tryParseTerm :: String -> Maybe NP.Term
tryParseTerm = run pTerm

hasValidRuleSyntax :: String -> Bool
hasValidRuleSyntax rule = maybe False (const True) (tryParseRule rule)

tryParseRule :: String -> Maybe NP.Rule
tryParseRule = run pRule

run :: Parser a b -> [a] -> Maybe b
run p as = fmap fst . find (null . snd) $ startParse p as

pRules :: Parser Char [NP.Rule]                      
pRules = bracketed (commaList pRule <|> succeed [])

instance Read NP.Rule where
  readsPrec _ str = case find (null . snd) $ startParse pRule str of
                      (Just r) -> [r]
                      Nothing  -> []
  readList str = case find (null . snd) $ startParse pRules str of
                   (Just r) -> [r]
                   Nothing  -> []
