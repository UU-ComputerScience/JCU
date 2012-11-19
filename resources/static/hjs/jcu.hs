module JCU where

import qualified Control.Monad as CM (liftM, foldM, when)

import Data.Array (elems)
import Data.IORef
import Data.List as DL
import Data.LocalStorage
import Data.Map   (fromList)
import Data.Maybe (fromJust)
import Data.Tree as T

import Language.UHC.JS.Prelude
import Language.UHC.JS.Types -- (JS, toJS, fromJS, FromJS)
import Language.UHC.JS.Primitives
import Language.UHC.JS.JQuery.JQuery as JQ
import Language.UHC.JS.W3C.HTML5 as HTML5

import Language.UHC.JS.ECMA.Bool
import Language.UHC.JS.ECMA.String as JSString


import Language.UHC.JS.Assorted (alert , _alert)

import Language.UHC.JS.JQuery.Draggable
import Language.UHC.JS.JQuery.Droppable

import qualified Language.Prolog.NanoProlog.NanoProlog as NP
import Language.Prolog.NanoProlog.ParserUUTC

import Language.UHC.JS.JQuery.Deferred

{-import Language.UHC.JScript.WebWorker -}

----
--  App
----

import qualified Prolog

import qualified Language.UHC.JS.ECMA.Array as ECMAArray (JSArray, jsArrayToArray)

import Array

import Templates
import Models

type RulesRef = IORef [NP.Rule]

----
--   Constants
----

ruleTreeId     = "ul#proof-tree-view.tree"
storeDoCheckId = "#storeDoChecking"

----
--   Helpers
----
showError = alert
showInfo  = alert

-- | Update an existing input field that is used to store `global' variables
--   Not entirely best practice. This should perhaps be modelled in a State
--   monad.
updateStore :: (Read a, Show a) => Selector -> (a -> a) -> IO ()
updateStore sel updateF = do
  store <- jQuery sel
  val   <- fmap read (valString store)
  setValString store (show $ updateF val)

-- | Read the contents of the store
-- TODO: Update this to use HTML5 local storage
readStore :: (Read a) => Selector -> IO a
readStore sel = fmap read (jQuery storeDoCheckId >>= valString)

rulesStoreKey = "rules"

-- | Reads the stored rules from the local datastore (HTML5)
readRulesFromStore :: IO [NP.Rule]
readRulesFromStore = do
  rules <- getLocalStorage rulesStoreKey :: IO [NP.Rule]
  return rules
  -- ajaxQ GET "/rules/stored" obj (addRules rlsref) noop

-- | Write the rules directly to storage
writeRulesInStore :: [NP.Rule] -> IO ()
writeRulesInStore = setLocalStorage "rules"

-- | Modify the rules in the storage
modifyRulesInStore :: ([NP.Rule] -> [NP.Rule]) -> IO ()
modifyRulesInStore f = fmap f readRulesFromStore >>= writeRulesInStore
  
-- | Adds the given Rule to the local datastore
addRuleToStore :: NP.Rule -> IO (Maybe Int)
addRuleToStore rule = do
  rules <- readRulesFromStore
  case elemIndex rule rules of
    Just n  -> return Nothing
    Nothing -> do writeRulesInStore (rules ++ [rule])
                  return . Just $ DL.length rules + 1

-- | Deletes a given rule from the store (using the ID)
deleteRuleFromStore :: Int -> IO ()
deleteRuleFromStore id = modifyRulesInStore dropX
  where
  dropX rules = let (ys,zs) = splitAt id rules
                in   ys ++ (tail zs)
  

----
--   Application
----
main :: IO ()
main = do
  path <- pathName
  init <- wrapIO initProofTree
  onDocumentReady init


checkTermSyntax :: EventHandler
checkTermSyntax _ = do
  inp   <- jQuery "#txtAddRule"
  input <- valString inp
  case tryParseRule input of
    Nothing  -> markInvalidTerm inp
    _        -> return ()
  return True

noevent :: EventHandler
noevent _ = return False

initProofTree :: IO ()
initProofTree = do -- Rendering
  l <- jQuery "#mainLeft"
  rules <- readRulesFromStore
  rlsref <- newIORef rules

  -- Proof tree
  addRuleTree rlsref
  -- Rules list
  addRules rlsref
  
  registerEvents  [  ("#btnCheck"  ,         Click   , toggleClue rlsref emptyProof)
                  ,  ("#btnAddRule",         Click   , addRuleEvent rlsref)
                  ,  ("#btnReset"  ,         Click   , resetTree rlsref)
                  ,  ("#btnLoadExampleData", Click   , loadExampleData rlsref)
                  ,  ("#txtAddRule", KeyPress, clr rlsref)
                  ,  ("#txtAddRule", Blur    , checkTermSyntax) ]
  where  resetTree rlsref _ = do -- Do not forget to add the class that hides the colours
           jQuery "#proof-tree-div" >>= flip addClass "noClue"
           -- Always store False in the store.
           updateStore storeDoCheckId (const False)
           replaceRuleTree rlsref emptyProof
           return True
         clr rlsref obj = do
           which <- getAttr "which" obj
           CM.when ((which :: Int) == 13) $
             addRuleEvent rlsref undefined >> return ()
           jQuery "#txtAddRule" >>= clearClasses >> return True

-- Toggles checking of the proof and showing the results
toggleClue :: RulesRef -> Prolog.Proof -> EventHandler
toggleClue rlsref p _ = do
  toggleClassString "#proof-tree-div" "noClue"
  updateStore storeDoCheckId not
  replaceRuleTree rlsref p
  return True

emptyProof :: Prolog.Proof
emptyProof = T.Node (NP.Var "") []

addRuleTree :: RulesRef -> IO ()
addRuleTree rlsref = do
  let status = T.Node Prolog.Correct []
  ruleTreeDiv <- jQuery "#proof-tree-div"
  ruleTreeUL  <- buildRuleUl rlsref emptyProof status
  setHTML ruleTreeDiv "" -- TODO: This is ugly....
  append ruleTreeDiv ruleTreeUL

-- | Builds up the rule tree
buildRuleUl :: RulesRef -> Prolog.Proof -> Prolog.PCheck -> IO JQuery
buildRuleUl rlsref node status =
  do topUL <- jQuery "<ul id=\"proof-tree-view\" class=\"tree\"/>"
     restUL <- build' rlsref [0] node (node, status) False
     append topUL restUL
     inputField <- findSelector restUL "input"
     eh  <- mkJThisEventHandler (fCheck rlsref)
     eh' <- wrappedJQueryEvent eh
     _bind inputField (toJS "blur") eh'
     return topUL
  where
    f :: RulesRef -> [Int] -> Prolog.Proof -> (JQuery, Int) -> (Prolog.Proof, Prolog.PCheck) -> IO (JQuery, Int)
    f rlsref lvl wp (jq, n) (node, status) = do
      li' <- build' rlsref (lvl ++ [n]) wp (node,status) True
      append jq li'
      return (jq, n + 1)
    onDrop :: RulesRef -> Prolog.Proof -> [Int] -> Prolog.Proof -> UIThisEventHandler
    onDrop rlsref wp lvl node this _ ui = do
      elemVal <- findSelector this "input[type='text']:first" >>= valString
      jsRuleText <- (getAttr "draggable" ui >>= getAttr "context" >>= getAttr "innerText") :: IO JSString
      let ruleText = fromJS jsRuleText :: String
      if null elemVal
        then  showError "There needs to be a term in the text field!"
        else  case tryParseRule ruleText of
                Nothing  -> showError "This should not happen. Dropping an invalid rule here."
                Just t   -> case Prolog.dropUnify wp lvl t of
                              Prolog.DropRes False  _  -> showError "I could not unify this."
                              Prolog.DropRes True   p  -> replaceRuleTree rlsref p
      return True

    build' :: RulesRef -> [Int] -> Prolog.Proof -> (Prolog.Proof, Prolog.PCheck) -> Bool -> IO JQuery
    build' rlsref lvl wp (n@(T.Node term chts), T.Node status chstat) disabled = do
      li <- jQuery "<li/>"
      appendString li $ proof_tree_item (show term) (intercalate "." $ map show lvl) disabled status
      dropzones <- findSelector li ".dropzone"
      drop      <- mkJUIThisEventHandler (onDrop rlsref wp lvl n) >>= wrappedJQueryUIEvent
      droppable dropzones $ Droppable (toJS "dropHover") drop
      startUl   <- jQuery "<ul/>"
      (res, _)  <- CM.foldM (f rlsref lvl wp) (startUl, 1) (zip chts chstat)
      append li res
      return li

    fCheck :: RulesRef -> ThisEventHandler
    fCheck rlsref this _ = do
      term <- valString this
      case tryParseTerm term of
        Just t  -> replaceRuleTree rlsref $ T.Node t []
        _       -> markInvalidTerm this
      return False

replaceRuleTree :: RulesRef -> Prolog.Proof -> IO ()
replaceRuleTree rlsref p = do
  status  <- checkProof rlsref p
  oldUL   <- jQuery ruleTreeId
  newUL   <- buildRuleUl rlsref p status
  -- Store new proof in the subst funct
  registerEvents  [  ("#btnCheck", Click, toggleClue rlsref p)
                  ,  ("#btnSubst", Click, doSubst rlsref p) ]
  -- Draw the new ruleTree
  replaceWith oldUL newUL
  CM.when (complete status) $
    showInfo "Congratulations! You have successfully completed your proof!"
  where  complete :: Prolog.PCheck -> Bool
         complete (T.Node Prolog.Correct [])  = True
         complete (T.Node Prolog.Correct xs)  = all complete xs
         complete _                    = False

addRules :: RulesRef -> IO ()
addRules rlsref = do
  rules_list_div <- jQuery "#rules-list-div"
  rules_list_ul  <- jQuery "<ul id=\"rules-list-view\"/>"
  append rules_list_div rules_list_ul
  addRulesList rlsref
  
addRulesList :: RulesRef -> IO ()
addRulesList rlsref = do
  rules_list_ul <- jQuery "#rules-list-view"
  empty rules_list_ul
  rules <- readIORef rlsref
  let f (idx, rule) = do listItem <- createRuleLi rlsref (show rule) idx
                         append rules_list_ul listItem
                         return ()
  mapM f (zip [0..] rules)
  
  onStart <- mkJUIEventHandler (\x y -> do focus <- jQuery ":focus"
                                           doBlur focus
                                           return False)
  draggables <- jQuery ".draggable"
  draggable draggables $ Draggable (toJS True) (toJS "document") (toJS True) 100 50 onStart
  return ()
  where addRuleRef rl lst = case tryParseRule (fromJS rl) of
                              Nothing  -> lst
                              Just r   -> r : lst

addRuleEvent :: RulesRef -> EventHandler
addRuleEvent rlsref event = do
  rule  <- jQuery "#txtAddRule" >>= valJSString
  case tryParseRule (fromJS rule) of
    Nothing  ->  showError $ "Invalid rule, not adding to rule list." ++ (fromJS rule)
    Just r   ->  do  success <- addRuleToStore r
                     case success of
                       Nothing -> showError $ "Rule already exists"
                       _       -> do modifyIORef rlsref (++ [r])
                                     addRulesList rlsref
                                     jQuery "#txtAddRule" >>= flip setValString ""
  return True
  
createRuleLi :: RulesRef -> String -> Int -> IO JQuery
createRuleLi rlsref rule id = do
  item <- jQuery $ "<li>" ++ rules_list_item rule ++ "</li>"
  delButton <- findSelector item "button.btnDeleteList"
  click delButton (deleteRule rlsref item id)
  return item

-- | Checks the current proof against the current list of rules. If the user
--   added rules in a different window or deleted them there those changes will
--   not be visible here.
checkProof :: RulesRef -> Prolog.Proof -> IO Prolog.PCheck
checkProof rlsref p = do
  rules'   <- readIORef rlsref
  doCheck  <- readStore storeDoCheckId
  return $ if doCheck
             then Prolog.checkProof rules' p
             else Prolog.dummyProof p

doSubst :: RulesRef -> Prolog.Proof -> EventHandler
doSubst rlsref p _ = do
  sub <- jQuery "#txtSubstSub" >>= valString
  for <- jQuery "#txtSubstFor" >>= valString
  case tryParseTerm sub of
    Nothing  ->  return False
    Just t   ->  let  newP = NP.subst (NP.Env $ fromList [(for, t)]) p
                 in   replaceRuleTree rlsref newP >> return True

clearClasses :: JQuery -> IO ()
clearClasses = flip removeClass' "blueField yellowField redField whiteField greenField"

markInvalidTerm :: JQuery -> IO ()
markInvalidTerm jq = clearClasses jq >> addClass jq "blueField"

markClear :: JQuery -> IO ()
markClear jq = clearClasses jq >> addClass jq "whiteField"

deleteRule :: RulesRef -> JQuery -> Int -> EventHandler
deleteRule rlsref jq i _ = do
  deleteRuleFromStore i
  rules <- readRulesFromStore
  writeIORef rlsref rules
  addRulesList rlsref
  return False

loadExampleData :: RulesRef -> EventHandler
loadExampleData rlsref _ = do 
  writeRulesInStore Prolog.exampleData
  addRulesList rlsref
  return False