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

import Language.UHC.JS.JQuery.Ajax as Ajax
import qualified Language.UHC.JS.JQuery.AjaxQueue as AQ
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

-- | Wrapper function for making Ajax Requests with all types set to JSON as it
--   is the only type of request we will be making.
-- ajaxQ  ::  (JS r, JS v) => AjaxRequestType -> String -> v -> AjaxCallback r
--        ->  AjaxCallback r -> IO ()
-- ajaxQ rt url = AQ.ajaxQ "jcu_app"
--   AjaxOptions  {  ao_url         = url
--                ,  ao_requestType = rt
--                ,  ao_contentType = "application/json"
--                ,  ao_dataType    = "json"
--                }

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

  
-- | Adds the given Rule to the local datastore
addRuleToStore :: NP.Rule -> IO Int
addRuleToStore rule = return 0

-- | Deletes a given rule from the store (using the ID)
deleteRuleFromStore :: Int -> IO ()
deleteRuleFromStore id = return ()

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

showInterpRes :: AjaxCallback JSString
showInterpRes res str obj = do
  op <- jQuery "#output"
  _setHTML op res
  return ()

initProofTree :: IO ()
initProofTree = do -- Rendering
  l <- jQuery "#mainLeft"
  rules <- readRulesFromStore
  rlsref <- newIORef rules

  -- Proof tree
  addRuleTree rlsref
  -- Rules list
  -- addRules rlsref
  let defRules' = (read "[pa(alex, ama).,pa(alex, ale).,pa(alex, ari).,pa(claus, alex).,pa(claus, const).,pa(claus, friso).,ma(max, ama).,ma(max, ale).,ma(max, ari).,ma(bea, alex).,ma(bea, const).,ma(bea, friso).,ma(juul, bea).,ma(mien, juul).,ouder(X, Y):-pa(X, Y).,ouder(X, Y):-ma(X, Y).,kind(X, Y):-ouder(Y, X).,voor(X, Y):-ouder(X, Y).,voor(X, Y):-ouder(Z, Y), voor(X, Z).,oeps(X):-oeps(Y).,plus(zero, X, X).,plus(succ(X), Y, succ(Z)):-plus(X, Y, Z).,length(nil, zero).,length(X:XS, succ(Y)):-length(XS, Y).,oplossing(BORD):-rijen(BORD, XSS), juist(XSS), kolommen(BORD, YSS), juist(YSS), vierkanten(BORD, ZSS), juist(ZSS).,juist(nil).,juist(XS:XSS):-verschillend(XS), juist(XSS).,rijen(XSS, XSS).,kolommen(nil, nil:nil:nil:nil:nil).,kolommen(XS:XSS):-voegtoe(XS, YSS, ZSS), kolommen(XSS, YSS).,voegtoe(nil, nil, nil).,voegtoe(X:XS, YS:YSS, (X:YS):ZSS):-voegtoe(XS, YSS, ZSS).]") :: [NP.Rule]
  alert (show defRules')


  
  registerEvents  [  ("#btnCheck"  ,         Click   , toggleClue rlsref emptyProof)
                  ,  ("#btnAddRule",         Click   , addRuleEvent rlsref)
                  ,  ("#btnReset"  ,         Click   , resetTree rlsref)
                  ,  ("#btnLoadExampleData", Click   , loadExampleData)
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
  
  rules <- readIORef rlsref
  let f (idx, rule) = do listItem <- createRuleLi (show rule) idx
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
    Just r   ->  let  str = foldl1 JSString.concat [toJS "{\"rule\":\"", rule, toJS "\"}"]
                 in   do  modifyIORef rlsref (r :)
                          _ <- addRuleToStore r
                          return ()
  return True
  where  onSuccess :: String -> AjaxCallback Int
         onSuccess r id _ _ = do ul   <- jQuery "ul#rules-list-view"
                                 item <- createRuleLi r id
                                 append ul item

createRuleLi :: String -> Int -> IO JQuery
createRuleLi rule id = do
  item <- jQuery $ "<li>" ++ rules_list_item rule ++ "</li>"
  delButton <- findSelector item "button.btnDeleteList"
  click delButton (deleteRule item id)
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

deleteRule :: JQuery -> Int -> EventHandler
deleteRule jq i _ = do
  deleteRuleFromStore i
  remove jq
  return False

loadExampleData :: EventHandler
loadExampleData _ = do 
  setLocalStorage "rules" Prolog.exampleData
  return False