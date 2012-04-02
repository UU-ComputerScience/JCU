module JCU where

import Control.Monad as CM (liftM, foldM, when)

import Data.Array (elems)
import Data.IORef
import Data.List as DL
import Data.Map   (fromList)
import Data.Maybe (fromJust)
import Data.Tree as T

import Language.UHC.JScript.Prelude
import Language.UHC.JScript.Types -- (JS, toJS, fromJS, FromJS)
import Language.UHC.JScript.Primitives
import Language.UHC.JScript.JQuery.JQuery
import Language.UHC.JScript.W3C.HTML5 as HTML5

import Language.UHC.JScript.ECMA.Bool
import Language.UHC.JScript.ECMA.String as JSString


import Language.UHC.JScript.Assorted (alert , _alert)

import Language.UHC.JScript.JQuery.Ajax as Ajax
import qualified Language.UHC.JScript.JQuery.AjaxQueue as AQ
import Language.UHC.JScript.JQuery.Draggable
import Language.UHC.JScript.JQuery.Droppable

import Language.Prolog.NanoProlog.NanoProlog
import Language.Prolog.NanoProlog.ParserUUTC

import Language.UHC.JScript.JQuery.Deferred 

{-import Language.UHC.JScript.WebWorker -}

----
--  App
----

import Prolog

import Language.UHC.JScript.ECMA.Array as ECMAArray (JSArray, jsArrayToArray)

import Array

import Templates
import Models


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
ajaxQ  ::  (JS r, JS v) => AjaxRequestType -> String -> v -> AjaxCallback r
       ->  AjaxCallback r -> IO ()
ajaxQ rt url = AQ.ajaxQ "jcu_app"
  AjaxOptions  {  ao_url         = url
               ,  ao_requestType = rt
               ,  ao_contentType = "application/json"
               ,  ao_dataType    = "json"
               }

-- | Update an existing input field that is used to store `global' variables
--   Not entirely best practice. This should perhaps be modelled in a State
--   monad.
updateStore :: (Read a, Show a) => Selector -> (a -> a) -> IO ()
updateStore sel updateF = do
  store <- jQuery sel
  val   <- fmap read (valString store)
  setValString store (show $ updateF val)

-- | Read the contents of the store
readStore :: (Read a) => Selector -> IO a
readStore sel = fmap read (jQuery storeDoCheckId >>= valString)

----
--   Application
----
main :: IO ()
main = do
  path <- pathName
  init <- wrapIO $ if "interpreter" `isInfixOf` path
                     then  initInterpreter
                     else  initProofTree
  onDocumentReady init

initInterpreter :: IO ()
initInterpreter = do
  obj <- mkAnonObj
  rlsref <- newIORef []
  ajaxQ GET "/rules/stored" obj (addRules rlsref) noop
  registerEvents  [  ("#submitquery", Click   , submitQuery rlsref)
                  ,  ("#txtAddRule" , KeyPress, noevent)
                  ,  ("#txtAddRule" , Blur    , checkTermSyntax)
                  ,  ("#btnAddRule" , Click   , addRuleEvent) ]
  where  submitQuery rlsref _ = do
           qryFld <- jQuery "#query"
           qry <- valString qryFld
           case tryParseTerm qry of
             Nothing   -> markInvalidTerm qryFld
             Just goal -> do
               rules <- readIORef rlsref
               showProof (solve rules emptyEnv [("0",goal)])
           return True
         showProof result = do
           resFld <- jQuery "#output"
           let prRes = [  concatMap (\(prefix, pr) -> prefix ++ " " ++ show (subst env pr) ++ "<br />\n") (reverse proof)
                          ++ envToStr (show env) ++ "<br /><br />\n"
                       |  (proof, env) <- enumerateDepthFirst [] result ]
               envToStr env | DL.null env = ""
                            | otherwise   = "substitution: " ++ env
               txt = if null prRes
                       then "Could not find an answer to that query"
                       else DL.concat prRes
           setHTML resFld txt

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
  -- Proof tree
  addRuleTree
  -- Rules list
  obj <- mkAnonObj
  rlsref <- newIORef []
  ajaxQ GET "/rules/stored" obj (addRules rlsref) noop
  registerEvents  [  ("#btnCheck"  , Click   , toggleClue emptyProof)
                  ,  ("#btnAddRule", Click   , addRuleEvent)
                  ,  ("#btnReset"  , Click   , resetTree)
                  ,  ("#txtAddRule", KeyPress, clr)
                  ,  ("#txtAddRule", Blur    , checkTermSyntax) ]
  where  resetTree _ = do -- Do not forget to add the class that hides the colours
           jQuery "#proof-tree-div" >>= flip addClass "noClue"
           -- Always store False in the store.
           updateStore storeDoCheckId (const False)
           replaceRuleTree emptyProof
           return True
         clr _ = jQuery "#txtAddRule" >>= clearClasses >> return True

-- Toggles checking of the proof and showing the results
toggleClue :: Proof -> EventHandler
toggleClue p _ = do
  toggleClassString "#proof-tree-div" "noClue"
  updateStore storeDoCheckId not
  replaceRuleTree p
  return True

emptyProof :: Proof
emptyProof = T.Node (Var "") []

addRuleTree :: IO ()
addRuleTree = do
  let status = T.Node Correct []
  ruleTreeDiv <- jQuery "#proof-tree-div"
  ruleTreeUL  <- buildRuleUl emptyProof status
  append ruleTreeDiv ruleTreeUL

-- | Builds up the rule tree  
buildRuleUl :: Proof -> PCheck -> IO JQuery
buildRuleUl node status =
  do topUL <- jQuery "<ul id=\"proof-tree-view\" class=\"tree\"/>"
     restUL <- build' [0] node (node, status) False
     append topUL restUL
     inputField <- findSelector restUL "input"
     eh  <- mkJThisEventHandler fCheck
     eh' <- wrappedJQueryEvent eh
     _bind inputField (toJS "blur") eh'
     return topUL
  where
    f :: [Int] -> Proof -> (JQuery, Int) -> (Proof, PCheck) -> IO (JQuery, Int)
    f lvl wp (jq, n) (node, status) = do
      li' <- build' (lvl ++ [n]) wp (node,status) True
      append jq li'
      return (jq, n + 1)
    onDrop :: Proof -> [Int] -> Proof -> UIThisEventHandler
    onDrop wp lvl node this _ ui = do
      elemVal <- findSelector this "input[type='text']:first" >>= valString
      jsRuleText <- (getAttr "draggable" ui >>= getAttr "context" >>= getAttr "innerText") :: IO JSString
      let ruleText = fromJS jsRuleText :: String
      if null elemVal
        then  showError "There needs to be a term in the text field!" 
        else  case tryParseRule ruleText of
                Nothing  -> showError "This should not happen. Dropping an invalid rule here."
                Just t   -> case dropUnify wp lvl t of
                              DropRes False  _  -> showError "I could not unify this."
                              DropRes True   p  -> replaceRuleTree p
      return True

    build' :: [Int] -> Proof -> (Proof, PCheck) -> Bool -> IO JQuery
    build' lvl wp (n@(T.Node term chts), T.Node status chstat) disabled = do
      li <- jQuery "<li/>"
      appendString li $ proof_tree_item (show term) (intercalate "." $ map show lvl) disabled status
      dropzones <- findSelector li ".dropzone"
      drop      <- mkJUIThisEventHandler (onDrop wp lvl n) >>= wrappedJQueryUIEvent
      droppable dropzones $ Droppable (toJS "dropHover") drop
      startUl   <- jQuery "<ul/>"
      (res, _)  <- foldM (f lvl wp) (startUl, 1) (zip chts chstat)
      append li res
      return li

    fCheck :: ThisEventHandler
    fCheck this _ = do
      term <- valString this
      case tryParseTerm term of
        Just t  -> replaceRuleTree $ T.Node t []
        _       -> markInvalidTerm this
      return False

replaceRuleTree :: Proof -> IO ()
replaceRuleTree p = do
  status  <- checkProof p
  oldUL   <- jQuery ruleTreeId
  newUL   <- buildRuleUl p status
  -- Store new proof in the subst funct
  registerEvents  [  ("#btnCheck", Click, toggleClue p)
                  ,  ("#btnSubst", Click, doSubst p) ]
  -- Draw the new ruleTree
  replaceWith oldUL newUL
  CM.when (complete status) $
    showInfo "Congratulations! You have successfully completed your proof!"
  where  complete :: PCheck -> Bool
         complete (Node Correct [])  = True
         complete (Node Correct xs)  = all complete xs
         complete _                  = False


addRules :: IORef [Rule] -> AjaxCallback (JSArray JSRule)
addRules rlsref obj str obj2 = do
  -- slet rules  = (Data.List.map fromJS . elems . jsArrayToArray) obj
  rules_list_div <- jQuery "#rules-list-div"
  rules_list_ul  <- jQuery "<ul id=\"rules-list-view\"/>"
  append rules_list_div rules_list_ul
  f <- mkEachIterator (\idx e -> do
    (Rule id _ rule') <- jsRule2Rule e
    modifyIORef rlsref (addRuleRef rule')
    listItem <- createRuleLi (fromJS rule') id
    append rules_list_ul listItem
    return ())
  each' obj f
  onStart <- mkJUIEventHandler (\x y -> do focus <- jQuery ":focus"
                                           doBlur focus
                                           return False)
  draggables <- jQuery ".draggable"
  draggable draggables $ Draggable (toJS True) (toJS "document") (toJS True) 100 50 onStart
  return ()
  where addRuleRef rl lst = case tryParseRule (fromJS rl) of
                              Nothing  -> lst
                              Just r   -> r : lst

addRuleEvent :: EventHandler
addRuleEvent event = do
  rule  <- jQuery "#txtAddRule" >>= valJSString
  case tryParseRule (fromJS rule) of
    Nothing  ->  showError "Invalid rule, not adding to rule list."
    Just _   ->  let  str = foldl1 JSString.concat [toJS "{\"rule\":\"", rule, toJS "\"}"]
                 in   ajaxQ POST "/rules/stored" str (onSuccess (fromJS rule)) onFail
  return True
  where  onSuccess :: String -> AjaxCallback Int
         onSuccess r id _ _ = do ul   <- jQuery "ul#rules-list-view" 
                                 item <- createRuleLi r id 
                                 append ul item
         onFail _ _ _ = showError "faal"

createRuleLi :: String -> Int -> IO JQuery
createRuleLi rule id = do
  item <- jQuery $ "<li>" ++ rules_list_item rule ++ "</li>"
  delButton <- findSelector item "button.btnDeleteList"
  click delButton (deleteRule item id)
  return item

-- | Checks the current proof against the current list of rules. If the user
--   added rules in a different window or deleted them there those changes will
--   not be visible here.
checkProof :: Proof -> IO PCheck
checkProof p = do
  rules' <- getRules
  doCheck <- readStore storeDoCheckId
  return $ if doCheck
             then Prolog.checkProof rules' p
             else Prolog.dummyProof p

getRules :: IO [Rule]
getRules = do
  rules  <- jQuery ".rule-list-item" >>= jQueryToArray
  (mapM f . elems . jsArrayToArray) rules
  where f x = return . fromJust . tryParseRule . (fromJS :: JSString -> String) =<< getAttr "innerText" x

-- | This is how I think checkProof should look when using workers.
-- checkProof :: Proof -> (PCheck -> IO ()) -> IO ()
-- checkProof p cps = do rules  <- jQuery ".rule-list-item" >>= jQueryToArray
--                       rules' <- (mapM f . elems . jsArrayToArray) rules
--
--                       let messagecps = \ obj -> do res <- getAttr "data" obj :: IO PCheck
--                                                    cps res
--
--                       proofWorker <- newWorker "hjs/worker.js"
--                       setOnMessage proofWorker messagecps
--                       let l = Data.List.length $ show (p, rules')
--                       msg <- mkAnonObj
--                       p' <- mkObj p
--                       rules'' <- mkObj rules'
--                       setAttr "proof" p'      msg
--                       setAttr "rules" rules'  msg
--                       postMessage proofWorker msg
--  where f x =    getAttr "innerText" x
--            >>=  return . fromJust . tryParseRule . (fromJS :: JSString -> String)

-- foreign import js "_deepe_"
--   deepE :: a -> IO a

doSubst :: Proof -> EventHandler
doSubst p _ = do
  sub <- jQuery "#txtSubstSub" >>= valString
  for <- jQuery "#txtSubstFor" >>= valString
  case tryParseTerm sub of
    Nothing  ->  return False
    Just t   ->  let  newP = subst (Env $ fromList [(for, t)]) p
                 in   replaceRuleTree newP >> return True

clearClasses :: JQuery -> IO ()
clearClasses = flip removeClass' "blueField yellowField redField whiteField greenField"

markInvalidTerm :: JQuery -> IO ()
markInvalidTerm jq = clearClasses jq >> addClass jq "blueField"

markClear :: JQuery -> IO ()
markClear jq = clearClasses jq >> addClass jq "whiteField"

deleteRule :: JQuery -> Int -> EventHandler
deleteRule jq i _ = do
  ajaxQ DELETE ("/rules/stored/"++show i) i removeLi noop
  return False
  where  removeLi :: AjaxCallback ()
         removeLi _ _ _ = remove jq
