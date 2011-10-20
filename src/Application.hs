{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleContexts #-}


module Application where

import            Control.Applicative
import            Control.Monad
import            Control.Monad.Reader
import            Control.Monad.State
import            Data.Aeson as AE
import            Data.Aeson.Parser as AE
import qualified  Data.Attoparsec.Lazy as AP
import qualified  Data.ByteString.Lazy.Char8 as LBS
import qualified  Data.ByteString.Char8 as BS
import            Data.Char
import            Data.Lens.Template
import qualified  Data.List as DL
import            Data.Map (Map)
import qualified  Data.Map as DM
import            Data.Maybe
import            Data.Text (Text)
import qualified  Data.Text as DT
import qualified  Data.Text.Encoding as DT
import            Data.Tree (Tree(..))
import            Database.HDBC.Sqlite3
import            JCU.Prolog
import            JCU.Templates
import            JCU.Types
import            Language.Prolog.NanoProlog.NanoProlog
import            Snap.Core
import            Snap.Snaplet
import            Snap.Snaplet.Auth
import            Snap.Snaplet.Auth.Backends.Hdbc
import            Snap.Snaplet.Hdbc
import            Snap.Snaplet.Session
import            Snap.Snaplet.Session.Backends.CookieSession
import            Snap.Util.FileServe
import            Text.Blaze
import qualified  Text.Blaze.Html5 as H
import qualified  Text.Blaze.Html5.Attributes as A
import            Text.Blaze.Internal (HtmlM(..))
import            Text.Blaze.Renderer.Utf8 (renderHtml)
import            Text.Digestive
import            Text.Digestive.Blaze.Html5
import            Text.Digestive.Forms.Snap
import qualified  Text.Email.Validate as E
import            Text.ParserCombinators.UU.BasicInstances (Parser())


data App = App
  {  _authLens  :: Snaplet (AuthManager App)
  ,  _sessLens  :: Snaplet SessionManager
  ,  _dbLens    :: Snaplet (HdbcSnaplet Connection)
  }

makeLens ''App

type AppHandler = Handler App App

instance HasHdbc AppHandler Connection where
  getPool = with dbLens $ gets hdbcPool

jcu :: SnapletInit App App
jcu = makeSnaplet "jcu" "Prolog proof tree practice application" Nothing $ do
  addRoutes  [  ("/",           siteIndex)
             ,  ("/forbidden",  forbiddenH)
             ,  ("/login",   loginH)
             ,  ("/logout",  logoutH)
             ,  ("/signup",  signupH)
             ,  ("/rules/stored",  method GET   readStoredRulesH)
             ,  ("/rules/stored",  method POST  addStoredRuleH)
             ,  ("/rules/stored/:id",  method DELETE  deleteStoredRuleH)
             ,  ("/proof/check",   method POST  checkProofH)
             ,  ("/rules/unify",   method POST  unifyH)
             ,  ("/load-example",  method GET loadExampleH)
             ,  ("/check-syntax/:type",  method POST checkSyntaxH)
             ,  ("/subst/:sub/:for",     method POST substH)
             ,  ("", serveDirectory "resources/static")
             ]
  _sesslens'  <- nestSnaplet "session" sessLens $ initCookieSessionManager
                   "config/site_key.txt" "_session" Nothing
  let sqli = connectSqlite3 "resources/jcu.db"
  _dblens'    <- nestSnaplet "hdbc" dbLens $ hdbcInit sqli
  _authlens'  <- nestSnaplet "auth" authLens $ initHdbcAuthManager
                   defAuthSettings sessLens sqli defAuthTable defQueries
  return  $ App _authlens' _sesslens' _dblens'


restrict :: AppHandler b -> AppHandler b -> AppHandler b
restrict failH succH = do
  with sessLens touchSession
  authed <- with authLens $ isLoggedIn
  if authed
    then succH
    else failH

loginRedir :: AppHandler ()
loginRedir = redirect "/login"

forbiddenH :: AppHandler a
forbiddenH = do
  modifyResponse $ setResponseStatus 403 "Forbidden"
  writeBS "403 forbidden"
  r <- getResponse
  finishWith r

------------------------------------------------------------------------------
-- | Renders the front page of the sample site.
--
-- The 'ifTop' is required to limit this to the top of a route.
-- Otherwise, the way the route table is currently set up, this action
-- would be given every request.
siteIndex :: AppHandler ()
siteIndex = ifTop $ restrict loginRedir $ (blaze $ template index)

-- TODO: Remove
{- loginH :: AppHandler ()-}
{- loginH = loginHandler "password" (Just "remember") failedLogin redirHome-}
  {- where failedLogin _ = blaze $ template False login-}

loginH :: AppHandler ()
loginH = withSession sessLens $ do
  loggedIn <- with authLens isLoggedIn
  when loggedIn $ redirect "/"
  res <- eitherSnapForm registrationForm "registration-form"
  case res of
    Left form' -> do
      didFail <- with sessLens $ do
        failed <- getFromSession "login-failed"
        deleteFromSession "login-failed"
        commitSession
        return failed
      blaze $ template $ loginHTML (isJust didFail) form'
    Right (FormUser e p r) -> do
      loginRes <- with authLens $ loginByUsername (DT.encodeUtf8 e) (ClearText $ DT.encodeUtf8 p) r
      case loginRes of
        Left _   ->  do  with sessLens $ do
                           setInSession "login-failed" "1"
                           commitSession
                         redirect "/login"
        Right _  ->  redirect "/"

logoutH :: AppHandler ()
logoutH = do
  with authLens logout
  redirect "/"


------------------------------------------------------------------------------
-- | Renders the login page

redirIfLogin :: AppHandler () -> AppHandler ()
redirIfLogin = flip restrict redirHome

redirHome :: AppHandler ()
redirHome = redirect "/"

{- additionalUserFields :: User -> Document-}
{- additionalUserFields usr = [ "storedRules" =: storedRules usr ]-}


signupH :: AppHandler ()
signupH = do
  loggedIn <- with authLens isLoggedIn
  when loggedIn $ redirect "/"
  res <- eitherSnapForm registrationForm "registration-form"
  case res of
    Left form' ->
      blaze $ template (signupHTML form')
    Right (FormUser u p _) -> do
      _ <- with authLens $ createUser u (DT.encodeUtf8 p) -- TODO Could throw a DuplicateLogin!
      redirect "/"


------------------------------------------------------------------------------
-- | Functions for handling reading and saving per-person rules

readStoredRulesH :: AppHandler ()
readStoredRulesH = restrict forbiddenH $ do
  rules <- getRawRules
  modifyResponse $ setContentType "application/json"
  writeLBS $ encode rules

deleteStoredRuleH :: AppHandler ()
deleteStoredRuleH = restrict forbiddenH $ do
  rule  <- getParam "id"
  rls   <- getRawRules
  case rule of
    Nothing  -> return ()
    Just x   -> putRawRules (DL.delete x rls)

addStoredRuleH :: AppHandler ()
addStoredRuleH = restrict forbiddenH $ do
  rqrl  <- getRequestBody
  rls   <- getRawRules
  case mkRule rqrl of
    Left   err   -> error500H err
    Right  rule  -> putRawRules (rls ++ [BS.pack . show $ rule])

loadExampleH :: AppHandler ()
loadExampleH = restrict forbiddenH $ do
  putRules exampleData
  redirHome

putRules :: [Rule] -> AppHandler ()
putRules = putRawRules . map (BS.pack . show)

putRawRules :: [BS.ByteString] -> AppHandler ()
putRawRules rls = restrict forbiddenH $ do
  cau  <- with authLens $ currentUser
  return undefined
  {- doc  <- rulesToDoc rls (snd . fromJust $ cau)-}
  {- tbl  <- fmap u authUserTable-}
  {- withDB' $ save tbl doc-}


{- rulesToDoc :: (MonadMongoDB m) => [ByteString] -> Document -> m Document-}
{- rulesToDoc rls d = do-}
{-   let tsc = ["storedRules" =: rls]-}
{-   return $ tsc `MDB.merge` d-}

-- TODO: Abstract over the uid thing.. also refactor it; it's ugly
getRuleList :: AppHandler [Rule]
getRuleList = restrict forbiddenH $ do
  cau <- with authLens $ currentUser
  uid <- case cau of
           Nothing -> redirect "/"
           Just x  ->  case userId x of
                         Nothing -> redirect "/"
                         Just y  -> return y
  rawRules <- getStoredRules uid
  -- TODO: Error handling
  return $ map (fst . startParse pRule . BS.unpack) rawRules

getRawRules :: AppHandler [BS.ByteString]
getRawRules = restrict forbiddenH $ do
  cau <- with authLens $ currentUser
  uid <- case cau of
           Nothing -> redirect "/"
           Just x  ->  case userId x of
                         Nothing -> redirect "/"
                         Just y  -> return y
  getStoredRules uid


-- | Check the proof from the client. Since the checking could potentially
-- shoot into an inifinite recursion, a timeout is in place.
checkProofH :: AppHandler ()
checkProofH = restrict forbiddenH $ do
  setTimeout 15
  body <- getRequestBody
  case mkProof body of
    Left   err    -> error500H err
    Right  proof  -> do  rules <- getRuleList
                         let prf = checkProof rules  proof
                         writeLBS $ encode prf

unifyH :: AppHandler ()
unifyH = restrict forbiddenH $ do
  setTimeout 10
  body <- getRequestBody
  case mkDropReq body of
    Left   err                   -> error500H err
    Right  (DropReq prf lvl rl)  -> writeLBS $ encode (dropUnify prf lvl rl)

error500H :: BS.ByteString -> AppHandler a
error500H msg = do
  modifyResponse $ setResponseStatus 500 "Internal server error"
  writeBS $ BS.append (BS.pack "500 internal server error: ") msg
  r <- getResponse
  finishWith r

checkSyntaxH :: AppHandler ()
checkSyntaxH = restrict forbiddenH $ do
  ptype  <- getParam "type"
  body   <- getRequestBody
  let ret = parseCheck ptype body
  writeLBS $ encode ret

substH :: AppHandler ()
substH = restrict forbiddenH $ do
  body  <- getRequestBody
  sub   <- getParam "sub"
  for   <- getParam "for"
  case mkProof body of
    Left   err    ->  error500H err
    Right  proof  ->  let  unjust  = BS.unpack . fromJust
                           stree   = subst (Env $ DM.fromList [(unjust for, Var $ unjust sub)]) proof
                      in   writeLBS $ encode stree



blaze :: Reader AuthState Html -> AppHandler ()
blaze htmlRdr = do
  modifyResponse $ addHeader "Content-Type" "text/html; charset=UTF-8"
  li <- with authLens isLoggedIn
  email <- with authLens $ undefined -- TODO: Get user email address
  let html = runReader htmlRdr (AuthState li email)
  writeLBS $ renderHtml html

-------------------------------------------------------------------------------
-- Forms

data FormUser = FormUser
  {  email     :: Text
  ,  password  :: Text
  ,  remember  :: Bool }
  deriving Show

isEmail :: Monad m => Validator m Html Text
isEmail = check "Invalid email address" (E.isValid . DT.unpack)

longPwd :: Monad m => Validator m Html Text
longPwd  =  check "Password needs to be at least six characters long"
         $  \xs -> DT.length xs >= 6

isNonEmpty :: Monad m => Validator m Html Text
isNonEmpty = check "Field must not be empty" $ not . DT.null

loginForm :: Form AppHandler SnapInput Html BlazeFormHtml FormUser
loginForm = FormUser
  <$>  label  "Email address: "
       ++>  inputText Nothing `validate` isEmail
       <++  errors
  <*>  label  "Password: "
       ++>  inputPassword `validate` longPwd
       <++  errors
  <*>  label  "Remember me?"
       ++>  inputCheckBox True

-- TODO: Check if the email addresses are the same
-- TODO: Also send an email after registration
registrationForm :: Form AppHandler SnapInput Html BlazeFormHtml FormUser
registrationForm = (\e _ p _ -> FormUser e p False)
  <$>  label  "Email address: "
       ++>  inputText Nothing `validate` isEmail
       <++  errors
  <*>  label  "Email address (confirmation): "
       ++>  inputText Nothing `validate` isEmail
       <++  errors
  <*>  label  "Password: "
       ++>  inputPassword `validate` longPwd
       <++  errors
  <*>  label  "Password (confirmation): "
       ++>  inputPassword `validate` longPwd
       <++  errors


-------------------------------------------------------------------------------
-- Authentication and authorization


-------------------------------------------------------------------------------
-- Database interaction

voidM :: Monad m => m a -> m ()
voidM m = do
  _ <- m
  return ()

insertRule :: HasHdbc m c => UserId -> Rule -> m ()
insertRule uid rl = voidM $
  query'  "INSERT INTRO rules (uid, rule) VALUES (?, ?)"
          [toSql $ unUid uid, toSql $ show rl]

deleteRule :: HasHdbc m c => Int -> m ()
deleteRule rid = voidM $
  query' "DELETE FROM rules WHERE rid = ?" [toSql rid]

getStoredRules :: HasHdbc m c => UserId -> m [BS.ByteString]
getStoredRules uid = do
  rs <- query "SELECT * FROM rules WHERE uid = ?" [toSql uid]
  return $ mkRules rs
  where mkRules = undefined

