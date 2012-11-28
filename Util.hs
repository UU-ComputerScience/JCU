module Util where

import           Language.UHC.JS.Assorted (alert)
import           Language.UHC.JS.ECMA.String   as JSString
import           Language.UHC.JS.JQuery.JQuery as JQ
import           Language.UHC.JS.Types


readMaybe :: (Read a) => String -> Maybe a
readMaybe s = case reads s of
              [(x, "")] -> Just x
              _         -> Nothing
              
              
noevent :: EventHandler
noevent _ = return False

isJust :: Maybe a -> Bool
isJust (Just _) = True
isJust _        = False

fromJSString :: JSString -> String
fromJSString = fromJS

void :: IO a -> IO ()
void io = io >> return ()

----
--   Helpers
----
showError = alert
showInfo  = alert


