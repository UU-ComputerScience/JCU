module Main where

import Language.UHC.JS.Assorted (alert)
import Language.UHC.JS.Types (fromJS)

import Language.UHC.JS.ECMA.String (JSString)

foreign import js "window.location.href"
  windowHref :: JSString

main :: IO ()
main = alert (fromJS windowHref)
