module Array where

import Language.UHC.JS.Primitives

data JSArrayPtr a
type JSArray a = JSPtr (JSArrayPtr a)

