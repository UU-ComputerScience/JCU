module Debug (trace, consoleLog) where

import System.IO.Unsafe (unsafePerformIO)

import Language.UHC.JS.ECMA.String as JSString
import Language.UHC.JS.Types as JSString

foreign import js "console.log(%1)"
  _consoleLog :: JSString -> IO ()

consoleLog :: String -> IO ()
consoleLog = _consoleLog . toJS

trace :: String -> a -> a
trace str a = unsafePerformIO $ do (_consoleLog . toJS) str
                                   return a