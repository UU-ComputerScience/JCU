module Data.LocalStorage 
  ( getLocalStorage
  , setLocalStorage
  , removeLocalStorage
  , clearLocalStorage
  , lengthLocalStorage
  , keyLocalStorage
  , StorageEvent(..)
  ) where

import Language.UHC.JS.Types
  
import Language.UHC.JS.ECMA.String as JSString
  
data StorageEvent a = StorageEvent { key      :: String
                                   , oldValue :: a
                                   , newValue :: a
                                   , url      :: String }

foreign import js "localStorage.getItem(%1)"
  _getLocalStorage :: JSString -> IO a
    
getLocalStorage :: Read a => String -> IO a
getLocalStorage = fmap read . _getLocalStorage . toJS

foreign import js "localStorage.setItem(%1, %2)"
  _setLocalStorage :: JSString -> a -> IO ()

setLocalStorage :: Show a => String -> a -> IO ()
setLocalStorage key = _setLocalStorage (toJS key) . (toJS :: String -> JSString) . show

foreign import js "localStorage.removeItem(%1)"
  _removeLocalStorage :: JSString -> IO ()
  
removeLocalStorage :: String -> IO ()
removeLocalStorage = _removeLocalStorage . toJS

foreign import js "localStorage.clear()"
  clearLocalStorage :: IO ()
  
foreign import js "localStorage.length"
  lengthLocalStorage :: IO Int

foreign import js "localStorage.key(%1)"
  _keyLocalStorage :: Int -> IO JSString

keyLocalStorage :: Int -> IO String
keyLocalStorage = fmap fromJS . _keyLocalStorage
