module Data.LocalStorage 
  ( getLocalStorage
  , setLocalStorage
  , removeLocalStorage
  , clearLocalStorage
  , lengthLocalStorage
  , keyLocalStorage
  , addStorageListener
  , StorageEvent(..)
  ) where

import Language.UHC.JS.Primitives
import Language.UHC.JS.Types

  
import Language.UHC.JS.ECMA.String as JSString

data JStorageEventPtr
type JStorageEvent = JSPtr JStorageEventPtr
  
data StorageEvent a = StorageEvent { key      :: String
                                   , oldValue :: a
                                   , newValue :: a
                                   , url      :: String }

foreign import js "localStorage.getItem(%1)"
  _getLocalStorage :: JSString -> IO a
    
getLocalStorage :: Read a => String -> IO a
getLocalStorage = fmap (read . (fromJS :: JSString -> String)) . _getLocalStorage . toJS

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

foreign import js "window.addEventListener('storage', %1, false)"
  _addStorageListener :: JSFunPtr (JStorageEvent -> IO ()) -> IO ()

foreign import js "wrapper"
  mkJStorageEventHandler :: (JStorageEvent -> IO ()) -> IO (JSFunPtr (JStorageEvent -> IO ()))
  
addStorageListener :: Read a => (StorageEvent a -> IO ()) -> IO ()
addStorageListener f =
  let g :: JStorageEvent -> IO ()
      g obj = do storageevent <- convert obj
                 f storageevent
  in do eh <- mkJStorageEventHandler g
        _addStorageListener eh        
  where
    convert :: Read a => JStorageEvent -> IO (StorageEvent a)
    convert obj = do key <- fmap (fromJS :: JSString -> String)          $ getAttr "key" obj
                     old <- fmap (read . (fromJS :: JSString -> String)) $ getAttr "old" obj
                     new <- fmap (read . (fromJS :: JSString -> String)) $ getAttr "new" obj
                     url <- fmap (fromJS :: JSString -> String)          $ getAttr "url" obj
                     return $ StorageEvent key old new url