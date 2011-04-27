{-|

  This is a support module meant to back all session back-end implementations.

  It gives us an encrypted and timestamped cookie that can store an arbitrary
  serializable payload. For security, it will:
  
    * Encrypt its payload together with a timestamp.  
    
    * Check the timestamp for session expiration everytime you read from the
    cookie. This will limit intercept-and-replay attacks by disallowing cookies
    older than the timeout threshold. 

-}

module Snap.Extension.Session.SecureCookie where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans

import Data.ByteString (ByteString)
import Data.Time
import Data.Time.Clock.POSIX

import Data.Serialize
import Web.ClientSession

import Snap.Types



------------------------------------------------------------------------------
-- | Serialize UTCTime
instance Serialize UTCTime where
    put t = put (round (utcTimeToPOSIXSeconds t) :: Integer)
    get   = posixSecondsToUTCTime . fromInteger <$> get


------------------------------------------------------------------------------
-- | Arbitrary payload with timestamp.
type SecureCookie t = (UTCTime, t)


------------------------------------------------------------------------------
-- Get the payload back
getSecureCookie :: (MonadSnap m, Serialize t) 
                => ByteString       -- ^ Cookie name
                -> Key              -- ^ Encryption key
                -> Maybe Int        -- ^ Timeout in seconds
                -> m (Maybe t)
getSecureCookie name key timeout = do
    rqCookie <- getCookie name
    rspCookie <- getResponseCookie name `fmap` getResponse
    let ck = rspCookie `mplus` rqCookie
    let val = fmap cookieValue ck >>= decrypt key >>= return . decode
    let val' = val >>= either (const Nothing) Just 
    case val' of
      Nothing -> return Nothing
      Just (ts, t) -> do
        to <- checkTimeout timeout ts
        return $ case to of
          True -> Nothing
          False -> Just t


------------------------------------------------------------------------------
-- | Inject the payload
setSecureCookie :: (MonadSnap m, Serialize t) 
                => ByteString       -- ^ Cookie name
                -> Key              -- ^ Encryption key 
                -> t                -- ^ Serializable payload
                -> Maybe Int        -- ^ Max age in seconds
                -> m ()
setSecureCookie name key val to = do
    t <- liftIO getCurrentTime
    let expire = to >>= Just . flip addUTCTime t . fromIntegral
    let val' = encrypt key . encode $ (t, val)
    let nc = Cookie name val' expire Nothing (Just "/")
    modifyResponse $ addResponseCookie nc


------------------------------------------------------------------------------
-- | Validate session against timeout policy.
--
-- * If timeout is set to 'Nothing', never trigger a time-out.
-- * Othwerwise, do a regular time-out check based on current time and given
-- timestamp.
checkTimeout :: (MonadSnap m) => Maybe Int -> UTCTime -> m Bool
checkTimeout Nothing _ = return False
checkTimeout (Just x) t0 = 
  let x' = fromIntegral x
  in do
      t1 <- liftIO getCurrentTime
      return $ t1 > addUTCTime x' t0
