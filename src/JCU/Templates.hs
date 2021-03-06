{-# LANGUAGE OverloadedStrings #-}

module JCU.Templates where

import            Control.Monad
import            Control.Monad.Reader
import            Data.Text (Text)
import            Text.Blaze.Html5 (Html, (!))
import qualified  Text.Blaze.Html5 as H
import qualified  Text.Blaze.Html5.Attributes as A
import            Text.Digestive.Blaze.Html5
import qualified  Text.Digestive.View as V


-------------------------------------------------------------------------------
-- View

data AuthState = AuthState {
     loggedInST :: Bool
  ,  emailST    :: Text
}


-- replaces the layout.tpl file
template :: Reader AuthState Html -> Reader AuthState Html
template content = do
  h <- header
  d <- doc content
  return $ H.docTypeHtml (h >> d)

doc :: Reader AuthState Html -> Reader AuthState Html
doc c = do
  content   <- c
  loggedIn  <- asks loggedInST
  return $
    H.body $
      H.div ! A.id "doc" $ do
        H.div ! A.id "hd" $ do
          H.span ! A.id "header" $ do
            H.img ! A.src jcuLogo64 ! A.alt "JCU logo"
            H.toHtml ("Module Functional and Logical Programming" :: Text)
          if loggedIn
            then  H.span ! A.id "logout" $ do
                    H.a ! A.href "/" $ H.toHtml ("Proof tree" :: Text)
                    H.toHtml (" | " :: Text)
                    H.a ! A.href "/interpreter" $ H.toHtml ("Interpreter" :: Text)
                    H.toHtml (" | " :: Text)
                    H.a ! A.href "/logout" $ H.toHtml ("Logout" :: Text)
            else  H.span ! A.id "logout" $ H.a ! A.href "/signup" $
                   H.toHtml ("Create an account" :: Text)
        H.div ! A.id "bd" $ content
        H.div ! A.id "ft" $
          H.img ! A.src "/img/uulogo.png" ! A.id "uulogo" ! A.alt "UU Logo"
  where
    jcuLogo64  = "img/jculogo-64.png"

header :: Reader AuthState Html
header = do
  loggedIn <- asks loggedInST
  return $ H.head $ do
    H.title "JCU: Module Functioneel en Logische Programmeren"
    H.link ! A.rel "stylesheet" ! A.type_ "text/css" ! A.href cssBase
    H.link ! A.rel "stylesheet" ! A.type_ "text/css" ! A.href cssFonts
    H.link ! A.rel "stylesheet" ! A.type_ "text/css" ! A.href cssGrids
    H.link ! A.rel "stylesheet" ! A.type_ "text/css" ! A.media "screen" ! A.href mainCss
    H.link ! A.rel "icon" ! A.type_ "image/png" ! A.href jcuLogo16
    when loggedIn $ do
      -- H.script ! A.src "brunch/build/web/js/app.js" $ return ()
      H.script ! A.src "brunch/src/vendor/jquery-1.6.2.js" $ return ()
      H.script ! A.src "brunch/src/vendor/jquery-ui-1.8.16.custom.min.js" $ return ()
      H.script ! A.src "hjs/ajaxq.js" $ return ()
      H.script ! A.src "hjs/jcu.js" $ return ()
      -- H.script $ H.toHtml ("require('main');" :: Text)
  where
    cssBase    = "http://yui.yahooapis.com/3.3.0/build/cssbase/base-min.css"
    cssFonts   = "http://yui.yahooapis.com/3.3.0/build/cssfonts/fonts-min.css"
    cssGrids   = "http://yui.yahooapis.com/3.3.0/build/cssgrids/grids-min.css"
    mainCss    = "brunch/build/web/css/main.css"
    jcuLogo16  = "img/jculogo-16.png"


-- Replaces the signup.tpl file
signupHTML :: Monad m => Bool -> V.View Html -> m Html
signupHTML exists view = return $
  H.div ! A.id "home-view" $ do
    H.h1 $ H.toHtml ("Please sign up" :: Text)
    when exists $ H.h2 "Username is already taken"
    form view "/signup" $ do
      registrationFormView view
      H.div $ inputSubmit "Sign up!"

registrationFormView :: V.View v -> Html
registrationFormView view = do
  H.div $ do
    label "email1" view "Email address: "
    inputText "email1" view
  H.div $ do
    label "email2" view "Email address (confirmation): "
    inputText "email2" view
  H.div $ do
    label "password1" view "Password: "
    inputPassword "password1" view
  H.div $ do
    label "password2" view "Password (confirmation): "
    inputPassword "password2" view

-- Replaces the login.tpl file
{-loginHTML :: Bool -> FormHtml (HtmlM a) -> Reader AuthState Html-}
loginHTML :: Monad m => Bool -> V.View Html -> m Html
loginHTML loginFailed view = return $
  H.div ! A.id "home-view" $ do
    H.h1 $ H.toHtml ("Please log in" :: Text)
    when loginFailed $ H.h2 "Incorrect login credentials"
    form view "/login" $ do
      loginFormView view
      H.div $ inputSubmit "Log in"

loginFormView :: V.View Html -> Html
loginFormView view = do
  H.div $ do
    label "email" view "Email address: "
    inputText "email" view
  H.div $ do
    label "password" view "Password: "
    inputPassword "password" view
  H.div $ do
    label "remember" view "Remember me?"
    inputCheckbox "remember" view

mainHTML :: Html -> Reader AuthState Html
mainHTML left = return $ do
  H.div ! A.id "home-view" $
    H.div ! A.class_ "yui3-g" $ do
      H.div ! A.class_ "yui3-u-1-2" ! A.id "mainLeft" $
        H.div ! A.class_ "content" $ left
      H.div ! A.class_ "yui3-u-1-2" ! A.id "mainRight" $ do
        H.div ! A.class_ "content" $ do
          H.h2 (H.toHtml ("Stored Rules" :: Text))
          H.p (H.toHtml ("Drag a rule form the list below to a field containing a term in the tree on the left." :: Text))
          H.div ! A.id "rules-list-div" $ return ()
          H.div ! A.id "divListAdd" $ do
            H.input ! A.type_ "text" ! A.id "txtAddRule"
            H.input ! A.type_ "button" ! A.id "btnAddRule" ! A.value "Add"

interpreterHTML :: Reader AuthState Html
interpreterHTML = mainHTML $ do
  H.h2 $ H.toHtml ("Interpreter" :: Text)
  H.input ! A.type_ "text" ! A.id "query"
  H.input ! A.type_ "button" ! A.id "submitquery" ! A.value "Submit Query"
  H.div ! A.id "output" $
    H.toHtml ("Please enter a query" :: Text)

index :: Reader AuthState Html
index = mainHTML $ do
  H.h2 "Proof Tree"
  H.div ! A.id "proof-tree-div" ! A.class_ "noClue" $
    H.div $ H.toHtml ("JCU: Wiskunde D. The application is either loading, or something went wrong." :: Text)
  H.div ! A.id "subst" $ do
    H.toHtml ("Substitute " :: Text)
    H.input ! A.type_ "text" ! A.id "txtSubstSub" ! A.style "width: 50px"
    H.toHtml (" for " :: Text)
    H.input ! A.type_ "text" ! A.id "txtSubstFor" ! A.style "width: 50px"
    H.input ! A.type_ "button" ! A.id "btnSubst" ! A.value "Substitute"
    H.toHtml (" (e.g. substitute bea for X0)" :: Text)
  H.input ! A.type_ "hidden" ! A.id "storeDoChecking" ! A.value "False"
  H.input ! A.type_ "button" ! A.id "btnCheck" ! A.value "Check Proof"
  H.input ! A.type_ "button" ! A.id "btnReset" ! A.value "Reset Tree"
  H.h3 $ H.toHtml ("The Goal" :: Text)
  H.p ! A.class_ "lhsText" $
    H.toHtml ("With this exercise you get to do what a Prolog interpreter usually does for you: unifying terms and rules and find substitutions for variables. To start, you enter a Prolog query in the textfield above. Your job then is to proof that there exist solutions for this query. This is done by dragging rules from the right-hand side of the screen onto your query. This will unify the two and produce new terms to proof. When the bottom text fields all contain facts, your work is done! If you do not have rules and facts yet, you can load the examples below and/or add new ones yourself using the text field on the right-hand side of the screen. Good luck!" :: Text)
  H.h3 $ H.toHtml ("Color coding help" :: Text)
  H.ul ! A.id "color-coding-list" $ do
    H.li $ do
      H.div ! A.class_ "box redField" $ return ()
      H.toHtml ("Incorrect rule application" :: Text)
    H.li $ do
       H.div ! A.class_ "box yellowField" $ return ()
       H.toHtml ("Incomplete proof" :: Text)
    H.li $ do
       H.div ! A.class_ "box greenField" $ return ()
       H.toHtml ("Correct rule" :: Text)
    H.li $ do
       H.div ! A.class_ "box blueField" $ return ()
       H.toHtml ("Syntax error" :: Text)
  H.h3 $ H.toHtml ("Example data" :: Text)
  H.p ! A.class_ "lhsText" $ do
    H.toHtml ("Example data containing the Dutch royal family, the list structure and lookup, and the natural numbers (as discussed in the JCU lecture notes) can be loaded by " :: Text)
    H.a ! A.href "/load-example" $ H.toHtml ("clicking this link" :: Text)
    H.toHtml (". Beware that this will replace all your existing rules!" :: Text)
