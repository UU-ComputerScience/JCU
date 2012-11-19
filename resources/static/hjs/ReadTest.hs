{-# LANGUAGE CPP #-}
module Main where

import           Data.List (find)

import qualified Language.Prolog.NanoProlog.NanoProlog as NP
import           Language.Prolog.NanoProlog.ParserUUTC

import           ParseLib.Abstract

#if __UHC__
import           Language.UHC.JS.Assorted (alert)
#else
alert :: String -> IO ()
alert = putStrLn
#endif



instance Read NP.Rule where
  readsPrec _ str = case find (null . snd) $ startParse pRule str of
                      (Just r) -> [r]
                      Nothing  -> []
                      
  -- readList str = case find (null . snd) $ startParse pRules str of
  --                  (Just r) -> [r]
  --                  Nothing  -> []

pRules :: Parser Char [NP.Rule]                      
pRules = bracketed (commaList pRule)

main = do
  let rulesTxt  = "[pa(alex, ama).,pa(alex, ale).,pa(alex, ari).,pa(claus, alex).,pa(claus, const).,pa(claus, friso).,ma(max, ama).,ma(max, ale).,ma(max, ari).,ma(bea, alex).,ma(bea, const).,ma(bea, friso).,ma(juul, bea).,ma(mien, juul).,ouder(X, Y):-pa(X, Y).,ouder(X, Y):-ma(X, Y).,kind(X, Y):-ouder(Y, X).,voor(X, Y):-ouder(X, Y).,voor(X, Y):-ouder(Z, Y), voor(X, Z).,oeps(X):-oeps(Y).,plus(zero, X, X).,plus(succ(X), Y, succ(Z)):-plus(X, Y, Z).,length(nil, zero).,length(X:XS, succ(Y)):-length(XS, Y).,oplossing(BORD):-rijen(BORD, XSS), juist(XSS), kolommen(BORD, YSS), juist(YSS), vierkanten(BORD, ZSS), juist(ZSS).,juist(nil).,juist(XS:XSS):-verschillend(XS), juist(XSS).,rijen(XSS, XSS).,kolommen(nil, nil:nil:nil:nil:nil).,kolommen(XS:XSS):-voegtoe(XS, YSS, ZSS), kolommen(XSS, YSS).,voegtoe(nil, nil, nil).,voegtoe(X:XS, YS:YSS, (X:YS):ZSS):-voegtoe(XS, YSS, ZSS).]"
  let defRules' = read rulesTxt :: [NP.Rule]
  -- let defRules  = startParse pRules rulesTxt
  alert (show $ defRules')
