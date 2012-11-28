{-# LANGUAGE CPP #-}
-- | This code was scavenged from the JCU server-side Prolog code. 
--   So if that changes you should change it here too otherwise you won't see
--   the effects of your changes. :)
module Prolog where

import           Data.List
import qualified Data.Map as M  
import           Data.Tree (Tree(..))


import            Language.Prolog.NanoProlog.NanoProlog
import            Language.Prolog.NanoProlog.ParserUUTC

#if __UHC__
import            Debug (trace)
#else
import            Debug.Trace (trace)
#endif

type Proof     =  Tree Term
type PCheck    =  Tree Status

data Status    =  Correct
               |  Incomplete
               |  Invalid
               deriving Show

dummyProof :: Proof -> PCheck
-- dummyProof = fmap (const Incomplete)
dummyProof (Node _ xs) = Node Incomplete (map dummyProof xs)

-- | Check if the proof provided by the client is correct, incomplete or
-- incorrect. It returns a @PCheck@: a @Tree Status@. Each node is assigned
-- an indiviual status. The status is determined by examining a node's child
-- nodes (containing terms) and see if they unify. If they do, that particular
-- node is Correct. If a node does not have any more children, but has not
-- reached a fact yet, it is Incomplete. If the child term is a non-unifyable
-- term, it is Incorrect.
checkProof :: [Rule] -> Proof -> PCheck
checkProof rls (Node tm cs)
  | rlsMatch   =  if hasVars tm
                    then  mkNode Incomplete
                    else  mkNode Correct
  | otherwise  =  if null cs
                    then  mkNode Incomplete
                    else  mkNode Invalid
  where  rlsMatch   = any (tryRule tm (map rootLabel cs)) rls
         mkNode st  = Node st (map (checkProof rls) cs)

hasVars :: Term -> Bool
hasVars (Var _)     = True
hasVars (Fun _ [])  = False
hasVars (Fun _ xs)  = any hasVars xs

tryRule ::  Term -> [Term] -> Rule -> Bool
tryRule tm cs (lhs :<-: rhs) =
  case matches (lhs, tm) emptyEnv of
    Nothing  ->  False
    env      ->  length cs == length rhs &&
                 isJust (foldr matches env (zip rhs cs))

instance Subst (Tree Term) where
  subst env (Node tm cs) = Node (subst env tm) (subst env cs)


data DropRes   =  DropRes Bool Proof
               deriving Show

dropUnify :: Proof -> [Int] -> Rule -> DropRes
dropUnify prf []          _                               = DropRes False prf
dropUnify prf tns@(_:ns)  (t :<-: ts)  |  isNothing tmnd  = DropRes False prf
                                       |  otherwise       = drprs
  where  tmnd   =  getNode prf ns
         drprs  =  let  (Just (Node tm _)) = tmnd
                        ntg         = intersperse '.' $ concatMap show tns
                        ncs         = map (flip Node []) (tag ntg ts)
                        mkPrf' env  = subst env (insertNode prf ns ncs)
                   in   case unify' (tag ntg t, tm) emptyEnv of
                          Nothing   -> DropRes False  prf
                          Just env  -> DropRes True   (mkPrf' env)

-- | Add maximum depth to the unification proces                          
unify' :: (Term, Term) -> Maybe Env -> Maybe Env
unify' = trace "unify 10" $ unify 10
  where
    unify :: Int -> (Term, Term) -> Maybe Env -> Maybe Env
    unify 0       _      _                     = Nothing
    unify _       _      Nothing               = Nothing
    unify n      (t, u)  env@(Just e@(Env m))  = trace ("unify.3 " ++ show n) $ uni (subst e t) (subst e u)
      where  uni  (Var x)  y        = Just  (Env (M.insert x  y  m))
             uni  x        (Var y)  = Just  (Env (M.insert y  x  m))
             uni  (Fun x xs) (Fun y ys)
               |  x == y && length xs == length ys  = trace ("uni " ++ show n) $ foldr (unify (n-1)) env (zip xs ys)
               |  otherwise                         = Nothing                          

getNode :: Proof -> [Int] -> Maybe Proof
getNode (Node _ [])  (_:_)   =  Nothing
getNode (Node _ ys)  (x:xs)  |  length ys >= x  = getNode (ys !! (x-1)) xs
                             |  otherwise       = Nothing
getNode node         []      =  Just node

insertNode :: Proof -> [Int] -> [Proof] -> Proof
insertNode (Node t ys)  (x:xs)  cs = Node t (take (x-1) ys ++ insertNode (ys !! (x-1)) xs cs : drop x ys)
insertNode (Node t _)   []      cs = Node t cs

isNothing :: Maybe a -> Bool
isNothing Nothing = True
isNothing _       = False

isJust :: Maybe a -> Bool
isJust = not . isNothing

cnst :: LowerCase -> Term
cnst s = Fun s []

fact :: LowerCase -> [Term] -> Rule
fact fn ts = Fun fn ts :<-: []

paFact :: [String] -> Rule
paFact = fact "pa" . map cnst

maFact :: [String] -> Rule
maFact = fact "ma" . map cnst

nil :: Term
nil = cnst "nil"

exampleData :: [Rule]
exampleData =
  [
  -- Dutch Royal family
     paFact ["alex", "ama"]
  ,  paFact ["alex", "ale"]
  ,  paFact ["alex", "ari"]
  ,  paFact ["claus", "alex"]
  ,  paFact ["claus", "const"]
  ,  paFact ["claus", "friso"]
  ,  maFact ["max", "ama"]
  ,  maFact ["max", "ale"]
  ,  maFact ["max", "ari"]
  ,  maFact ["bea", "alex"]
  ,  maFact ["bea", "const"]
  ,  maFact ["bea", "friso"]
  ,  maFact ["juul", "bea"]
  ,  maFact ["mien", "juul"]
  ,  Fun "ouder"  [Var "X",  Var "Y"] :<-:  [  Fun "pa"     [Var "X",  Var "Y"] ]
  ,  Fun "ouder"  [Var "X",  Var "Y"] :<-:  [  Fun "ma"     [Var "X",  Var "Y"] ]
  ,  Fun "kind"   [Var "X",  Var "Y"] :<-:  [  Fun "ouder"  [Var "Y",  Var "X"] ]
  ,  Fun "voor"   [Var "X",  Var "Y"] :<-:  [  Fun "ouder"  [Var "X",  Var "Y"] ]
  ,  Fun "voor"   [Var "X",  Var "Y"] :<-:  [  Fun "ouder"  [Var "Z",  Var "Y"]
                                            ,  Fun "voor"   [Var "X",  Var "Z"] ]
  ,  Fun "oeps"   [Var "X"] :<-: [Fun "oeps" [Var "Y"]]

  -- Natural numbers
  ,  fact "plus"  [cnst "zero", Var "X", Var "X"]
  ,  Fun "plus"   [Fun "succ" [Var "X"], Var "Y", Fun "succ" [Var "Z"]]
                  :<-: [Fun "plus" [Var "X", Var "Y", Var "Z"]]

  -- Lists
  ,  fact "length" [nil, cnst "zero"]
  ,  Fun "length" [Fun "cons" [Var "X", Var "XS"], Fun "succ" [Var "Y"]] :<-: [Fun "length" [Var "XS", Var "Y"]]

  -- Sudoku
  ,  Fun "oplossing" [Var "BORD"] :<-:  [  Fun "rijen" [Var "BORD", Var "XSS"]
                                        ,  Fun "juist" [Var "XSS"]
                                        ,  Fun "kolommen" [Var "BORD", Var "YSS"]
                                        ,  Fun "juist" [Var "YSS"]
                                        ,  Fun "vierkanten" [Var "BORD", Var "ZSS"]
                                        ,  Fun "juist" [Var "ZSS"]]
  ,  fact "juist" [nil]
  ,  Fun "juist" [Fun "cons" [Var "XS", Var "XSS"]] :<-:  [  Fun "verschillend" [Var "XS"]
                                                          ,  Fun "juist" [Var "XSS"]]
  ,  fact "rijen" [Var "XSS", Var "XSS"]
  ,  fact "kolommen" [nil, Fun "cons" [nil, Fun "cons" [nil, Fun "cons" [nil, Fun "cons" [nil, nil]]]]]
  ,  Fun "kolommen" [Fun "cons" [Var "XS", Var "XSS"]] :<-: [  Fun "voegtoe" [Var "XS", Var "YSS", Var "ZSS"]
                                                            ,  Fun "kolommen" [Var "XSS", Var "YSS"]]
  ,  fact "voegtoe" [nil, nil, nil]
  ,  Fun "voegtoe" [  Fun "cons" [Var "X", Var "XS"]
                   ,  Fun "cons" [Var "YS", Var "YSS"]
                   ,  Fun "cons" [Fun "cons" [Var "X", Var "YS"], Var "ZSS"]]
                   :<-: [Fun "voegtoe" [Var "XS", Var "YSS", Var "ZSS"]]
  ]

exampleGoals :: [(String, Term)]
exampleGoals = 
  [ ("Alexander is ouder van Amalia",   Fun "ouder"     [cnst "alex", cnst "ama"])
  , ("Beatrix is voorouder van Amalia", Fun "voorouder" [cnst "bea",  cnst "ama"])
  ]
          
test = dropUnify (Node (Fun "ouder" [Var "X", cnst "ama"]) []) 
                 [0] 
                 (Fun "ouder"  [Var "X",  Var "Y"] :<-:  [  Fun "pa"     [Var "X",  Var "Y"] ])