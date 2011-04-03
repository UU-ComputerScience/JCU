{-# LANGUAGE FlexibleContexts #-}

module Main where

import Control.Monad
import Data.Char (isUpper)
import Data.List (intercalate)
import Graphics.UI.WX
import Graphics.UI.WXCore
import Prolog

main :: IO ()
main = start gui

gui :: IO ()
gui = do -- Application frame 
    f        <- frame [text := "Prolog in Haskell"]
    sw       <- scrolledWindow f  [ style       := wxVSCROLL
                                  , scrollRate  := sz 20 20
                                  , clientSize  := sz 400 400 ]
    windowReLayoutMinimal f
    vlogic   <- variable       [  value := [] ]
    venvtr   <- variable       [  value := [] ] -- Stores [EnvTrace]. Each EnvTrace is a total solution.
    vrows    <- variable       [  value := [] ] -- [LogicRow]
    istermr  <- variable       [  value := True ]
    onAdd sw vrows istermr -- Add initial row
    rules    <- textCtrl   f   []
    query    <- textEntry  f   [ text := "ouder(X,ama)" ]
    output   <- textCtrl   f   []
    rbox     <- singleListBox f []
    cvas     <- panel      sw  [  on paint    := draw vlogic query
                               ,  clientSize  := sz 800 500 ]
    mfile    <- menuPane   [text := "&File"]
    mopen    <- menuItem   mfile  [  text        := "&Open\tCtrl+O"
                                  ,  help        := "Open a Prolog file"
                                  ,  on command  := onOpen f rules ]
    msave    <- menuItem   mfile  [  text        := "&Save\tCtrl+S"
                                  ,  help        := "Save a Prolog file"
                                  ,  on command  := onSave f rules ]
    msaveas  <- menuItem   mfile  [  text        := "&Save As\tCtrl+Shift+S"
                                  ,  help        := "Save As a Prolog file"
                                  ,  on command  := onSaveAs f rules ]
    mquit    <- menuQuit   mfile  [  text        := "&Quit"
                                  ,  help        := "Quit the program"
                                  ,  on command  := close f ]
    mquery   <- menuPane   [text  := "Query" ]
    mrun     <- menuItem   mquery  [  text        := "&Run\tCtrl+R"
                                   ,  help        := "Run the query"
                                   ,  on command  := onRun cvas vlogic rules query output ]
    addbtn   <- button     f       [  text        := "Add"
                                   ,  on command  := onAdd sw vrows istermr ]
    run      <- button     f       [  text        := "Run!"
                                   ,  on command  := onRun cvas vlogic rules query output ]
    set sw   [  layout      := column 5 [hfill $ widget cvas]
             ,  clientSize  := sz 500 300 ]
    set f    [  menuBar     := [mfile, mquery]
             ,  layout      := column 5 [ boxed "Enter rules and queries, press Run and be amazed!"
                                                (overGrid sw rules query output run rbox)
                                        ]
             ,  clientSize := sz 1000 700 ]

onAdd :: (Form (Window a), Valued w, Valued w1) => Window a -> w [[Layout]]
      -> w1 Bool -> IO ()
onAdd sw vrows istermr = do
  nrw  <- createRow sw vrows
  itr  <- get istermr value
  rws  <- get vrows value
  let  newRows = if itr then mkTermLayout nrw:rws
                        else mkRuleLayout nrw:rws
  set  vrows    [ value       :=  newRows ]
  set  sw       [ layout      :=  grid 5 5 newRows
                , clientSize  :=  sz 500 200 ]
  set  istermr  [ value       :~  \x -> not x ]

data LogicRow = LogicRow  { okButton   :: BitmapButton ()
                          , hntButton  :: BitmapButton ()
                          , delButton  :: BitmapButton ()
                          , logicFld   :: TextCtrl () }

createRow :: (Form (Window a), Valued w) => Window a -> w [[Layout]]
          -> IO LogicRow
createRow sw vrows =
   let  mkBtn file cmd = bitmapButton sw [  picture     := file
                                         ,  clientSize  := sz 16 16
                                         ,  on command  := cmd ] in
   do   ok    <- mkBtn "accept.png" undefined 
        hint  <- mkBtn "help.png" undefined
        del   <- mkBtn "delete.png" (popRow sw vrows) -- TODO: I want a reference to these guys for deletion!
        fld   <- textEntry sw []
        return $ LogicRow ok hint del fld

popRow :: (Form w1, Valued w, Dimensions w1) => w1 -> w [[Layout]] -> IO ()
popRow sw vrows = do
  rows <- get vrows value
  case rows of
    []     ->  return ()
    (x:xs) ->  let tl = tail xs in
               do -- objectDelete x
                  set vrows  [  value := tl ]
                  set sw     [  layout      := grid 5 5 tl
                             ,  clientSize  := sz 500 200 ]

mkRuleLayout, mkTermLayout :: LogicRow -> [Layout]
mkRuleLayout (LogicRow btnOK btnHint btnDel fld) =
  [ answerField btnOK btnHint btnDel fld, widget $ hrule 350 ]
mkTermLayout (LogicRow btnOK btnHint btnDel fld) =
  [ widget $ empty, answerField btnOK btnHint btnDel fld ]

answerField :: (Widget w3, Widget w, Widget w2, Widget w1) => w -> w1 -> w2
            -> w3 -> Layout
answerField btnOK btnHint btnDel fld = widget $ row 5  [ widget btnOK
                                                       , widget btnHint
                                                       , widget btnDel
                                                       , widget fld ]

overGrid :: (Widget w1,Widget w3,Widget w5,Widget w4,Widget w2,Widget w) =>w -> w1 -> w2 -> w3 -> w5 -> w4 -> Layout
overGrid sw rules query output run rbox = row 5 [widget mgrd, vfill $ widget rbox]
  where mgrd = grid 5 5  [ [label "Action:",  hfill $ widget sw    ]
                         , [label "Rules:",   hfill $ widget rules ]
                         , [label "Query:",   hfill $ widget query ]
                         , [label "Output:",  hfill $ widget output]
                         , [widget run]
                         ]

onSolve = undefined
onHint  = undefined

runDiag :: (t1 -> Bool -> Bool -> t2 -> [(String, [String])] -> String
        -> String -> t) -> t1 -> t2 -> t
runDiag diag f hdr =  diag f True True hdr
                          [("Prolog files (*.pro, *.pl)", ["*.pro", "*.pl"])]
                          "" ""

onOpen :: Textual w => Window a -> w -> IO ()
onOpen f rules = do
    diag <- runDiag fileOpenDialog f "Select Prolog file"
    case diag of
        Nothing  -> return () -- TODO: Nice error handling
        Just f   -> do  cnts <- readFile f
                        set rules [ text := cnts ]

onSave :: Textual w => Window a -> w -> IO ()
onSave f rules = do
    diag <- runDiag fileSaveDialog f "Save Prolog file"
    case diag of
        Nothing  -> return () -- TODO: Nice handling
        Just f   -> do  rs <- get rules text
                        writeFile f rs

onSaveAs :: Textual w => Window a -> w -> IO ()
onSaveAs = onSave

onRun :: (Textual a, Textual w1, Textual w2, Valued w, Paint w3)
      => w3 -> w [EnvTrace] -> w1 -> w2 -> a -> IO ()
onRun cvas vlogic rules query output = do
    set output  [  text   := "Running..." ]
    set vlogic  [  value  := [] ]
    repaint cvas
    rs <- get rules text
    let (rules, rerr) = startParse pRules rs
    if null rerr
        then  do qs <- get query text
                 let (goal, ferr) = startParse pFun qs
                 if null ferr
                     then  do  append output "Done!"
                               let sol = solve rules [goal] [] 0
                               set vlogic [ value := sol ]
                               showSolutions output sol
                               repaint cvas
                     else  append output $ "Invalid query: " ++ qs
        else  append output $ "Errors in parsing rules! " ++ show rerr

{-
ouder(X,ama):


    ma(max, ama):-.                pa(alex, ama):-.
    ---------------                ----------------
        ma(X0, Y0)                    pa(X0, Y0)
--------------------------    --------------------------
ouder(X0, Y0):-ma(X0, Y0).    ouder(X0, Y0):-pa(X0, Y0).
--------------------------------------------------------
                    ouder(X,ama)
-}


-- TODO: Clean up and improve drawing code
draw :: (Textual b, Valued w) => w [EnvTrace] -> b -> DC a1 -> t -> IO ()
draw tv query dc va = do
    vl  <- get tv value
    q   <- get query text
    set dc [  fontFace  := "Courier New"
           ,  fontSize  := 14 ]
    if null vl
        then  drawText dc "No solutions yet!" (pt 50 50) []
        else  do  drawText    dc "We have a solution!" (pt 50 50) []
                  drawTraces  dc vl 350

drawTraces :: DC a -> [EnvTrace] -> Int -> IO ()
drawTraces dc trs y = foldM_ drawTraces' 50 trs
    where drawTraces' x (_,tr) = do  drawTrace dc tr x
                                     return $ x+300

drawTrace :: DC a -> [Trace] -> Int -> IO ()
drawTrace dc trs x = foldM_ drawTrace' 350 trs
    where drawTrace' y t =  let dt f  y' = drawText  dc (show $ f t)  (pt x y')    []
                                ln    y' = line      dc (pt 0 y')     (pt 700 y')  [] in
                            do  dt goal y
                                ln (y+15)
                                dt unif (y-20)
                                ln (y-5)
                                return $ y-40

append :: Textual a => a -> String -> IO ()
append t s = appendText t $ '\n':s

showSolutions :: Textual a => a -> [EnvTrace] -> IO ()
showSolutions t es = sequence_ [ showSolution t etr | etr <- es]
    where showSolution t (bs, trace) = do  mapM_ (append t . show) trace
                                           append t $ concatMap (showBdg bs) bs

