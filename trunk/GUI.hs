module Main where

import Data.Char (isUpper)
import Data.List (intercalate)
import Graphics.UI.WX
import Prolog

main :: IO ()
main = start gui

gui :: IO ()
gui = do -- Application frame 
    f        <- frame [text := "Prolog in Haskell"]
    vlogic   <- variable   [  value := [] ]
    rules    <- textCtrl   f  []
    query    <- textEntry  f  []
    output   <- textCtrl   f  []
    cvas     <- panel f    [  on paint    := draw vlogic query
                           ,  clientSize  := sz 200 200 ]
    mfile    <- menuPane   [text := "&File"]
    mopen    <- menuItem   mfile  [  text        := "&Open\tCtrl+O"
                                  ,  help        := "Open a Prolog file"
                                  ,  on command  := onOpen f rules ]
    msave    <- menuItem   mfile  [  text        := "&Save\tCtrl+S"
                                  ,  help        := "Save a Prolog file"
                                  ,  on command  := onSave f rules ]
    msaveas  <- menuItem   mfile  [  text        := "&Save As"
                                  ,  help        := "Save As a Prolog file"
                                  ,  on command  := onSaveAs f rules ]
    mquit    <- menuQuit   mfile  [  text        := "&Quit"
                                  ,  help        := "Quit the program"
                                  ,  on command  := close f ]
    run      <- button     f  [  text := "Run!"
                              ,  on command ::= onRun cvas vlogic rules query output ]
    set f  [  menuBar  := [mfile]
           ,  layout   := column 5 [ boxed "Enter rules and queries, press Run and be amazed!"
                                       (grid 5 5 [
                                              [label "Canvas:",  hfill $ widget cvas] 
                                           ,  [label "Rules:",   hfill $ widget rules]
                                           ,  [label "Query:",   hfill $ widget query]
                                           ,  [label "Output:",  hfill $ widget output]
                                           ,  [widget run]
                                           ])
                                       ]
           ,  clientSize := sz 800 600 ]

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

onRun cvas vlogic rules query output _ = do
    set output [ text := "Running..." ]
    set vlogic [ value := [] ]
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

draw :: (Textual b, Valued w) => w [a] -> b -> DC a1 -> t -> IO ()
draw tv query dc va = do
    vl  <- get tv value
    q   <- get query text
    set dc [fontFace := "Courier New", fontSize := 16, fontWeight := WeightBold ]
    if null vl -- vl contains the solve results! honestly!
        then  drawText dc "No solutions yet!" (pt 50 50) []
        else  do  drawText dc "We have a solution!" (pt 50 100) []
                  line dc (pt 0 115) (pt 500 115) []
                  drawText dc q (pt 75 120) []

append :: Textual a => a -> String -> IO ()
append t s = appendText t $ '\n':s

showSolutions :: Textual a => a -> [EnvTrace] -> IO ()
showSolutions t es = sequence_ [ showSolution t etr | etr <- es]
    where showSolution t (bs, trace) = do  mapM_ (append t . show) trace
                                           append t $ concatMap (showBdg bs) bs