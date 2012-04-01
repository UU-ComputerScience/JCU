module Templates where
  
import Prolog (Status(..))  
  
proof_tree_item term treeLbl disabled status = 
  "<div class=\"tree_item dropzone\">  " ++ treeLbl ++ 
    ". <input type=\"text\" class=\"droppable " ++ statusClass status ++ "\" id=\"proof_" ++ treeLbl ++ "\" value=\"" ++ term ++ "\"" ++ disabled' ++ " /></div>"
  where
    disabled' = if disabled then " disabled=\"disabled\"" else ""
    statusClass Correct     = "greenField"
    statusClass Incomplete  = "yellowField"
    statusClass Invalid     = "redField"
    
rules_list_item :: String -> String  
rules_list_item rule = 
  let rule_replaced = rule -- replace /[^a-zA-Z0-9]+/g, "" 
  in "<div id=\"rule_" ++ rule_replaced   ++ "\" class=\"draggable rule-list-item ui-widget-content\">  <span class=\"rule-text\">"++ rule ++ "</span>  <span class=\"buttons\"><button class=\"btnDeleteList\" type=\"button\" value=\"X\" /></span</div>"
