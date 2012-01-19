module Templates where
  
import Prolog (Status(..))  
  
home = "<div class=\"yui3-g\">  <div class=\"yui3-u-1-2\">    <div class=\"content\">      <h2>Proof Tree</h2>      <div id=\"proof-tree-div\" class=\"noClue\"><!-- TREE GOES HERE --></div>      <div id=\"subst\">Substitute        <input type=\"text\" id=\"txtSubstSub\" style=\"width: 50px\" /> for        <input type=\"text\" id=\"txtSubstFor\" style=\"width: 50px\" />        <input type=\"button\" id=\"btnSubst\" value=\"Substitute\" />        (e.g. substitute bea for X0)      </div><input type=\"hidden\" id=\"storeDoChecking\" value=\"False\"/>      <input type=\"button\" id=\"btnCheck\" value=\"Check Proof\" />      <input type=\"button\" id=\"btnReset\" value=\"Reset Tree\" />      <!--      <h3>Note</h3>      <p class=\"lhsText\">Due to limitations in the current version of the      software, you might see variables with the same name in different text      fields in the  tree. However, these are not necessarily the same      variable! Double-check to see which rules you can apply and which      variables those rules have.</p>      -->      <h3>Color coding help</h3>      <ul id=\"color-coding-list\">        <li><div class=\"box redField\"></div> Incorrect rule application</li>        <li><div class=\"box yellowField\"></div> Incomplete proof</li>        <li><div class=\"box greenField\"></div> Correct rule</li>        <li><div class=\"box blueField\"></div> Syntax error</li>      </ul>      <h3>Example data</h3>      <p class=\"lhsText\">      Example data containing the Dutch royal family, the list structure and      lookup, and the natural numbers (as discussed in the JCU lecture notes)      can be loaded by <a href=\"/load-example\">clicking this link</a>. Beware      that this will replace all your existing rules!      </p>    </div>  </div>  <div class=\"yui3-u-1-2\">    <div class=\"content\">      <h2>Stored Rules</h2>      <p>Drag a rule form the list below to a field containing a term in the      tree on the left.</p>      <div id=\"rules-list-div\"><!-- LIST GOES HERE --></div>      <div id=\"divListAdd\">        <input type=\"text\" id=\"txtAddRule\" />        <input type=\"button\" value=\"Add\" id=\"btnAddRule\" />      </div>    </div>  </div></div>"

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
