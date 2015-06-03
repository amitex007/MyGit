import java.io.PrintStream;
import org.apache.hadoop.hive.ql.parse.HiveParser;
import java.io.Serializable;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;

import org.antlr.runtime.CommonToken;
import org.antlr.runtime.Token;
import org.apache.hadoop.hive.ql.exec.Task;
import org.apache.hadoop.hive.ql.lib.Node;
import org.apache.hadoop.hive.ql.parse.ASTNode;
import org.apache.hadoop.hive.ql.parse.AbstractSemanticAnalyzerHook;
import org.apache.hadoop.hive.ql.parse.HiveParser;
import org.apache.hadoop.hive.ql.parse.HiveSemanticAnalyzerHookContext;
import org.apache.hadoop.hive.ql.parse.SemanticException;
import org.apache.hadoop.hive.ql.session.SessionState;

public class TandemHook extends AbstractSemanticAnalyzerHook {
private static final String SNAPSHOT_TAB_SUFFIX = "_sp";
private final static int TOK_WHERE = HiveParser.TOK_WHERE;//511;//0.13 871;
private final static int TOK_TABREF = HiveParser.TOK_TABREF;//490;//848;
private final static int TOK_FROM = HiveParser.TOK_FROM;//339;//667;
private final static int TOK_QUERY = HiveParser.TOK_QUERY;//421;//762;
private final static int TOK_TABNAME =HiveParser.TOK_TABNAME;//489;//847;
private final static int TOK_INSERT = HiveParser.TOK_INSERT;//362;//692;
private final static int AND = HiveParser.KW_AND;//30;//33;
private final static int EQUAL = HiveParser.EQUAL;//18;//20;
private final static int OR =HiveParser.KW_OR;// 152;//173;
private final static int TOK_TABLE_OR_COL = HiveParser.TOK_TABLE_OR_COL;//487;//844;
private final static int DOT =HiveParser.DOT;//16;//17;
private final static int lq = HiveParser.LESSTHANOREQUALTO;//243;//280;
private final static int gt = HiveParser.GREATERTHAN;//21;// 23;
private final static int string = HiveParser.StringLiteral;//260;//298;
private final static int COLUMN = HiveParser.Identifier;//24;//26;
private final static int NUMBER = HiveParser.Number;//250;//287;
private final static int TOK_SELEXPR = HiveParser.TOK_SELEXPR;//433;//778;
private final static int TOK_JOIN = HiveParser.TOK_JOIN;//367;//698;

/*TOK_WHERE
=
TOK_TABLE_OR_COL
pt
'200123'*/

/*TOK_WHERE
or
and
=
TOK_TABLE_OR_COL
pt
3
=
TOK_TABLE_OR_COL
id
3
TOK_FUNCTION
TOK_ISNULL
TOK_TABLE_OR_COL
id

TOK_WHERE
and
=
.
TOK_TABLE_OR_COL
o
pt
3
=
TOK_TABLE_OR_COL
id
3


TOK_WHERE
=
.
TOK_TABLE_OR_COL
o
pt
3



TOK_WHERE
and
<=
.
TOK_TABLE_OR_COL
o
id
3
=
TOK_TABLE_OR_COL
status
'3'

*/
public ASTNode preAnalyze(HiveSemanticAnalyzerHookContext context, ASTNode ast) throws SemanticException {
PrintStream stream = SessionState.getConsole().getOutStream();
// stream.println("ast info before" + ast.dump());

List<ASTNode> ptConds = findASTNodeWithPt(ast);
if(ptConds.isEmpty()){
return ast;
}
List<String> aliasInfos = new ArrayList<String>();
for (ASTNode eachPtCond : ptConds) {
String alias = "";
ASTNode fuhao;
if(eachPtCond.getParent().getType() == DOT){
fuhao = (ASTNode) eachPtCond.getParent().getParent();
alias = eachPtCond.getFirstChildWithType(COLUMN).getText();
aliasInfos.add(alias);
}else{
fuhao = (ASTNode) eachPtCond.getParent();
}
ASTNode whereClauseOrLogic = (ASTNode) fuhao.getParent();
String cloumnVal = fuhao.getChild(1).getText();

// stream.println("cloumnVal" + cloumnVal);
String[] dates = cloumnVal.split("\\|");
ASTNode andAstNode;

if(dates.length == 2){
andAstNode = andAST(constructLqCond("'"+dates[0].replace("'", "")+"'",alias),constructGtCond("'"+dates[1].replace("'", "")+"'",alias));
}else{
andAstNode = andAST(constructLqCond("'"+dates[0].replace("'", "")+"'",alias),constructGtCond("'"+dates[0].replace("'", "")+"'",alias));
}


whereClauseOrLogic.replaceChildren(fuhao.getChildIndex(), fuhao.getChildIndex(), andAstNode);

ASTNode whereNode = pointToWhereNode(whereClauseOrLogic);
if(whereNode == null){
continue;
}
List<ASTNode> tabrefs = findTabRefsByWhereNode(whereNode);//if join will find tow tabref
/*TOK_QUERY
TOK_FROM
TOK_JOIN
TOK_TABREF
TOK_TABNAME
test2
w
TOK_TABREF
TOK_TABNAME
tandem
test1*/
/* TOK_QUERY
TOK_FROM
TOK_SUBQUERY
TOK_QUERY
TOK_FROM
TOK_JOIN
TOK_JOIN
TOK_TABREF
TOK_TABNAME
tandem
test_ext
w
TOK_TABREF
TOK_TABNAME
tandem
test2
o
TOK_TABREF
TOK_TABNAME
tandem
test1
mm*/
if(tabrefs.isEmpty()){
continue;
}
changeTbNameByTabRefs(tabrefs,alias);
}

//stream.println("ast info after" + ast.dump());

// findASTNodeWithPt(ast);
return ast;
}

private List<ASTNode> findTabRefsByWhereNode(ASTNode whereNode) {
/*ASTNode queryNode = (ASTNode)whereNode.getParent().getParent();
if(queryNode == null ||queryNode.isNil()||queryNode.getToken() ==null){
return null;
}
ASTNode tabrefNod = queryNode;
while(tabrefNod.getToken().getType() != TOK_TABREF) {
tabrefNod =(ASTNode) tabrefNod.getChild(0);

if(tabrefNod == null ||tabrefNod.isNil()||tabrefNod.getToken() ==null){
return null;
}
}
ASTNode tabrefparent = (ASTNode)tabrefNod.getParent();
return tabrefparent.getChildren();*/

PrintStream stream = SessionState.getConsole().getOutStream();
ASTNode queryNode = (ASTNode)whereNode.getParent().getParent();
if(queryNode == null ||queryNode.isNil()||queryNode.getToken() ==null){
return null;
}
List<ASTNode> tabrefNodes = new ArrayList<ASTNode>();
Queue<ASTNode> queryNodes = new LinkedList<ASTNode>();
queryNodes.offer(queryNode);
while (!queryNodes.isEmpty()) {
ASTNode node = queryNodes.poll();
// stream.println("node info: "+ node.getText() + " type: " +node.getToken().getType()+ "index: "+ node.getChildIndex() +"token: "+node.getToken()+"line: "+node.getLine());
if(node.getToken() != null && node.getToken().getType() == TOK_TABREF){
tabrefNodes.add(node);
}
List<Node> child = node.getChildren();
if(child != null){
for (Node eachNode : child) {
queryNodes.offer((ASTNode)eachNode);
}
}
}
return tabrefNodes;
}
private ASTNode pointToWhereNode(ASTNode whereClauseOrLogic) {
ASTNode whereNode = whereClauseOrLogic;
if(whereNode.getToken() == null ){
return null;
}
while(whereNode.getToken().getType() != TOK_WHERE){
whereNode = (ASTNode)whereNode.getParent();
if(whereNode == null||whereNode.getToken() == null||whereNode.isNil()){
return null;
}
}
return whereNode;
}
private void changeTbNameByTabRefs(List<ASTNode> tabRefs,String alias) {
//PrintStream stream = SessionState.getConsole().getOutStream();
/*if(tabRef.getChild(1) == null){
stream.println("tabRef.getChild(1) is null because subquery");
}*/
if(alias.equals("")){
for (ASTNode tabref : tabRefs) {
ASTNode tabName = (ASTNode) tabref.getFirstChildWithType(TOK_TABNAME);
changeTbName(tabName);
}
}
else{
for (ASTNode tabref : tabRefs) {
if(tabref.getChild(1)!=null&&tabref.getChild(1).getText().equals(alias)){
ASTNode tabName = (ASTNode) tabref.getFirstChildWithType(TOK_TABNAME);
changeTbName(tabName);
}
}
}
}
/*private List<ASTNode> findTabRefNode(ASTNode root){
PrintStream stream = SessionState.getConsole().getOutStream();
Queue<ASTNode> queue = new LinkedList<ASTNode>();
queue.offer(root);
List<ASTNode> tabRefs = new ArrayList<ASTNode>();
while (!queue.isEmpty()) {
ASTNode node = queue.poll();
if(node.getType() == TOK_TABREF ){
stream.println("node info: "+ node.getText() + " type: " +node.getToken().getType()+ "index: "+ node.getChildIndex() +"token: "+node.getToken()+"line: "+node.getLine());
tabRefs.add(node);
}
List<Node> child = node.getChildren();
if(child != null){
for (Node eachNode : child) {
queue.offer((ASTNode)eachNode);
}
}
}
return tabRefs;
}*/
private List<ASTNode> findASTNodeWithPt(ASTNode root) {
PrintStream stream = SessionState.getConsole().getOutStream();
if(root.getToken().getType() != TOK_QUERY && root.getToken().getType() != TOK_FROM){
return Collections.emptyList();
}
List<ASTNode> ptNodes = new ArrayList<ASTNode>();
Queue<ASTNode> queue = new LinkedList<ASTNode>();
queue.offer(root);
while (!queue.isEmpty()) {
ASTNode node = queue.poll();
stream.println("node info: "+ node.getText() + " type: " +node.getToken().getType()+ "index: "+ node.getChildIndex() +"token: "+node.getToken()+"line: "+node.getLine());
if(node.getParent().getType() != TOK_SELEXPR && node.getToken().getType() == TOK_TABLE_OR_COL&&node.getParent().getParent().getType() != TOK_SELEXPR){
String clumn = "";
if(node.getParent().getType() == DOT){
clumn = node.getParent().getChild(1).getText();
}else{
clumn = node.getFirstChildWithType(COLUMN).getText();
}
if(clumn.equals("pt")){
ptNodes.add(node);
}

}
List<Node> child = node.getChildren();
if(child != null){
for (Node eachNode : child) {
queue.offer((ASTNode)eachNode);
}
}
}
return ptNodes;
}
private void changeTbName(ASTNode tabName) {
if (tabName.getToken().getType() != TOK_TABNAME) {
return;
}
int replaceIndex = 0;
int startIndex = 0;
ASTNode tab;
if(tabName.getChildCount() == 2){// has dbname
startIndex = 1;
replaceIndex = 1;
tab =(ASTNode)tabName.getChild(1);
}else{
tab =(ASTNode)tabName.getFirstChildWithType(COLUMN);
}

Token newToken = new CommonToken(tab.getToken());
newToken.setText(newToken.getText()+SNAPSHOT_TAB_SUFFIX);
tabName.replaceChildren(startIndex, replaceIndex, new ASTNode(newToken));

}
public void postAnalyze(HiveSemanticAnalyzerHookContext context, List<Task<? extends Serializable>> rootTasks) throws SemanticException {
}
/* TOK_WHERE
and
<=
.
TOK_TABLE_OR_COL
o
id
3
=
TOK_TABLE_OR_COL
status
'3'*/

private ASTNode constructLqCond(String date ,String tabAlias) {
ASTNode lqNode = new ASTNode(new CommonToken(lq,"<="));
ASTNode lhs;
if(!tabAlias.equals("")){
lhs = new ASTNode(new CommonToken(DOT,"."));
ASTNode dotlhs = new ASTNode(new CommonToken(TOK_TABLE_OR_COL,"TOK_TABLE_OR_COL"));
dotlhs.addChild(new ASTNode(new CommonToken(string,tabAlias)));
lhs.addChild(dotlhs);

}else{
lhs = new ASTNode(new CommonToken(TOK_TABLE_OR_COL,"TOK_TABLE_OR_COL"));
}

lhs.addChild(new ASTNode(new CommonToken(COLUMN,"start_date")));
ASTNode rhs = new ASTNode(new CommonToken(string,date));
lqNode.addChild(lhs);
lqNode.addChild(rhs);
return lqNode;
}
private ASTNode constructGtCond(String date,String tabAlias) {
ASTNode lqNode = new ASTNode(new CommonToken(gt,">"));
ASTNode lhs;
if(!tabAlias.equals("")){
lhs = new ASTNode(new CommonToken(DOT,"."));
ASTNode dotlhs = new ASTNode(new CommonToken(TOK_TABLE_OR_COL,"TOK_TABLE_OR_COL"));
dotlhs.addChild(new ASTNode(new CommonToken(string,tabAlias)));
lhs.addChild(dotlhs);
}else{
lhs = new ASTNode(new CommonToken(TOK_TABLE_OR_COL,"TOK_TABLE_OR_COL"));
}

lhs.addChild(new ASTNode(new CommonToken(COLUMN,"end_date")));
ASTNode rhs = new ASTNode(new CommonToken(string,date));
lqNode.addChild(lhs);
lqNode.addChild(rhs);
return lqNode;
}

private ASTNode andAST(ASTNode left, ASTNode right) {
if ( left == null ) {
return right;
} else if ( right == null ) {
return left;
} else {

ASTNode and = new ASTNode(new CommonToken(AND,"and"));
and.addChild(left);
and.addChild(right);
return and;
}
}

} 
