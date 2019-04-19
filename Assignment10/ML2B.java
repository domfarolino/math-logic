// ML2B.java CS6021 cheng 2019
// Recursive descent parsing for LTL
// propositions are limited to single characters A to Z
// connectives ->, or, and, not, (, )
// temporal connectives x, f, g, u, r, w
// build the parse tree
// Usage: java ML2B < LTLformulas1.txt


import java.io.*;
import java.util.*;

public class ML2B{

   enum GrammarSymbol{
     PROP, NOT, AND, OR, IMPLIES, OPEN, CLOSE, END,
     X, F, G, U, R, W,
     S, S2, E, E2, T, T2, D, D2, B };

   class Node{
     GrammarSymbol type; char propID; Node operand1; Node operand2;
     public Node(GrammarSymbol t, char p, Node c1, Node c2){
    type = t; propID = p; operand1 = c1; operand2 = c2; }
   };

   String formula = "";
   int pos = 0;
   char propSymbol = 0;
   int formulaLen = 0;
   GrammarSymbol lookahead;
   Node root;

   GrammarSymbol nextToken(){
    if (pos >= formulaLen) return GrammarSymbol.END;
    char ch = formula.charAt(pos);
    while (ch == ' ') if (pos++ < formulaLen) ch = formula.charAt(pos);
    if (ch >= 'A' && ch <= 'Z'){
        propSymbol = ch;
        pos++;
        return GrammarSymbol.PROP;
    }else if (ch == '-')
        if (pos + 1 == formulaLen || formula.charAt(pos + 1) != '>'){
            System.err.println("syntax error: '-' must be followed by '>'");
            System.exit(1);
        }else{ pos += 2; return GrammarSymbol.IMPLIES; }
    else if (ch == 'o')
        if (pos + 1 == formulaLen || formula.charAt(pos + 1) != 'r'){
            System.err.println("syntax error: 'o' must be followed by 'r'");
            System.exit(1);
        }else{ pos += 2; return GrammarSymbol.OR; }
    else if (ch == 'a')
        if (pos + 1 == formulaLen || !formula.substring(pos, pos + 3).equals("and")){
            System.err.println("syntax error: 'a' must be followed by 'nd'");
            System.exit(1);
        }else{ pos += 3; return GrammarSymbol.AND; }
    else if (ch == 'n')
        if (pos + 2 >= formulaLen || !formula.substring(pos, pos + 3).equals("not")){
            System.err.println("syntax error: 'n' must be followed by 'ot'");
            System.exit(1);
        }else{ pos += 3; return GrammarSymbol.NOT; }
    else if (ch == '('){ pos++; return GrammarSymbol.OPEN; }
    else if (ch == ')'){ pos++; return GrammarSymbol.CLOSE; }
    else if (ch == 'x'){ pos++; return GrammarSymbol.X; }
    else if (ch == 'f'){ pos++; return GrammarSymbol.F; }
    else if (ch == 'g'){ pos++; return GrammarSymbol.G; }
    else if (ch == 'u'){ pos++; return GrammarSymbol.U; }
    else if (ch == 'r'){ pos++; return GrammarSymbol.R; }
    else if (ch == 'w'){ pos++; return GrammarSymbol.W; }
    else{
        System.err.println("syntax error: Unexpected character " + ch);
        System.exit(1);
    }
    return GrammarSymbol.END;
   }

   Node S(){
    if (lookahead == GrammarSymbol.PROP ||
        lookahead == GrammarSymbol.OPEN ||
        lookahead == GrammarSymbol.NOT ||
        lookahead == GrammarSymbol.X ||
        lookahead == GrammarSymbol.F ||
        lookahead == GrammarSymbol.G){
        Node e = E();
        Node s2 = S2();
        if (s2 == null) return e;
        else return new Node(GrammarSymbol.IMPLIES, '0', e, s2);
    }else{
        System.err.println("parsing error");
        System.exit(1);
        return null;
    }
   }

   Node S2(){
    if (lookahead == GrammarSymbol.IMPLIES){
        lookahead = nextToken();
        Node e  = E();
        Node s2 = S2();
        if (s2 == null) return e;
        else            return new Node(GrammarSymbol.IMPLIES, '0', e, s2);

    }else if (lookahead == GrammarSymbol.CLOSE ||
              lookahead == GrammarSymbol.END)
        return null;
    else{
        System.err.println("parsing error");
        System.exit(1);
        return null;
    }
   }

   Node E(){
    if (lookahead == GrammarSymbol.PROP ||
        lookahead == GrammarSymbol.OPEN ||
        lookahead == GrammarSymbol.NOT ||
        lookahead == GrammarSymbol.X ||
        lookahead == GrammarSymbol.F ||
        lookahead == GrammarSymbol.G){
        Node t = T();
        Node e2 = E2();
        if (e2 == null) return t;
        else return new Node(GrammarSymbol.OR, '0', t, e2);
    }else{
        System.err.println("parsing error");
        System.exit(1);
        return null;
    }
   }

   Node E2(){
    if (lookahead == GrammarSymbol.OR){
        lookahead = nextToken();
        Node t = T();
        Node e2 = E2();
        if (e2 == null) return t;
        else return new Node(GrammarSymbol.OR, '0', t, e2);
    }else if (lookahead == GrammarSymbol.IMPLIES ||
        lookahead == GrammarSymbol.CLOSE ||
        lookahead == GrammarSymbol.END) return null;
    else{
        System.err.println("parsing error");
        System.exit(1);
        return null;
    }
   }

   Node T(){
    if (lookahead == GrammarSymbol.PROP ||
        lookahead == GrammarSymbol.OPEN ||
        lookahead == GrammarSymbol.NOT ||
        lookahead == GrammarSymbol.X ||
        lookahead == GrammarSymbol.F ||
        lookahead == GrammarSymbol.G){
        Node d = D();
        Node t2 = T2();
        if (t2 == null) return d;
        else return new Node(GrammarSymbol.AND, '0', d, t2);
    }else{
        System.err.println("parsing error");
        System.exit(1);
        return null;
    }
   }

   Node T2(){
    if (lookahead == GrammarSymbol.AND){
        lookahead = nextToken();
        Node d = D();
        Node t2 = T2();
        if (t2 == null) return d;
        else return new Node(GrammarSymbol.AND, '0', d, t2);
    }else if (lookahead == GrammarSymbol.IMPLIES ||
        lookahead == GrammarSymbol.OR ||
        lookahead == GrammarSymbol.CLOSE ||
        lookahead == GrammarSymbol.END) return null;
    else{
        System.err.println("parsing error");
        System.exit(1);
        return null;
    }
   }

   Node D(){ // only grammar rule: D ::= B D2
    if (lookahead == GrammarSymbol.PROP ||
        lookahead == GrammarSymbol.OPEN ||
        lookahead == GrammarSymbol.NOT ||
        lookahead == GrammarSymbol.X ||
        lookahead == GrammarSymbol.F ||
        lookahead == GrammarSymbol.G){
        Node b  = B();
        Node d2 = D2();
        if (d2 == null) return b;
        else return new Node(lookahead, '0', b, d2); // This will be B1 U/R/W B2
    }else{
        System.err.println("parsing error");
        System.exit(1);
        return null;
    }
   }

   Node D2(){ // non-recursive
    if (lookahead == GrammarSymbol.U ||
        lookahead == GrammarSymbol.R ||
        lookahead == GrammarSymbol.W){  // grammar rule D2 ::= U/R/W B
        Node d2 = new Node(lookahead, '0', null, null);
        lookahead = nextToken();
        // your code to call B() and put the result as operand1 in d2
        d2.operand1 = B();
        return d2;
    }else if (lookahead == GrammarSymbol.IMPLIES ||
              lookahead == GrammarSymbol.OR ||
              lookahead == GrammarSymbol.AND ||
              lookahead == GrammarSymbol.CLOSE ||
              lookahead == GrammarSymbol.END) return null;  // grammar rule D2 ::=
    else{
        System.err.println("parsing error");
        System.exit(1);
        return null;
    }
   }

   Node B(){
    if (lookahead == GrammarSymbol.PROP){
        Node b = new Node(GrammarSymbol.PROP, propSymbol, null, null);
        lookahead = nextToken();
        return b;
    }else if (lookahead == GrammarSymbol.OPEN){
        lookahead = nextToken();
        Node s = S();
        if (lookahead == GrammarSymbol.CLOSE){
            lookahead = nextToken();
            return s;
        }else{
            System.err.println("parsing error");
            System.exit(1);
            return null;
        }
    }
    else if (lookahead == GrammarSymbol.NOT ||
        lookahead == GrammarSymbol.X ||
        lookahead == GrammarSymbol.F ||
        lookahead == GrammarSymbol.G){
        Node b = new Node(lookahead, '0', null, null);
		lookahead = nextToken();
		// your code to call B() and put the result as operand1 in b
        Node op = B();
        b.operand1 = op;
		return b;
    }
    else{
        System.err.println("parsing error");
        System.exit(1);
        return null;
    }
   }


   void parse(){
    Scanner in = new Scanner(System.in);
    while (in.hasNextLine()){
        formula = in.nextLine();
        System.out.println(formula);
        pos = 0;
        formulaLen = formula.length();
        lookahead = nextToken();
        showTree(S(), 0);
        System.out.println();
    }
   }

   void showTree(Node tree, int depth){
    for (int i = 0; i < depth; i++) System.out.print("  ");
    System.out.print(tree.type);
    switch (tree.type){
        case IMPLIES: case OR: case AND: case U: case R: case W:
            System.out.println();
            showTree(tree.operand1, depth + 1);
            showTree(tree.operand2, depth + 1);
            break;
        case NOT: case X: case F: case G:
            System.out.println();
            showTree(tree.operand1, depth + 1);
            break;
        case PROP: System.out.println(" " + tree.propID);
            break;
        default: ;
    }
   }


 public static void main(String[] args){
     ML2B ml2 = new ML2B();
     ml2.parse();
 }
}


