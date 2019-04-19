// ML3B.java CS6021 cheng 2019
// Recursive descent parsing for CTL
// propositions are limited to single characters A to Z
// connectives ->, or, and, not, (, )
// temporal connectives ax, af, ag, au, ex, ef, eg, eu
// build the parse tree
// Usage: java ML3B < CTLformulas1.txt

import java.io.*;
import java.util.*;

public class ML3B{

   enum GrammarSymbol{ 
     PROP, NOT, AND, OR, IMPLIES, OPEN, CLOSE, END,
     AX, AF, AG, AU, EX, EF, EG, EU,
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
		if (pos + 1 == formulaLen){ 
			System.err.println("syntax error: 'a' must be followed");
			System.exit(1);
		}else switch (formula.charAt(pos + 1)){
			case 'n': 
			if ((pos + 2 < formulaLen) && formula.substring(pos, pos + 3).equals("and")){
				pos += 3; return GrammarSymbol.AND; 
			}else{ System.err.println("syntax error: 'an' must be followed by 'd'");
			System.exit(1);
			}
			case 'x': pos += 2; return GrammarSymbol.AX;
			case 'f': pos += 2; return GrammarSymbol.AF;
			case 'g': pos += 2; return GrammarSymbol.AG;
			case 'u': pos += 2; return GrammarSymbol.AU;
			default: System.err.println("syntax error: 'a' followed by unknown");
				System.exit(1);
		}
	else if (ch == 'e')
		if (pos + 1 == formulaLen){ 
			System.err.println("syntax error: 'e' must be followed");
			System.exit(1);
		}else switch (formula.charAt(pos + 1)){
			case 'x': pos += 2; return GrammarSymbol.EX;
			case 'f': pos += 2; return GrammarSymbol.EF;
			case 'g': pos += 2; return GrammarSymbol.EG;
			case 'u': pos += 2; return GrammarSymbol.EU;
			default: System.err.println("syntax error: 'e' followed by unknown");
				System.exit(1);
		}
	else if (ch == 'n')
		if (pos + 2 >= formulaLen || !formula.substring(pos, pos + 3).equals("not")){ 
			System.err.println("syntax error: 'n' must be followed by 'ot'");
			System.exit(1);
		}else{ pos += 3; return GrammarSymbol.NOT; }
	else if (ch == '('){ pos++; return GrammarSymbol.OPEN; }
	else if (ch == ')'){ pos++; return GrammarSymbol.CLOSE; }
	else{
		System.err.println("syntax error: Unexpected character " + ch);
		System.exit(1);
	}
	return GrammarSymbol.END;
   }

   Node D(){ 
	if (lookahead == GrammarSymbol.PROP ||
		lookahead == GrammarSymbol.OPEN ||
		lookahead == GrammarSymbol.NOT ||
		lookahead == GrammarSymbol.AX ||
		lookahead == GrammarSymbol.AF ||
		lookahead == GrammarSymbol.AG ||
		lookahead == GrammarSymbol.EX ||
		lookahead == GrammarSymbol.EF ||
		lookahead == GrammarSymbol.EG){
		Node b = S();
		Node d2 = D2();
		if (d2 == null) return b;
                //                   should this be lookahead?
		else return new Node(lookahead, '0', b, d2); // This will be S1 AU/EU S2	
		//else return new Node(d2.type, '0', b, d2); // This will be S1 AU/EU S2	
	}else{
		System.err.println("parsing error");
		System.exit(1);						
                return null;
	}
   }

   Node D2(){
	if (lookahead == GrammarSymbol.AU ||
		lookahead == GrammarSymbol.EU){  // D2 ::= AU/EU S
		Node d2 = new Node(lookahead, '0', null, null);
		lookahead = nextToken();
		// your code to call S() and put the result as operand1 in d2
                d2.operand1 = B();
		return d2;
	}else if (lookahead == GrammarSymbol.CLOSE ||
		lookahead == GrammarSymbol.END) return null; // D2 ::=
	else{
		System.err.println("parsing error");
		System.exit(1);						
                return null;
	}
   }

   Node S(){ 
	if (lookahead == GrammarSymbol.PROP ||
		lookahead == GrammarSymbol.OPEN ||
		lookahead == GrammarSymbol.NOT ||
		lookahead == GrammarSymbol.AX ||
		lookahead == GrammarSymbol.AF ||
		lookahead == GrammarSymbol.AG ||
		lookahead == GrammarSymbol.EX ||
		lookahead == GrammarSymbol.EF ||
		lookahead == GrammarSymbol.EG){
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
		Node e = E();
		Node s2 = S2();
		if (s2 == null) return e;
		else return new Node(GrammarSymbol.IMPLIES, '0', e, s2);
	}else if (lookahead == GrammarSymbol.CLOSE ||
		lookahead == GrammarSymbol.AU ||
		lookahead == GrammarSymbol.EU ||
		lookahead == GrammarSymbol.END) return null;
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
		lookahead == GrammarSymbol.AX ||
		lookahead == GrammarSymbol.AF ||
		lookahead == GrammarSymbol.AG ||
		lookahead == GrammarSymbol.EX ||
		lookahead == GrammarSymbol.EF ||
		lookahead == GrammarSymbol.EG){
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
		System.out.println("E2 ::= or T E2");
		lookahead = nextToken();
		Node t = T();
		Node e2 = E2();
		if (e2 == null) return t;
		else return new Node(GrammarSymbol.OR, '0', t, e2);		
	}else if (lookahead == GrammarSymbol.IMPLIES || 
		lookahead == GrammarSymbol.AU ||
		lookahead == GrammarSymbol.EU ||
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
		lookahead == GrammarSymbol.AX ||
		lookahead == GrammarSymbol.AF ||
		lookahead == GrammarSymbol.AG ||
		lookahead == GrammarSymbol.EX ||
		lookahead == GrammarSymbol.EF ||
		lookahead == GrammarSymbol.EG){
		Node b = B();
		Node t2 = T2();
		if (t2 == null) return b;
		else return new Node(GrammarSymbol.AND, '0', b, t2);		
	}else{
		System.err.println("parsing error");
		System.exit(1);						
                return null;
	}
   }

   Node T2(){
	if (lookahead == GrammarSymbol.AND){
		lookahead = nextToken();
		Node b = B();
		Node t2 = T2();
		if (t2 == null) return b;
		else return new Node(GrammarSymbol.AND, '0', b, t2);		
	}else if (lookahead == GrammarSymbol.IMPLIES ||
		lookahead == GrammarSymbol.AU ||
		lookahead == GrammarSymbol.EU ||
		lookahead == GrammarSymbol.OR ||
		lookahead == GrammarSymbol.CLOSE ||
		lookahead == GrammarSymbol.END) return null;
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
		Node d = D();
		if (lookahead == GrammarSymbol.CLOSE){		
			lookahead = nextToken();
			return d;
		}else{
			System.err.println("parsing error");
			System.exit(1);						
			return null;					
		}
	}else if (lookahead == GrammarSymbol.NOT ||
		lookahead == GrammarSymbol.AX ||
		lookahead == GrammarSymbol.AF ||
		lookahead == GrammarSymbol.AG ||
		lookahead == GrammarSymbol.EX ||
		lookahead == GrammarSymbol.EF ||
		lookahead == GrammarSymbol.EG){
		Node b = new Node(lookahead, '0', null, null);
		lookahead = nextToken();
		// your code to call B() and put the result as operand1 in b
                Node opp = B();
                b.operand1 = opp;
		return b;
	}else{
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
		showTree(D(), 0);
		System.out.println();
	}
   }

   void showTree(Node tree, int depth){
	for (int i = 0; i < depth; i++) System.out.print("  ");
	System.out.print(tree.type);
	switch (tree.type){
		case IMPLIES: case OR: case AND: case AU: case EU:
			System.out.println();
			showTree(tree.operand1, depth + 1);
			showTree(tree.operand2, depth + 1);
			break;
		case NOT: case AX: case AF: case AG: case EX: case EF: case EG:
			System.out.println();
			showTree(tree.operand1, depth + 1);
			break;
		case PROP: System.out.println(" " + tree.propID);
			break;
		default: ;
	}
   }

 public static void main(String[] args){
    ML3B ml3 = new ML3B();
    ml3.parse();
 }
}


	
