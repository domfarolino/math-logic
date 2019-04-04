// ML1C.java CS6021 cheng 2019
// Recursive descent parsing for propositional logic
// propositions are limited to single characters A to Z
// connectives ->, or, and, not, (, )
// build the parse tree
// and then replace each P -> Q with not P or Q
// Usage: java ML1C "notPandQ->Pand(QornotR)" or
// Usage: java ML1C "not P and Q -> P and(Q or not R)"

import java.io.*;
import java.util.*;

public class ML1C{

   enum GrammarSymbol{ 
     PROP, NOT, AND, OR, IMPLIES, OPEN, CLOSE, END,
     S, S2, E, E2, T, T2, F };

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

   public ML1C(String f){
	formula = f; pos = 0; formulaLen = f.length();
   }

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
	else{
		System.err.println("syntax error: Unexpected character " + ch);
		System.exit(1);
	}
	return GrammarSymbol.END;
   }

   Node S(){ 
	if (lookahead == GrammarSymbol.PROP ||
		lookahead == GrammarSymbol.OPEN ||
		lookahead == GrammarSymbol.NOT){
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
		lookahead == GrammarSymbol.NOT){
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
		lookahead == GrammarSymbol.NOT){
		Node f = F();
		Node t2 = T2();
		if (t2 == null) return f;
		else return new Node(GrammarSymbol.AND, '0', f, t2);		
	}else{
		System.err.println("parsing error");
		System.exit(1);						
		return null;					
	}
   }

   Node T2(){
	if (lookahead == GrammarSymbol.AND){
		lookahead = nextToken();
		Node f = F();
		Node t2 = T2();
		if (t2 == null) return f;
		else return new Node(GrammarSymbol.AND, '0', f, t2);		
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

   Node F(){
	if (lookahead == GrammarSymbol.PROP){
		char oldProp = propSymbol;
		lookahead = nextToken();
		return new Node(GrammarSymbol.PROP, oldProp, null, null);
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
	}else if (lookahead == GrammarSymbol.NOT){
		lookahead = nextToken();
		Node f = F();
		return new Node(GrammarSymbol.NOT, '0', f, null);
	}else{
		System.err.println("parsing error");
		System.exit(1);						
		return null;					
	}
   }


   void parse(){
	lookahead = nextToken();
	root = S();
   }

   void showTree(Node tree, int depth){
	for (int i = 0; i < depth; i++) System.out.print("  ");
	System.out.print(tree.type);
	switch (tree.type){
		case IMPLIES: case OR: case AND: 
			System.out.println();
			showTree(tree.operand1, depth + 1);
			showTree(tree.operand2, depth + 1);
			break;
		case NOT: System.out.println();
			showTree(tree.operand1, depth + 1);
			break;
		case PROP: System.out.println(" " + tree.propID);
			break;
		default: ;
	}
   }

  Node IMPL_FREE(Node tree){
	if (tree.type == GrammarSymbol.IMPLIES) return new Node(GrammarSymbol.OR, '0',
		new Node(GrammarSymbol.NOT, '0', IMPL_FREE(tree.operand1), null),
		IMPL_FREE(tree.operand2));
	else return tree;
  }

  Node NNF(Node tree){
	switch (tree.type){
		case PROP: return tree;
		case OR: return new Node(GrammarSymbol.OR, '0', 
				NNF(tree.operand1), NNF(tree.operand2));
		case AND: return new Node(GrammarSymbol.AND, '0', 
				NNF(tree.operand1), NNF(tree.operand2));
		case NOT: switch(tree.operand1.type){
				case PROP: return tree;
				case NOT: return tree.operand1.operand1; 
				case OR: return new Node(GrammarSymbol.AND, '0',
					NNF(new Node(GrammarSymbol.NOT, '0',
						tree.operand1.operand1, null)),
					NNF(new Node(GrammarSymbol.NOT, '0',
						tree.operand1.operand2, null)));
				case AND: return new Node(GrammarSymbol.OR, '0',
					NNF(new Node(GrammarSymbol.NOT, '0',
						tree.operand1.operand1, null)),
					NNF(new Node(GrammarSymbol.NOT, '0',
						tree.operand1.operand2, null)));
				default: return null;
			}
		default: return null;
	}
  }

  Node CNF(Node tree){  // implementing CNF in lecture notes
	switch (tree.type){
		case PROP: case NOT: return tree;
		case AND: case OR: return DISTR(tree.operand1, tree.operand2);
		default: return null;
	}
  }

  Node DISTR(Node n1, Node n2){
    if (n1.type == GrammarSymbol.AND) return new Node(GrammarSymbol.AND, '0',
      DISTR(n1.operand1, n2), DISTR(n1.operand2, n2));
    if (n2.type == GrammarSymbol.AND) return new Node(GrammarSymbol.AND, '0',
      DISTR(n1, n2.operand1), DISTR(n1, n2.operand2));
    return new Node(GrammarSymbol.OR, '0', n1, n2);
  }

  void transform(){
	root = CNF(NNF(IMPL_FREE(root)));
	showTree(root, 0);
	conjuncts(root);
  }

  void conjuncts(Node tree){  // precondition: tree is in CNF
	switch(tree.type){
		case PROP: System.out.print(tree.propID + " "); break;
		case NOT: System.out.print("-" + tree.operand1.propID + " "); break;
		case AND: conjuncts(tree.operand1); System.out.println(); 
			conjuncts(tree.operand2); System.out.println(); break;
		case OR: conjuncts(tree.operand1); conjuncts(tree.operand2);
		default: ;
	}
 }

 void transform1(){
	showTree(IMPL_FREE(root), 0);
 }

  void transform2(){
	root = NNF(IMPL_FREE(root));
	showTree(root, 0);
  }

	
 public static void main(String[] args){
    if (args.length < 1){
	System.err.println("Usage: java ML1C quoted_propositional_logic_expression");
	return;
    }
    ML1C ml1 = new ML1C(args[0]);
    ml1.parse();
    ml1.transform();
 }
}


	
