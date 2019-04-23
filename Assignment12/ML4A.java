// ML4A.java CS6021 cheng 2019
// Recursive descent parsing for CTL
// propositions are limited to single characters A to Z
// connectives ->, or, and, not, (, )
// temporal connectives ax, af, ag, au, ex, ef, eg, eu
// build the parse tree
// implementing SAT from Fig. 3.28 of Huth and Ryan
// Usage: java ML4A model formulas

import java.io.*;
import java.util.*;

public class ML4A{

   class Model{  // states are integers 0 to numberOfStates - 1
	int numberOfStates = 0;
	HashSet<Integer> S = null;
	ArrayList<HashSet<Character>> L = null;
	ArrayList<HashSet<Integer>> transitionTo = null;
	ArrayList<HashSet<Integer>> transitionFrom = null;

	public Model(String filename){  // construct model from file
		Scanner in = null;
		try {
			in = new Scanner(new File(filename));
		} catch (FileNotFoundException e){
			System.err.println(filename + " not found");
			System.exit(1);
		}
		numberOfStates = Integer.parseInt(in.nextLine());  
		S = new HashSet<Integer>(numberOfStates);
		for (int i = 0; i < numberOfStates; i++) S.add(i);
		L = new ArrayList<HashSet<Character>>(numberOfStates);  // truth assignments
		for (int i = 0; i < numberOfStates; i++){
			String line = in.nextLine();
			HashSet<Character> props = new HashSet<Character>(line.length());
			for (int j = 0; j < line.length(); j++) props.add(line.charAt(j));
			L.add(props);
		}
		transitionTo = new ArrayList<HashSet<Integer>>(numberOfStates);
		transitionFrom = new ArrayList<HashSet<Integer>>(numberOfStates);
		for (int i = 0; i < numberOfStates; i++){   // transitions
			transitionTo.add(new HashSet<Integer>());
			transitionFrom.add(new HashSet<Integer>());
		}
		for (int i = 0; i < numberOfStates; i++){
			String[] terms = in.nextLine().split(" ");
			for (String t: terms){
				int j = Integer.parseInt(t);
				transitionTo.get(i).add(j);
				transitionFrom.get(j).add(i);
			}
		}
		in.close();
	}

	HashSet<Integer> preE(Set<Integer> Y){  // all states that may transition into Y
		HashSet<Integer> Z = new HashSet<Integer>();
		for (int j: Y) Z.addAll(transitionFrom.get(j));
		return Z;
	}

	HashSet<Integer> preA(Set<Integer> Y){  // all states that only transition into Y
		HashSet<Integer> Z = new HashSet<Integer>();
		for (int i: S) if (Y.containsAll(transitionTo.get(i))) Z.add(i);
		return Z;
	}
   };

   enum GrammarSymbol{ 
     PROP, NOT, AND, OR, IMPLIES, OPEN, CLOSE, END,
     AX, AF, AG, AU, EX, EF, EG, EU, TRUE, 
     S, S2, E, E2, T, T2, D, D2, B };

   class Node{
     GrammarSymbol type; char propID; Node operand1; Node operand2; 
     public Node(GrammarSymbol t, char p, Node c1, Node c2){
	type = t; propID = p; operand1 = c1; operand2 = c2; }
   };

   Model model = null;
   String formula = "";
   int pos = 0;
   char propSymbol = 0;
   int formulaLen = 0;
   GrammarSymbol lookahead;
   Node True = new Node(GrammarSymbol.TRUE, '0', null, null);
   Node root = null;

   public ML4A(String filename){
	model = new Model(filename);
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
		Node s = S();
		Node d2 = D2();
		if (d2 == null) return s;
                // Should this be lookahead?
		else return new Node(d2.type, '0', s, d2); // This will be S1 AU/EU S2	
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
                Node s = S();
                d2.operand1 = s;
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
                Node bb = B();
                b.operand1 = bb;
		return b;
	}else{
		System.err.println("parsing error");
		System.exit(1);						
		return null;					
	}

   }

   void parse(String f){
	formula = f;
	System.out.println("formula " + formula);
	pos = 0; 
	formulaLen = formula.length();
	lookahead = nextToken();
        root = D();
	showTree(root, 0);
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

   HashSet<Integer> SAT(Node tree){ // Fig. 3.28
	switch (tree.type){
		case TRUE: System.out.println("TRUE"); return model.S;
		case PROP: System.out.println("PROP " + tree.propID); 
			HashSet<Integer> T = new HashSet<Integer>();
			for (int i: model.S) if (model.L.get(i).contains(tree.propID)) T.add(i);
			return T;
		case NOT: System.out.println("NOT");
			HashSet<Integer> S2 = new HashSet<Integer>(model.S);
			S2.removeAll(SAT(tree.operand1));
			return S2;
		case AND: System.out.println("NOT"); 
			T = SAT(tree.operand1);
			T.retainAll(SAT(tree.operand2));
			return T;
		case OR: System.out.println("OR");
			T = SAT(tree.operand1);
			T.addAll(SAT(tree.operand2));
			return T;
		case IMPLIES: System.out.println("IMPLIES");
			return SAT(new Node(GrammarSymbol.OR, '0',
			new Node(GrammarSymbol.NOT, '0', tree.operand1, null),
			tree.operand2));
		case AX: System.out.println("AX");
			return SAT(// your code for "not EX not tree.operand1"
                                  new Node(GrammarSymbol.NOT, '0', new Node(GrammarSymbol.EX, '0', new Node(GrammarSymbol.NOT, '0', tree.operand1, null), null), null)
				);
		case EX: System.out.println("EX"); return SATex(tree.operand1);
		case AU: return SAT(new Node(GrammarSymbol.NOT, '0', new Node(GrammarSymbol.AND, '0',
				new Node(GrammarSymbol.NOT, '0', new Node(GrammarSymbol.EU, '0',
				  new Node(GrammarSymbol.NOT, '0', tree.operand2, null),
				  new Node(GrammarSymbol.AND, '0', 
				    new Node(GrammarSymbol.NOT, '0', tree.operand1, null),
				    new Node(GrammarSymbol.NOT, '0', tree.operand2, null))), null),
				new Node(GrammarSymbol.AF, '0', tree.operand2, null)), null));
		case EU: System.out.println("EU");
			return SATeu(tree.operand1, tree.operand2);
		case EF: System.out.println("EF"); return SATeu(True, tree.operand1);
		case EG: System.out.println("EG");
			return SAT(// your code for "not AF not tree.operand1"
                                  new Node(GrammarSymbol.NOT, '0', new Node(GrammarSymbol.AF, '0', new Node(GrammarSymbol.NOT, '0', tree.operand1, null), null), null)
				);
		case AF: System.out.println("AF"); return SATaf(tree.operand1);
		case AG: System.out.println("AG");
			return SAT(// your code for "not EF not tree.operand1"
                                  new Node(GrammarSymbol.NOT, '0', new Node(GrammarSymbol.EF, '0', new Node(GrammarSymbol.NOT, '0', tree.operand1, null), null), null)
				);
		default: ;
	}
	return null;
  }

  HashSet<Integer> SATex(Node tree){  // Fig.3.29
	return model.preE(SAT(tree));
  }

  HashSet<Integer> SATaf(Node tree){  // Fig. 3.30
	HashSet<Integer> X = model.S;
	HashSet<Integer> Y = SAT(tree);
	while (!X.equals(Y)){
		X = Y;
		Y.addAll(model.preA(Y));
	}
	return Y;
 }

 HashSet<Integer> SATeu(Node tree1, Node tree2){  // Fig. 3.31
	HashSet<Integer> W = SAT(tree1); 
	HashSet<Integer> X = model.S;
	HashSet<Integer> Y = SAT(tree2); 
	while (!X.equals(Y)){
		X = Y;
		HashSet<Integer> Y2 = model.preE(Y);
		Y2.retainAll(W);
		Y.addAll(Y2);
	}
	return Y;
 }

 void printSet(Set<Integer> s){
	for (int j: s) System.out.print(j + " ");
	System.out.println();
 }

 void modelChecking(String filename){
	Scanner in = null;
	try {
		in = new Scanner(new File(filename));
	} catch (FileNotFoundException e){
		System.err.println(filename + " not found");
		System.exit(1);
	}
	while (in.hasNextLine()){
		parse(in.nextLine());
		HashSet<Integer> sat = SAT(root);
		printSet(sat);
		System.out.println();
	}
 }

 public static void main(String[] args){
    ML4A ml4 = new ML4A(args[0]);
    ml4.modelChecking(args[1]);
 }
}


	
