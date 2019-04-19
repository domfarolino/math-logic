// ML2A.java CS6021 cheng 2019
// Recursive descent parsing for LTL
// propositions are limited to single characters A to Z
// connectives ->, or, and, not, (, )
// temporal connectives x, f, g, u, r, w
// outputs the grammar rules applied in leftmost first order
// Usage: java ML2A < LTLformulas1.txt

import java.io.*;
import java.util.*;

public class ML2A{

   enum GrammarSymbol{ 
     PROP, NOT, AND, OR, IMPLIES, OPEN, CLOSE, END,
     X, F, G, U, R, W, 
     S, S2, E, E2, T, T2, D, D2, B };

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

   void S(){ 
	if (lookahead == GrammarSymbol.PROP ||
		lookahead == GrammarSymbol.OPEN ||
		lookahead == GrammarSymbol.NOT ||
		lookahead == GrammarSymbol.X ||
		lookahead == GrammarSymbol.F ||
		lookahead == GrammarSymbol.G){
		System.out.println("S ::= E S2");
		E();
		S2();
	}else{
		System.err.println("parsing error");
		System.exit(1);						
	}
   }

   void S2(){
	if (lookahead == GrammarSymbol.IMPLIES){
		System.out.println("S2 ::= -> E S2");
		lookahead = nextToken();
		E();
		S2();
	}else if (lookahead == GrammarSymbol.CLOSE ||
		lookahead == GrammarSymbol.END) System.out.println("S2 ::=");
	else{
		System.err.println("parsing error");
		System.exit(1);						
	}
   }

   void E(){ 
	if (lookahead == GrammarSymbol.PROP ||
		lookahead == GrammarSymbol.OPEN ||
		lookahead == GrammarSymbol.NOT ||
		lookahead == GrammarSymbol.X ||
		lookahead == GrammarSymbol.F ||
		lookahead == GrammarSymbol.G){
		System.out.println("E ::= T E2");
		T();
		E2();
	}else{
		System.err.println("parsing error");
		System.exit(1);						
	}
   }

   void E2(){
	if (lookahead == GrammarSymbol.OR){
		System.out.println("E2 ::= or T E2");
		lookahead = nextToken();
		T();
		E2();
	}else if (lookahead == GrammarSymbol.IMPLIES || 
		lookahead == GrammarSymbol.CLOSE ||
		lookahead == GrammarSymbol.END) System.out.println("E2 ::=");
	else{
		System.err.println("parsing error");
		System.exit(1);						
	}
   }

   void T(){ 
	if (lookahead == GrammarSymbol.PROP ||
		lookahead == GrammarSymbol.OPEN ||
		lookahead == GrammarSymbol.NOT ||
		lookahead == GrammarSymbol.X ||
		lookahead == GrammarSymbol.F ||
		lookahead == GrammarSymbol.G){
		System.out.println("T ::= D T2");
		D();
		T2();
	}else{
		System.err.println("parsing error");
		System.exit(1);						
	}
   }

   void T2(){
	if (lookahead == GrammarSymbol.AND){
		System.out.println("T2 ::= and D T2");
		lookahead = nextToken();
		D();
		T2();
	}else if (lookahead == GrammarSymbol.IMPLIES ||
		lookahead == GrammarSymbol.OR ||
		lookahead == GrammarSymbol.CLOSE ||
		lookahead == GrammarSymbol.END) System.out.println("T2 ::=");
	else{
		System.err.println("parsing error");
		System.exit(1);						
	}
   }

   void D(){ 
	if (lookahead == GrammarSymbol.PROP ||
		lookahead == GrammarSymbol.OPEN ||
		lookahead == GrammarSymbol.NOT ||
		lookahead == GrammarSymbol.X ||
		lookahead == GrammarSymbol.F ||
		lookahead == GrammarSymbol.G){
		System.out.println("D ::= B D2");
		B();
		D2();
	}else{
		System.err.println("parsing error");
		System.exit(1);						
	}
   }

   void D2(){
	if (lookahead == GrammarSymbol.U){
		System.out.println("D2 ::= U B");
		lookahead = nextToken();
		B();
	}else if (lookahead == GrammarSymbol.R){
		System.out.println("D2 ::= R B");
		lookahead = nextToken();
		B();
	}else if (lookahead == GrammarSymbol.W){
		System.out.println("D2 ::= W B");
		lookahead = nextToken();
		B();
	}else if (lookahead == GrammarSymbol.IMPLIES ||
		lookahead == GrammarSymbol.OR ||
		lookahead == GrammarSymbol.AND ||
		lookahead == GrammarSymbol.CLOSE ||
		lookahead == GrammarSymbol.END) System.out.println("D2 ::=");
	else{
		System.err.println("parsing error");
		System.exit(1);						
	}
   }


   void B(){
	if (lookahead == GrammarSymbol.PROP){
		System.out.println("B ::= " + propSymbol);
		lookahead = nextToken();
	}else if (lookahead == GrammarSymbol.OPEN){
		System.out.println("B ::= ( S )");
		lookahead = nextToken();
		S();
		if (lookahead == GrammarSymbol.CLOSE)		
			lookahead = nextToken();
		else{
			System.err.println("parsing error");
			System.exit(1);						
		}
	}else if (lookahead == GrammarSymbol.NOT){
		System.out.println("B ::= not B");
		lookahead = nextToken();
		B();
	}else if (lookahead == GrammarSymbol.X){
		System.out.println("B ::= X B");
		lookahead = nextToken();
		B();
	}else if (lookahead == GrammarSymbol.F){
		System.out.println("B ::= F B");
		lookahead = nextToken();
		B();
	}else if (lookahead == GrammarSymbol.G){
		System.out.println("B ::= G B");
		lookahead = nextToken();
		B();
	}else{
		System.err.println("parsing error");
		System.exit(1);						
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
		S();
		System.out.println();
	}
   }


 public static void main(String[] args){
    ML2A ml2 = new ML2A();
    ml2.parse();
 }
}


	