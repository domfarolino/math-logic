// ML3A.java CS6021 cheng 2019
// Recursive descent parsing for CTL
// propositions are limited to single characters A to Z
// connectives ->, or, and, not, (, )
// temporal connectives ax, af, ag, au, ex, ef, eg, eu
// outputs the grammar rules applied in leftmost first order
// Usage: java ML3A < CTLformulas1.txt

import java.io.*;
import java.util.*;

public class ML3A{

   enum GrammarSymbol{ 
     PROP, NOT, AND, OR, IMPLIES, OPEN, CLOSE, END,
     AX, AF, AG, AU, EX, EF, EG, EU,
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

   void D(){ 
	if (lookahead == GrammarSymbol.PROP ||
		lookahead == GrammarSymbol.OPEN ||
		lookahead == GrammarSymbol.NOT ||
		lookahead == GrammarSymbol.AX ||
		lookahead == GrammarSymbol.AF ||
		lookahead == GrammarSymbol.AG ||
		lookahead == GrammarSymbol.EX ||
		lookahead == GrammarSymbol.EF ||
		lookahead == GrammarSymbol.EG){
		System.out.println("D ::= S D2");
		S();
		D2();
	}else{
		System.err.println("parsing error");
		System.exit(1);						
	}
   }

   void D2(){
	if (lookahead == GrammarSymbol.AU){
		System.out.println("D2 ::= AU S");
		lookahead = nextToken();
		S();
	}else if (lookahead == GrammarSymbol.EU){
		System.out.println("D2 ::= EU S");
		lookahead = nextToken();
		S();
	}else if (lookahead == GrammarSymbol.CLOSE ||
		lookahead == GrammarSymbol.END) System.out.println("D2 ::=");
	else{
		System.err.println("parsing error");
		System.exit(1);						
	}
   }

   void S(){ 
	if (lookahead == GrammarSymbol.PROP ||
		lookahead == GrammarSymbol.OPEN ||
		lookahead == GrammarSymbol.NOT ||
		lookahead == GrammarSymbol.AX ||
		lookahead == GrammarSymbol.AF ||
		lookahead == GrammarSymbol.AG ||
		lookahead == GrammarSymbol.EX ||
		lookahead == GrammarSymbol.EF ||
		lookahead == GrammarSymbol.EG){
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
		lookahead == GrammarSymbol.AU ||
		lookahead == GrammarSymbol.EU ||
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
		lookahead == GrammarSymbol.AX ||
		lookahead == GrammarSymbol.AF ||
		lookahead == GrammarSymbol.AG ||
		lookahead == GrammarSymbol.EX ||
		lookahead == GrammarSymbol.EF ||
		lookahead == GrammarSymbol.EG){
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
		lookahead == GrammarSymbol.AU ||
		lookahead == GrammarSymbol.EU ||
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
		lookahead == GrammarSymbol.AX ||
		lookahead == GrammarSymbol.AF ||
		lookahead == GrammarSymbol.AG ||
		lookahead == GrammarSymbol.EX ||
		lookahead == GrammarSymbol.EF ||
		lookahead == GrammarSymbol.EG){
		System.out.println("T ::= B T2");
		B();
		T2();
	}else{
		System.err.println("parsing error");
		System.exit(1);						
	}
   }

   void T2(){
	if (lookahead == GrammarSymbol.AND){
		System.out.println("T2 ::= and B T2");
		lookahead = nextToken();
		B();
		T2();
	}else if (lookahead == GrammarSymbol.IMPLIES ||
		lookahead == GrammarSymbol.AU ||
		lookahead == GrammarSymbol.EU ||
		lookahead == GrammarSymbol.OR ||
		lookahead == GrammarSymbol.CLOSE ||
		lookahead == GrammarSymbol.END) System.out.println("T2 ::=");
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
		System.out.println("B ::= ( D )");
		lookahead = nextToken();
		D();
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
	}else if (lookahead == GrammarSymbol.AX){
		System.out.println("B ::= AX B");
		lookahead = nextToken();
		B();
	}else if (lookahead == GrammarSymbol.AF){
		System.out.println("B ::= AF B");
		lookahead = nextToken();
		B();
	}else if (lookahead == GrammarSymbol.AG){
		System.out.println("B ::= AG B");
		lookahead = nextToken();
		B();
	}else if (lookahead == GrammarSymbol.EX){
		System.out.println("B ::= EX B");
		lookahead = nextToken();
		B();
	}else if (lookahead == GrammarSymbol.EF){
		System.out.println("B ::= EF B");
		lookahead = nextToken();
		B();
	}else if (lookahead == GrammarSymbol.EG){
		System.out.println("B ::= EG B");
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
		D();
		System.out.println();
	}
   }



    void allTokens(){
	System.out.println(formulaLen);
	while (pos < formulaLen){
		GrammarSymbol g = nextToken();
		if (g == GrammarSymbol.PROP) 
			System.out.println(pos + " " + g + " " + propSymbol);
		else System.out.println(pos + " " + g);
	}
    }


   void parse2(){
	Scanner in = new Scanner(System.in);
	while (in.hasNextLine()){
		formula = in.nextLine();
		System.out.println(formula);
		pos = 0; 
		formulaLen = formula.length();
		allTokens();
		System.out.println();
	}
   }


 public static void main(String[] args){
    ML3A ml3 = new ML3A();
    ml3.parse();
 }
}


	