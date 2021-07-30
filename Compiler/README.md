# Compiler
If the implementations are complete, you can build and run the program as follows:

<pre>
  <code>
  $ ./build
  $ ./main.native
  </code>
</pre> 

## hw1
The goal is to write a compiler that translates regular expressions to deterministic finite automata (DFAs).  
This corresponds to Lexical Analyzer of the compiler.

* <code>main.ml</code>: Driver code with some test cases.  
* <code>regex.ml</code>: The definitions of regular expressions.  
* <code>nfa.ml</code>: NFA implementation.  
* <code>dfa.ml</code>: DFA implementation.  
* <code>hw1.ml</code>: Implement __regex2nfa, nfa2dfa, and run_dfa__ to translate regular expressions to dfa.  

## hw2
Top-down parser was implemented to determine whether the input program is syntactically valid.  
This corresponds to Syntax Analyzer of the compiler.  

## hw3
Implements a SLR parser that has the same purpose as hw2, but is a top-down approach.  
This corresponds to Syntax Analyzer of the compiler.  

## hw4
Implements a static sign analyzer.
The analyzer receives programs in the while language defined in Ocaml.  
And, it analyzes the signs of the variables.  

You can compile <code>analysis.ml</code> and run it as follows:

<pre>
  <code>
  $ ocamlc analysis.ml -o analyzer
  $ ./analyzer
  </code>
</pre> 

This corresponds to Semantic Analyzer of the compiler.  

## hw5
The goal is to convert the source program into a more efficient yet semantically equivalent program.  
This corresponds to Translator and Optimizer of the compiler.  

* <code>s.ml</code>: The definitions of the source language S.  
* <code>t.ml</code>: The definitions of the target language T.  
* <code>translator.ml</code>: Translator to translate the S language program into a the T language program.  
* <code>optimizer.ml</code>: Optimizer to optimize the program to run.  

You can run as follows:
<pre>
  <code>
  $ make
  $ ./run test/t0.s
  </code>
</pre> 

## Parser_Generator
Practice of using ocamlyacc that is a parset generator for OCaml.  

