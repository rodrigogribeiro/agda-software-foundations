\chapter{Proof Objects --- Explicit Evidence in Agda}

We have seen that in Agda the mechanisms used for programming --- inductive data types (like |Nat| or |List|) 
and functions over these types --- can be also used for proving properties of these programs, using 
inductive propositions (like |Ev| or |_==_|), implication, and universal quantification. 
In other proof assistants, like Coq, these mechanisms are quite separate.  

In this chapter we will take a more serious look at the so called ``Curry-Howard Isomophism'', that
states the correspondence between functional programs and proofs.

%if False
\begin{code}
module ProofObjects where

open import Basics hiding (_*_) renaming (_+_ to _:+_)
open import Poly
open import Propositions
open import MorePropositions
open import Logic
\end{code}
%endif

We have already seen the fundamental idea: provability in Agda is represented by concrete evidence. 
When we construct the proof of a basic proposition, we are actually building a tree of evidence, 
which can be thought of as a data structure. If the proposition is an implication like |A -> B|, 
then its proof will be an evidence transformer: a recipe for converting evidence for |A| into 
evidence for |B|. So at a fundamental level, proofs are simply programs that manipulate evidence.

\begin{itemize}
  \item[Q.] If evidence is data, what are propositions themselves?
  \item[A.] They are types!
\end{itemize}

Look again at the definition of the beautiful property.
\begin{spec}
data Beautiful : Nat -> Set where
   b0   : Beautiful 0
   b3   : Beautiful 3
   b5   : Beautiful 5
   bsum : forall {n m} -> Beautiful n -> Beautiful m -> Beautiful (n + m)
\end{spec}
The trick is to introduce an alternative pronunciation of ``:''. Instead of ``has type'' we can also say ``is a proof of.'' 
For example, the second line in the definition of |Beautiful| declares that |b0 : beautiful 0|. Instead of 
``b0 has type beautiful 0,'' we can say that ``b0 is a proof of beautiful 0.'' Similarly for |b3| and |b5|.
This pun between types and propositions (between : as ``has type'' and : as ``is a proof of'' or ``is evidence for'') 
is called the \textbf{Curry-Howard correspondence}. It proposes a deep connection between the world of logic and 
the world of computation. This can be represented as:
\begin{center}
\begin{tabular}{lcl}
Logic        &          & Computation\\
propositions & $\equiv$ & types\\
proofs       & $\equiv$ & data values
\end{tabular}
\end{center}
Many useful insights follow from this connection. To begin with, it gives us a natural interpretation of the type of |bsum| constructor:
\begin{center}
  |bsum : forall {n m} -> Beautiful n -> Beautiful m -> Beautiful (n + m)|
\end{center}
This can be read ``|bsum| is a constructor that takes four arguments --- two numbers, |n| and |m|, and two values, of types 
|Beautiful n| and |Beautiful m| --- and yields evidence for the proposition |Beautiful (n+m)|.''

A proof that eight is beautiful, is just the expression |bsum {3} {5} b3 b5|, as we can represent by the following natural deduction style proof:
\[
\begin{array}{c}
  \infer[(b_{sum})]
      {\textit{beautiful }8}
      {
        \infer[(b_3)]
        {\textit{beautiful }3}
        {} 
        &
        \infer[(b_5)]
        {\textit{beautiful }5}
        {} 
      }
\end{array}
\]
Note that in the expression |bsum {3} {5} b3 b5| we can optionally give the implicit parameters |n| and |m| of |bsum| constructor.

\section{Quantification, Implications and Functions}

In Agda there are two sorts of values with arrows in their types: constructors introduced by inductively defined data types, and functions.
Arrows correspond, in the logical side, to the way of give evidence to implications and functions.
Consider the following statement:
\begin{code}
bplus3 : forall (n : Nat) -> Beautiful n -> Beautiful (n :+ 3)
bplus3 n bn = bsum bn b3
\end{code}
What is the proof object corresponding to |bplus3|?
We're looking for an expression whose type is |forall n -> Beautiful n -> Beautiful (n + 3)| --- that is, a function that takes two 
arguments (one number and a piece of evidence) and returns a piece of evidence! 

When we view the proposition being proved by |bplus3| as a function type, one aspect of it may seem a little unusual. The second 
argument's type, |Beautiful n|, mentions the value of the first argument, |n|. While such dependent types are not commonly found 
in ``mainstream'' programming languages, even functional ones like ML or Haskell, they can be useful there too.

Notice that both implication |->| and quantification |forall| correspond to functions on evidence. In fact, they are really 
the same thing: |->| is just a shorthand for a degenerate use of |forall| where there is no dependency, i.e., no need to give 
a name to the type on the LHS of the arrow.

For example, consider this proposition:

\begin{center}
|bplus3' : forall n (E : Beautiful n) -> Beautiful (n :+ 3)|
\end{center}

A proof term inhabiting this proposition would be a function with two arguments: a number |n| and some evidence |E| that |n| is beautiful. 
But the name |E| for this evidence is not used in the rest of the statement of |bplus3'|, so it's a bit silly to bother making up a name 
for it. We could write it like this instead, using the dummy identifier |_| in place of a real name:

\begin{center}
|bplus3' : forall n (_ : Beautiful n) -> Beautiful (n :+ 3)|
\end{center}

\section{Giving Explicit Arguments to Lemmas and Hypotheses}

Sometimes when we want to use a theorem or a hypotheses that has implications or universal quantifiers we need to give
explicit arguments to these parameters. Agda has a efficient term inference mechanism that is able to infer most of
these parameters. Whenever Agda can't infer these parameters, Agda emacs mode will highlight the expression in yellow in
order to indicate that there is some parameter that could not be infered. Consider the next example:

%if False
\begin{code}
postulate plusComm : forall (a b : Nat) -> a :+ b == b :+ a
\end{code}
%endif
\begin{spec}
plusCommR : forall (a b c d e f: Nat) -> (a :+ b) == (c :+ d) -> (c :+ d) == (e :+ f) -> 
                                         (a :+ b) == (e :+ f)
plusCommR a b c = (HOLE GAP 0)
\end{spec}

Here I'll need a better example for this...


