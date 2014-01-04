\chapter{Logic in Agda}

Agda's built-in logic is very small: the only primitives are data type definitions, 
universal quantification (|forall|), and implication (|->|), while all the other familiar 
logical connectives --- conjunction, disjunction, negation, existential quantification, 
even equality --- can be encoded using just these.
This chapter explains the encodings and explain with some details how equality works in Agda.

%if False
\begin{code}
module Logic where

open import Basics hiding (_*_)
open import Poly
open import Propositions
open import MorePropositions
\end{code}
%endif

\section{Conjunction}

The logical conjunction of types |A| and |B| can be represented with a data type that
combines the evidence of |A| and a evidence of |B| in an evidence of its conjunction.

\begin{spec}
data _*_ (A B : Set) : Set where
  _,_ : A -> B -> A * B
\end{spec}

Note that, like the definition of |Ev| in a previous chapter, this definition is parameterized; 
however, in this case, the parameters are themselves types, rather than numbers.
The intuition behind this definition is simple: to construct evidence for $A \land B$, we must provide 
evidence for |A| and evidence for |B|. More precisely:
\begin{itemize}
  \item |a , b| can be taken as evidence for |A * B| if |a| is evidence for |A| and |b| is evidence for |B|; and
  \item this is the only way to give evidence for |A * B| --- that is, if someone gives us evidence for 
        |A * B|, we know it must have the form |a , b|, where |a| is evidence for |A| and |b| is evidence for |B|.
\end{itemize}
Besides the elegance of building everything up from a tiny foundation, what's nice about defining conjunction 
this way is that we can prove statements involving conjunction using pattern matching. Consider the next example:
\begin{code}
andExample : Beautiful 0 * Beautiful 3
andExample = b0 , b3
\end{code}
The evidence for |Beautiful 0 * Beautiful 3| is just a pair of evidences, one for |Beautiful 0| and other for |Beautiful 3|.
