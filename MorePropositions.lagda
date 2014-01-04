\chapter{More about Propositions and Evidence}

%if False
\begin{code}
module MorePropositions where

open import Basics
open import Poly
open import Propositions
\end{code}
%endif

\section{Relations}

A proposition parameterized by a number (such as |Ev| or |Beautiful|) can be thought of as a property --- 
i.e., it defines a subset of |Nat|, namely those numbers for which the proposition is provable. In the same 
way, a two-argument proposition can be thought of as a relation --- i.e., it defines a set of pairs for which 
the proposition is provable.

One useful example is the ``less than or equal to'' relation on numbers.

The following definition should be fairly intuitive. It says that there are two ways to give evidence that one 
number is less than or equal to another: either observe that they are the same number, or give evidence that 
the first is less than or equal to the predecessor of the second.
\begin{code}
data _<=_ : Nat -> Nat -> Set where
  len : forall n -> n <= n
  les : forall n m -> n <= m -> n <= suc m
\end{code}
Proofs of facts about |<=| using the constructors |len| and |les| follow the same patterns as proofs 
about properties, like |Ev| in the previous chapter. We can apply the constructors to prove |<=| goals 
(e.g., to show that |3<=3| or |3<=6|), and we can use pattern matching to extract information from |<=| 
hypotheses in the context (e.g., to prove that |(2 <= 1) -> 2+2==5|.)

The "strictly less than" relation |n < m| can now be defined in terms of |n <= m|:
\begin{code}
_<_ : Nat -> Nat -> Set
n < m = suc n <= m
\end{code}

\begin{exe}
Prove the following fact:
\begin{spec}
leTrans : forall {m n o} -> m <= n -> n <= o -> m <= o
leTrans = (HOLE GAP 0)
\end{spec}
\end{exe}

\begin{exe}
Prove the following fact:
\begin{spec}
zeroLeN : forall n -> 0 <= n
zeroLeN = (HOLE GAP 0)
\end{spec}
\end{exe}

\begin{exe}
Prove the following fact:
\begin{spec}
nLeMSnleSm : forall n m -> n <= m -> suc n <= suc m
nLeMSnleSm = (HOLE GAP 0)
\end{spec}
\end{exe}

\begin{exe}
Prove the following fact:
\begin{spec}
snLeSmNLeM : forall n m -> suc n <= suc m -> n <= m
snLeSmNLeM = (HOLE GAP 0)
\end{spec}
\end{exe}

\begin{exe}
Prove the following fact:
\begin{spec}
lePlusL : forall a b -> a <= a + b
lePlusL = (HOLE GAP 0)
\end{spec}
\end{exe}

\begin{exe}
Prove the following fact:
\begin{spec}
plusLt : forall n1 n2 m -> n1 + n2 < m -> n1 < m -> n2 < m
plusLt = (HOLE GAP 0)
\end{spec}
\end{exe}

\begin{exe}
Prove the following fact:
\begin{spec}
ltsuc : forall n m -> n < m -> n < suc m
ltsuc = (HOLE GAP 0)
\end{spec}
\end{exe}

\section{Programming with Propositions}

A proposition is a statement expressing a factual claim, like ``two plus two equals four.'' In Agda, propositions 
are written as types. Although we haven't discussed this explicitly, we have already seen numerous examples.

One important point: Both provable and unprovable claims are perfectly good propositions. Simply being a proposition is one thing; 
being provable is something else! Consider these examples:
\begin{spec}
t : 2 + 2 == 4
t = refl

t' : 2 + 2 == 5
t' = (HOLE GAP 0) -- not provable
\end{spec}
Of course proposition |t'| cannot be provable, because reducing its type we get |4 == 5|, that can't be proved.



