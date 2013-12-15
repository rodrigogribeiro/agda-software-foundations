%if False
\begin{code}
module InductionProofs where
\end{code}
%endif

\chapter{Proof by Induction}\label{induction-proofs}

The next line imports all definitions from the previous chapter.
\begin{code}
open import Basics
\end{code}
By processing this file with Agda using C-c C-l, the file |Basics| is loaded 
automatically.

\section{Naming Cases}

Unlike Coq, Agda does not have a way to define tactics for naming cases in
proofs by case analysis. Agda takes very seriously the Curry-Howard isomorphism
in which case analysis is understood as pattern matching in function definitions.
Consider the following example, that show a property of |and| function:

\begin{spec}
andElim1 : forall (b c : Bool) -> and b c == True -> b == True
andElim1 b c prf = (HOLE GAP 0)
\end{spec}

We can prove this by case analysis on |b|, since and is defined by analysis
on the first argument (see Section \ref{booleans}). So, we put |b| on the hole 
and trigger the case analysis using Agda mode to produce the following:

\begin{spec}
andElim1 : forall (b c : Bool) -> and b c == True -> b == True
andElim1 True c  prf = (HOLE GAP 0)
andElim1 False c prf = (HOLE GAP 1)
\end{spec}

Now, Agda type checker is able to reduce the hypothesis |prf| and
the goals hold definitionally using |refl|.

\begin{code}
andElim1 : forall (b c : Bool) -> and b c == True -> b == True
andElim1 True c  prf = refl
andElim1 False c prf = prf
\end{code}

\begin{exe}[Simple case analysis proof.]
Prove |andElim2|:
\begin{spec}
andElim2 : forall (b c : Bool) -> and b c == True -> c == True
andElim2 b c prf = (HOLE GAP 0)
\end{spec}
\end{exe}

\section{Proof by Induction}\label{proof-by-induction}

We proved in the last chapter that 0 is a neutral element for + on the left using a simple argument. 
The fact that it is also a neutral element on the right...

\begin{spec}
plus0R : forall (n : Nat) -> n + 0 == n
plus0R n = refl -- does not type check!
\end{spec}

... cannot be proved in the same simple way. Just using |refl| doesn't work: the n in n + 0 is an arbitrary unknown number, 
so Agda cannot reduce the definition of + can't be simplified for check that |n + 0 == n|.

And reasoning by cases doesn't get us much further: the branch of the case analysis where we assume n = 0 goes through, 
but in the branch where |n = S n'| for some |n'| we get stuck in exactly the same way. We could pattern match on |n'| to 
get one step further, but since |n| can be arbitrarily large, if we try to keep on like this we'll never be done.

\begin{spec}
plus0R : forall (n : Nat) -> n + 0 == n
plus0R zero    = refl
plus0R (suc n') = (HOLE GAP 0) -- stuck here...
\end{spec}

To prove such facts --- indeed, to prove most interesting facts about numbers, lists, and other inductively defined sets 
--- we need a more powerful reasoning principle: \textbf{induction}.

Recall (from high school) the principle of induction over natural numbers: If |P(n)| is some proposition involving a natural 
number |n| and we want to show that |P| holds for all numbers |n|, we can reason like this:
\begin{itemize}
  \item show that |P(zero)| holds;
  \item show that, for any |n'|, if |P(n')| holds, then so does |P(suc n')|;
        conclude that |P(n)| holds for all |n|.
\end{itemize}

Note that the induction hypothesis can be seen as a ``recursive call'' of the property being proved over |n'|. Taking this
view, induction proofs are just recursive functions! Curry-Howard isomorphism, strikes again! We need to use the induction
hypothesis |plus0R n'|, which has type |n' + 0 == n'|, but the hole has type |?0 : (suc n' + 0) == suc n'|, that can be simplified
by Agda to |?0 : suc (n' + 0) == suc n'|, according to the definition of |+|. Note that, that only difference between the type
|suc (n' + 0) == suc n'| and the type of induction hypothesis |n' + 0 == n'| is the application of |suc| constructor in both sides
of the equality, showing a \textit{congruence} property. Function |cong| allows us to reason in this way by applying a function on
both sides of a given equality. For now, we will only use |cong| and other equality related functions as ``black-boxes''. Latter,
we will see how these are defined in Agda.

\begin{code}
plus0R : forall (n : Nat) -> n + 0 == n
plus0R zero     = refl
plus0R (suc n') = cong suc (plus0R n')
\end{code}

As another example of an inductive proof over natural numbers, consider the following theorem:

\begin{code}
minusDiag : forall (n : Nat) -> n - n == 0
minusDiag zero     = refl
minusDiag (suc n') = minusDiag n'
\end{code}

\begin{exe}[Simple induction proofs]
Prove the following lemmas using induction. You might need previously proven results.
\begin{spec}
mult0R : forall (n : Nat) -> n * 0 == 0
mult0R = (HOLE GAP 0)

plusNSucM : forall (n m : Nat) -> suc (n + m) == n + suc m
plusNSucM = (HOLE GAP 1)

plusComm : forall (n m : Nat) -> n + m == m + n
plusComm = (HOLE GAP 2)

plusAssoc : forall (n m p : Nat) -> n + (m + p) == (n + m) + p
plusAssoc = (HOLE GAP 3)
\end{spec}
\end{exe}

\begin{exe}{doublePlus}
Consider the following function, which doubles its argument:
\begin{code}
double : Nat -> Nat
double zero = zero
double (suc n') = suc (suc (double n'))
\end{code}
Use induction to prove this simple fact about double:
\begin{spec}
doublePlus : forall (n : Nat) -> double n == n + n
doublePlus = (HOLE GAP 0)
\end{spec}
\end{exe}

\section{Proofs within Proofs}\label{proofs-within-proofs}

In informal mathematics, large proofs are very often broken into a sequence of theorems, 
with later proofs referring to earlier theorems. Occasionally, however, a proof will need some 
miscellaneous fact that is too trivial (and of too little general interest) to bother giving it its 
own top-level name. In such cases, it is convenient to be able to simply state and prove the needed ``sub-theorem'' 
right at the point where it is used. In Agda, we can do this by simply stating this little theorem as a
local definition using |where| reserved word. For people used to Haskell, local definitions are just as in Haskell.
In fact, Agda syntax is heavily based on Haskell's. Next example shows how to use local definitions in a proof.

\begin{code}
mult0Plus' : forall (n m : Nat) -> (0 + n) * m == n * m
mult0Plus' n m = cong (\n -> n * m) h where
           h : 0 + n == n
           h = refl
\end{code}

Here we use |h| as a sub-proof of the fact |0 + n == n| and a anonymous function --- denoted by the \ --- to represent
the greek letter $\lambda$, that is used in $\lambda$-calculus to represent a function binding symbol.

The next is a more elaborate example of local definitions in proofs. Note that we need to make a local proof
of the fact that |n + m == m + n|, using the previous fact (proved in an exercice) that addition is commutative.

%if False
Here will define plusComm just to Agda doesn't bother me in the next definition. In the typeset version,
this code will not appear, thanks to lhs2TeX.
\begin{code}
plusSnmnSm : forall (n m : Nat) -> suc (n + m) == n + suc m
plusSnmnSm zero m = refl
plusSnmnSm (suc n) m = cong suc (plusSnmnSm n m)

plusComm : forall (n m : Nat) -> n + m == m + n
plusComm zero m = sym (plus0R m)
plusComm (suc n) m = trans (plusSnmnSm n m) 
                           (trans (plusComm n (suc m)) 
                                  (plusSnmnSm m n)) 
\end{code}
%endif

\begin{code}
plusRearrange : forall (n m p q : Nat) -> (n + m) + (p + q) == (m + n) + (p + q)
plusRearrange n m p q = cong (\n -> n + p + q) nmComm where
              nmComm : n + m == m + n
              nmComm = plusComm n m
\end{code}

\begin{exe}[Commutativity of Multiplication]
Use local definitions to help prove this theorem. You shouldn't need to use induction.
\begin{spec}
plusSwap : forall (n m p : Nat) -> n + (m + p) == m + (n + p)
plusSwap = (HOLE GAP 0)
\end{spec}
Now prove commutativity of multiplication. (You will probably need to define and prove a 
separate subsidiary theorem to be used in the proof of this one.) You may find that 
|plusSwap| comes in handy.
\begin{spec}
multComm : forall (n m : Nat) -> n * m == m * n
multComm = (HOLE GAP 0)
\end{spec}
\end{exe}

\begin{exe}[even |n| implies odd |suc n|]
Prove the following simple fact:
\begin{spec}
evenNoddSucN : forall (n : Nat) -> evenb n == not (oddb (suc n))
evenNoddSucN = (HOLE GAP 0)
\end{spec}
\end{exe}

\section{More Exercices}

\begin{exe}
Take a piece of paper. For each of the following theorems, first think about whether (a) 
it can be proved using only simplification and rewriting, (b) it also requires case analysis, 
or (c) it also requires induction. Write down your prediction. Then fill in the proof. 
(There is no need to turn in your piece of paper; this is just to encourage you to reflect before hacking!)

\begin{spec}
bleNatRefl : forall (n : Nat) -> True == bleNat n n
bleNatRefl =  (HOLE GAP 0)

zeroNbeqSuc : forall (n : Nat) -> beqNat 0 (suc n) == False
zeroNbeqSuc =  (HOLE GAP 1)

andFalseR : forall (b : Bool) -> and b False == False
andFalseR =  (HOLE GAP 2)

plusBleCompatL : forall (n m p : Nat) -> bleNat n m == True -> 
                 bleNat (p + n) (p + m) == True
plusBleCompatL =  (HOLE GAP 3)

sucNBeq0 : forall (n : Nat) -> beqNat (suc n) zero == False
sucNBeq0 =  (HOLE GAP 4)

mult1L : forall (n : Nat) -> 1 * n == n
mult1L =  (HOLE GAP 5)

all3Spec : forall (b c : Bool) -> or (and b c) (or (not b) (not c)) == True
all3Spec =  (HOLE GAP 6)

multPlusDistrR : forall (n m p : Nat) -> (n + m) * p == (n * p) + (m * p)
multPlusDistrR =  (HOLE GAP 7)

multAssoc : forall (n m p : Nat) -> n * (m * p) == (n * m) * p
multAssoc =  (HOLE GAP 8)

beqNatRefl : forall (n : Nat) -> True == beqNat n n
beqNatRefl = (HOLE GAP 9)
\end{spec}
\end{exe}

\section{Equational Reasoning}\label{equational-reasoning}

Agda's supports for mixfix operators offers an excellent oportunity for creating
operators that can resamble pencil-and-paper style of reasoning. In this section
we will see how to use support for equational reasoning to construct a proof for
commutativity of addition for natural numbers.

NOTE: I belive that here would be nice to talk a bit about the usage of equational
reasoning proofs. Latter, in another chapter, talk about propositional equality and
some functions over it.
