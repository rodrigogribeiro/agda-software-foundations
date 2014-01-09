\chapter{Logic in Agda}

Agda's built-in logic is very small: the only primitives are data type definitions, 
universal quantification (|forall|), and implication (|->|), while all the other familiar 
logical connectives --- conjunction, disjunction, negation, existential quantification, 
even equality --- can be encoded using just these.
This chapter explains the encodings and explain with some details how equality works in Agda.

%if False
\begin{code}
module Logic where

open import Basics hiding (_*_;_+_)
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

We can pattern match on a conjunction in order to extract one of its components, as in the following example:
\begin{code}
andElimL : forall {A B : Set} -> A * B -> A
andElimL (a , b) = a

andElimR : forall {A B : Set} -> A * B -> B
andElimR (a , b) = b
\end{code}

\begin{exe}
Prove that conjunction is commutative:
\begin{spec}
andComm : forall {A B : Set} -> A * B -> B * A
andComm = (HOLE GAP 0)
\end{spec}
\end{exe}

\begin{exe}
Prove that conjunction is associative:
\begin{spec}
andAssoc : forall {A B C : Set} -> A * (B * C) -> (A * B) * C
andAssoc = (HOLE GAP 0)
\end{spec}
\end{exe}

\subsection{If and only if}

The handy ``if and only if'' connective is just the conjunction of two implications.

\begin{code}
_<->_ : forall (A B : Set) -> Set
A <-> B = (A -> B) * (B -> A)

iffImplies : forall {A B : Set} -> A <-> B -> A -> B
iffImplies (p , q) = p

iffSym : forall {A B : Set} -> A <-> B -> B <-> A
iffSym (p , q) = q , p
\end{code}

\begin{exe}
Using the proof that |<->| is symmetric (|iffSym|) as a guide,
prove that it is also reflexive e transitive.
\begin{spec}
iffRefl : forall (A : Set) -> A <-> A
iffRefl = (HOLE GAP 0)

iffTrans : forall (A B C : Set) -> A <-> B -> B <-> C -> A <-> C
iffTrans = (HOLE GAP 0)
\end{spec}
\end{exe}


\section{Disjunction}

Disjunction ("logical or") can also be defined as an data type.

\begin{code}
data _+_ (A B : Set) : Set where
  inl : A -> A + B
  inr : B -> A + B
\end{code}

Intuitively, there are two ways of giving evidence for |A + B|:
\begin{itemize}
  \item give evidence for |A| (and say that it is |A| you are giving evidence for 
        --- this is the function of the |inl| constructor), or
  \item give evidence for |B|, tagged with the |inr| constructor.
\end{itemize}

Since |A + B| has two constructors, doing pattern matching on a parameter of its type 
will need to two equations.

\begin{code}
orComm : forall {A B : Set} -> A + B -> B + A
orComm (inl p) = inr p
orComm (inr q) = inl q

orDistrAnd' : forall {A B C : Set} -> A + (B * C) -> (A + B) * (A + C)
orDistrAnd' (inl p)       = inl p , inl p
orDistrAnd' (inr (p , q)) = inr p , inr q
\end{code}

\begin{exe}
Prove the following theorem:
\begin{spec}
orDistrAnd : forall {A B C : Set} -> A + (B * C) <-> (A + B) * (A + C)
orDistrAnd = (HOLE GAP 0)
\end{spec}
\end{exe}

\subsection{Relating |+| and |*| with |or| and |and|}

We've already seen several places where analogous structures can be found in 
Agda's computational (expressions) and logical (types --- Set terms) worlds. Here is one more: 
the boolean operators |and| and |or| are clearly analogs of the types |*| and |+|. 
This analogy can be made more precise by the following theorems, which show how to translate 
knowledge about |and| and |or|'s behaviors on certain inputs into propositional facts about those inputs.

\begin{code}
andbProp : forall b c -> and b c == True -> (b == True) * (c == True)
andbProp True .True refl = refl , refl
andbProp False c ()

andTrueIntro : forall b c -> (b == True) * (c == True) -> and b c == True
andTrueIntro True .True (refl , refl) = refl
andTrueIntro False _    (()   , _   )
\end{code}

\begin{exe}
Prove the following theorems:
\begin{spec}
andBFalse : forall b c -> and b c == False -> (b == False) + (c == False)
andBFalse = (HOLE GAP 0)

orBTrue : forall b c -> or b c == True -> (b == True) + (c == True)
orBTrue = (HOLE GAP 0)

orBFalseElim : forall b c -> or b c == False = (b == False) * (c == False)
orBFalseElim = (HOLE GAP 0)
\end{spec}
\end{exe}

\section{Falsehood}

Logical falsehood can be represented in Agda as an data type with no constructors.

\begin{code}
data Empty : Set where
\end{code}
Intuition: |Empty| is a proposition for which there is no way to give evidence.

Since |Empty| has no constructors, pattern matching an assumption of type |Empty| 
always yields zero subgoals, allowing us to immediately prove any goal.
\begin{code}
falseImpliesNonSense : Empty -> 2 == 3
falseImpliesNonSense ()
\end{code}
Actually, since the proof of |falseImpliesNonSense| doesn't actually have anything 
to do with the specific nonsensical thing being proved; it can easily be generalized 
to work for an arbitrary |A|:
\begin{code}
emptyElim : forall {A : Set} -> Empty -> A
emptyElim ()
\end{code}
This function encodes the principle \textit{ex falso quodlibet} means, literally, 
``from falsehood follows whatever you please.'' This theorem is also known as 
the \textit{principle of explosion}.

\subsection{Truth}

Since we have defined falsehood in Agda, one might wonder whether it is possible to 
define truth in the same way. We can.
\begin{code}
data Unit : Set where
  unit : Unit
\end{code}
Truth is represented as a type with a unique inhabitant, with evidence |unit|.
However, unlike |Empty|, which we'll use extensively, |Unit| is used fairly 
rarely. By itself, it is trivial (and therefore uninteresting) to prove as a 
goal, and it carries no useful information as a hypothesis. But it can be 
useful when defining complex types using conditionals, or as a parameter to higher-order types.


\section{Negation}

The logical complement of a proposition |A| is written |~A|:
\begin{code}
~_ : (A : Set) -> Set
~ A = A -> Empty
\end{code}
The intuition is that, if |A| is not true, then anything at all 
(even |Empty|) follows from assuming |A|.

Unlike Coq, Agda automatically expands |~ A| definition in holes,
so, there's no special tactic to ``unfold'' definitions like negation.

\begin{exe}
Prove the following facts:
\begin{spec}
doubleNeg : forall A -> A -> ~ ~ A
doubleNeg = (HOLE GAP 0)

contrapositive : forall A B -> (A -> B) -> (~ B -> ~ A)
contrapositive = (HOLE GAP 1)
\end{spec}
\end{exe}

\subsection{Inequality}

Saying |x /= y| is just the same as saying |~(x == y)|.
\begin{code}
_/=_ : {A : Set} (x y : A) -> Set
x /= y = ~ (x == y)
\end{code}
Since inequality involves a negation, it again requires a little practice to be able 
to work with it fluently. Here is one very useful trick. If you are trying to prove a 
goal that is nonsensical (e.g., the goal state is |False == True|, apply the lemma 
|emptyElim| to change the goal to |Empty|. This makes it easier to use assumptions 
of the form |~ P| that are available in the context --- in particular, assumptions 
of the form |x /= y|.
\begin{code}
notFalseThenTrue : forall b -> b /= False -> b == True
notFalseThenTrue True p = refl
notFalseThenTrue False p = emptyElim (p refl)
\end{code}

\begin{exe}
Prove the following theorems:
\begin{spec}
falseBeqNat : forall (n m : Nat) -> n /= m -> beqNat n m == False
falseBeqNat = (HOLE GAP 0)

beqNatFalse : forall (n m : Nat) -> beqNat n m == False -> n /= m
beqNatFalse = (HOLE GAP 1)

beqLeFalse : forall (n m : Nat) -> bleNat n m == False -> ~ (n <= m)
beqLeFalse = (HOLE GAP 2)
\end{spec}
\end{exe}

\section{Existential Quantification}


