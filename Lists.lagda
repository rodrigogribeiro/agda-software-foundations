%if False
\begin{code}
module Lists where
open import Basics
open import InductionProofs
\end{code}
%endif

\chapter{Lists --- Working with Structured Data}\label{lists}

\section{Pairs of Numbers}

In a data type definition, each constructor can take any number of arguments ---
 none (as with |True| and |zero|), one (as with |suc|), or more than one, as in this definition:

\begin{code}
data NatProd : Set where
  _,_ : Nat -> Nat -> NatProd
\end{code}

This declaration can be read: ``There is just one way to construct a pair of numbers: by applying 
the constructor |,| to two arguments of type |Nat|.''

Here are two simple function definitions for extracting the first and second components of a pair. 
(The definitions also illustrate how to do pattern matching on two-argument constructors.)

\begin{code}
fst : NatProd -> Nat
fst (n , _) = n

snd : NatProd -> Nat
snd (_ , n) = n
\end{code}

The |NatProd| ilustrates that, in Agda, we can define infix constructors naturally by marking 
argument positions with underscores.

Let's try and prove a few simple facts about pairs. If we state the lemmas in a particular 
(and slightly peculiar) way, we can prove them with just |refl| (and its built-in simplification):

\begin{code}
surjectivePairing : forall (n m : Nat) -> (n , m) == (fst (n , m) , snd (n , m))
surjectivePairing n m = refl
\end{code}

Another way to state and prove this simple lemma is using pattern matching (case analysis):
\begin{code}
surjectivePairing' : forall (p : NatProd) -> p == (fst p , snd p)
surjectivePairing' (n , m) = refl
\end{code}
Here, in order to be able to state the definitional equality between |p| and  |(fst p , snd p)| we
need to pattern match on |p| in order to Agda be able to reduce functions |fst| and |snd|.

\begin{exe}[Projections and Swap]
First, define a function |swap| which swaps the first and second element of a given pair:
\begin{spec}
swap : NatProd -> NatProd
swap = (HOLE GAP 0)
\end{spec}
Next prove this property:
\begin{spec}
fstSndSwap : forall (p : NatProd) -> (snd p , fst p) == swap p
fstSndSwap = (HOLE GAP 0)
\end{spec}
\end{exe}

\section{List of Numbers}\label{list-of-numbers}

Generalizing the definition of pairs a little, we can describe the type of lists of numbers 
like this: ``A list is either the empty list or else a pair of a number and another list.''

\begin{code}
data NList : Set where
  <>  : NList
  _,_ : Nat -> NList -> NList

infixr 4 _,_
\end{code}

As an example, here we have a simple 3-element list:

\begin{code}
sample : NList 
sample = 1 , 2 , 3 , <>
\end{code}

As you might be an alert reader, Agda supports overloading of data constructors. The context
of a given expression is used to determine of which we are considering.

A number of functions are useful for manipulating lists. For example, the |repeat| function 
takes a number |n| and a |count| and returns a list of length |count| where every element is |n|.

\begin{code}
repeat : Nat -> Nat -> NList
repeat n zero = <>
repeat n (suc m) = n , repeat n m
\end{code}

The |length| function calculates the number of elements of a given list.

\begin{code}
length : NList -> Nat
length <> = zero
length (x , xs) = suc (length xs)
\end{code}

The |++| (``append'') function concatenate two lists:

\begin{code}
infixr 4 _++_

_++_ : NList -> NList -> NList
<> ++ ys = ys
(x , xs) ++ ys = x , (xs ++ ys)
\end{code}

Here are two smaller examples of programming with lists. The |head| function returns 
the first element (the ``head'') of the list, while |tail| returns everything but the 
first element (the ``tail''). Of course, the empty list has no first element, so 
we must pass a default value to be returned in that case.


