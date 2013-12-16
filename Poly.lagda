\chapter{Polymorphism and High-Order Functions}

In this chapter we continue our development of basic concepts of functional programming. 
The critical new ideas are polymorphism (abstracting functions over the types of the data 
they manipulate) and higher-order functions (treating functions as data).
%if False
\begin{code}
module Poly where

open import Basics
open import Lists
\end{code}
%endif

\section{Polymorphism}

\subsection{Polymorphic Lists}

For the last couple of chapters, we've been working just with lists of numbers. 
Obviously, interesting programs also need to be able to manipulate lists with elements 
from other types --- lists of strings, lists of booleans, lists of lists, etc. 
We could just define a new datatype for each of these, for example...

\begin{code}
data BList : Set where
  nil : BList
  cons : Bool -> BList -> BList
\end{code}
... but this would quickly become tedious, partly because we have to make up different
constructor names for each datatype, but mostly because we would also need to define 
new versions of all our list manipulating functions (|length|, |rev|, etc.) for each new 
datatype definition.

To avoid all this repetition, Agda supports polymorphic type definitions. 
For example, here is a polymorphic list datatype.

\begin{code}
data List (A : Set) : Set where
  nil : List A
  _,_ : A -> List A -> List A
\end{code}

This is exactly like the definition of |NList| from the previous chapter, except that the 
|Nat| argument to the |,| constructor has been replaced by an arbitrary type |A|, a binding for |A| 
has been added to the header, and the occurrences of |NList| in the types of the constructors have 
been replaced by |List A|.

What sort of thing is list itself? One good way to think about it is that list is a function 
from types (|Set|s) to type definitions; or, to put it another way, list is a function from |Set|s to |Set|s. 
For any particular type |A|, the type |List A| is an inductively defined set of lists whose elements are 
things of type |A|.

