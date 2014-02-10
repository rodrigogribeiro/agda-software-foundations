\chapter{Software Foundations Library}

Here we collect together several useful definitions and theorems from Basics.lagda, List.lagda, 
Poly.lagda, Induction.lagda, and Logic.lagda. From now on we can import this file, instead of 
cluttering our environment with all the examples and false starts in those files.

%if False
\begin{code}
module SfLib where
\end{code}
%endif

\section{Universe Levels}

\begin{code}
postulate Level : Set
postulate LZero : Level
postulate LSuc  : Level -> Level
postulate LMax  : Level -> Level -> Level
\end{code}

%if False
\begin{code}
{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO LZero #-}
{-# BUILTIN LEVELSUC LSuc #-}
{-# BUILTIN LEVELMAX LMax #-}
\end{code}
%endif


\section{Propositional Equality}

\begin{code}
data _==_ {l}{A : Set l}(x : A) : A -> Set l where
  refl : x == x

infix 1 _==_ 
\end{code}

%if False
\begin{code}
{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}
\end{code}
%endif

\subsection{Functions Over Equality}

\begin{code}
cong : forall {l l'}{A : Set l}{B : Set l'}(f : A -> B) {x y} -> x == y -> f x == f y
cong f refl = refl

sym : forall {l}{A : Set l}{x y : A} -> x == y -> y == x
sym refl = refl

trans : forall {l}{A : Set l}{x y z : A} -> x == y -> y == z -> x == z
trans refl refl = refl
\end{code}

\subsection{Equational Reasoning}

\begin{code}
infix 2 _QED

_QED : forall {l}{A : Set l}(x : A) -> x == x
x QED = refl

infixr 2 _==[_]_

infix 1 begin

_==[_]_ : forall {l}{A : Set l} (x : A) {y z} -> x == y -> y == z -> x == z
_==[_]_ x xy yz = trans xy yz

begin : forall {l}{A : Set l}{x y : A} -> x == y -> x == y
begin x = x
\end{code}

\section{Booleans}

\begin{code}
data Bool : Set where
  False : Bool
  True  : Bool
\end{code}

\subsection{Functions Over Booleans}

\begin{code}
not : Bool -> Bool
not False = True
not True = False

and : Bool -> Bool -> Bool
and True b = b
and False x = False

or : Bool -> Bool -> Bool
or False b = b
or True b = True

if_then_else : forall {l}{A : Set l} -> Bool -> A -> A -> A
if True then e else e' = e
if False then e else e' = e'
\end{code}

\section{Natural Numbers}

\begin{code}
data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat
\end{code}

\subsection{Functions Over Natural Numbers}

\begin{code}
_+N_ : Nat -> Nat -> Nat
zero +N m  = m
suc n +N m = suc (n +N m)

_*N_ : Nat -> Nat -> Nat
zero *N m = zero
suc n *N m = m +N (n *N m)

infixl 4 _+N_ _*N_

beqNat : Nat -> Nat -> Bool
beqNat zero zero = True
beqNat zero (suc m) = False
beqNat (suc n) zero = False
beqNat (suc n) (suc m) = beqNat n m

bleNat : Nat -> Nat -> Bool
bleNat zero m = True
bleNat (suc n) zero = False
bleNat (suc n) (suc m) = bleNat n m
\end{code}

\section{Logic Constructors}

\subsection{Falsehood, Negation and Truth}

\begin{code}
data Empty : Set where

~_ : forall {l}(A : Set l) -> Set l
~ A = A -> Empty

data Unit : Set where
  unit : Unit
\end{code}

\subsection{Disjunction}

\begin{code}
data _+_ {a b}(A : Set a)(B : Set b) : Set (LMax a b) where
  inl : A -> A + B
  inr : B -> A + B
\end{code}

\subsection{Dependent products}

\begin{code}
infixr 4 _,_ _*_

record Sigma {a b} (A : Set a) (B : A -> Set b) : Set (LMax a b) where
  constructor _,_
  field
    fst : A
    snd : B fst

open Sigma public
\end{code}

\subsection{Conjuntion}

\begin{code}
_*_  : forall {a b}(A : Set a)(B : Set b) -> Set (LMax a b)
A * B = Sigma A (\_ -> B)
\end{code}

\subsection{Existential Quantifier}

\begin{code}
exists : forall {a b}{A : Set a}(B : A -> Set b) -> Set (LMax a b)
exists = Sigma _
\end{code}
