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

%if False
\begin{code}
{-# BUILTIN NATURAL  Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC  suc #-}
\end{code}
%endif

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

_/=_ : forall {l}{A : Set l} -> A -> A -> Set l
x /= y = ~ (x == y)

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

\subsection{Predicates Over Natural Numbers}

\subsubsection{Evenness}

\begin{code}
data Ev : Nat -> Set where
  ev0 : Ev 0
  evs : forall {n : Nat} -> Ev n -> Ev (suc (suc n))
\end{code}

\subsubsection{Ordering}

\begin{code}
data _<=_ : Nat -> Nat -> Set where
  le0 : forall (n : Nat) -> 0 <= n
  leS : forall (n m : Nat) -> n <= m -> n <= suc m

data _<='_ : Nat -> Nat -> Set where
  leN  : forall (n : Nat) -> n <=' n
  leS' : forall (n m : Nat) -> n <=' m -> n <=' suc m

_<_ : Nat -> Nat -> Set 
n < m = n <= m * n /= m

_<'_ : Nat -> Nat -> Set
n <' m = n <=' m * n /= m
\end{code}

\begin{code}
data _>=_ : Nat -> Nat -> Set where
  ge0 : forall (n : Nat) -> n >= 0
  geS : forall (n m : Nat) -> n >= m -> suc n >= m

data _>='_ : Nat -> Nat -> Set where
  geN  : forall (n : Nat) -> n >=' n
  geS' : forall (n m : Nat) -> n >=' m -> suc n >=' m

_>_ : Nat -> Nat -> Set 
n > m = n >= m * n /= m

_>'_ : Nat -> Nat -> Set
n >' m = n >=' m * n /= m
\end{code}

\subsection{Some Useful Lemmas}

\begin{code}
andTrueElim : forall (b c : Bool) -> and b c == True -> (b == True) * (c == True)
andTrueElim False False ()
andTrueElim False True ()
andTrueElim True False ()
andTrueElim True True refl = refl , refl

beqNatSym : forall (n m : Nat) -> beqNat n m == beqNat m n
beqNatSym zero zero = refl
beqNatSym zero (suc m) = refl
beqNatSym (suc n) zero = refl
beqNatSym (suc n) (suc m) = beqNatSym n m

eqNatDec : forall (x y : Nat) -> (x == y) + (x /= y)
eqNatDec zero zero = inl refl
eqNatDec zero (suc y) = inr (\ ())
eqNatDec (suc x) zero = inr (\ ())
eqNatDec (suc x) (suc y) with eqNatDec x y 
eqNatDec (suc .y) (suc y) | inl refl = inl refl
eqNatDec (suc x) (suc y) | inr r = inr (λ ctr → r (inv x y ctr)) where
                         inv : forall (x y : Nat) -> suc x == suc y -> x == y
                         inv zero zero p = refl
                         inv zero (suc y) () 
                         inv (suc x) zero () 
                         inv (suc .y) (suc y) refl = refl

exFalsum : forall {l}{A : Set l} -> Empty -> A
exFalsum ()

evNotEvS : forall (n : Nat) -> Ev n -> ~ Ev (suc n)
evNotEvS zero p ()
evNotEvS (suc n) p (evs ctr) = evNotEvS n ctr p

<=-refl : forall (n : Nat) -> n <= n
<=-refl zero = le0 zero
<=-refl (suc n) with <=-refl n 
...| r = {!!}

<=-<=' : forall {n m : Nat} -> n <= m -> n <=' m
<=-<=' {.0} {zero} (le0 .0) = leN zero
<=-<=' {.0} {suc m} (le0 .(suc m)) = leS' zero m (<=-<=' (le0 m))
<=-<=' {n} (leS .n m p) = leS' n m (<=-<=' p) 

<='-<= : forall {n m : Nat} -> n <=' m -> n <= m
<='-<= {.m} {m} (leN .m) = {!!}
<='-<= {n} (leS' .n m p) = {!!}

bleNatTrue : forall (n m : Nat) -> bleNat n m == True -> n <= m
bleNatTrue zero zero p = le0 zero
bleNatTrue (suc n) zero ()
bleNatTrue zero (suc m) p = le0 (suc m)
bleNatTrue (suc n) (suc m) p with bleNatTrue n m p 
...| p' = {!!} 
\end{code}
