\chapter{More About Agda}

This chapter introduces some features involving Agda's pattern matching mechanism that, 
together, allow us to prove many more theorems about the functional programs we are writing.


%if False
\begin{code}
module MoreAgda where

open import Basics hiding (_*_)
open import Lists hiding (rev; length;snoc)
open import Poly
\end{code}
%endif

\section{Using Hypothesis and Theorems}

We often encounter situations where the goal to be proved is exactly the same as some 
hypothesis in the context or some previously proved lemma.
\begin{code}

Eq : {l : Level}(A : Set l) -> A -> A -> Set l
Eq {l} A x y = _==_ {l} {A} x y

NListEq : List Nat -> List Nat -> Set
NListEq l1 l2 = Eq (List Nat) l1 l2

Silly1 : (n o m p : Nat) -> Set
Silly1 n o m p = n == m -> t1 -> t2 
                where 
                  t1 = NListEq (n , o , nil) (n , p , nil)
                  t2 = NListEq (n , o , nil) (m , p , nil)


silly1 : forall (n m o p : Nat) -> Silly1 n o m p
silly1 n m o p nm rewrite nm = id
\end{code}                                          


\begin{code}
Hyp : Nat -> Nat -> Set
Hyp o p = forall (q r : Nat) -> q == r -> t q r
          where
            t : Nat -> Nat -> Set
            t q r = NListEq (q , o , nil) (r , p , nil)

Silly2 : (n m o p : Nat) -> Set
Silly2 n m o p = n == m -> Hyp o p -> t
               where
                 t = NListEq (n , o , nil) (m , p , nil)

silly2 : forall (n m o p : Nat) -> Silly2 n m o p
silly2 n m o p nm hyp = hyp n m nm
\end{code}


\begin{code}
NPairEq : (n m o p : Nat) -> Set
NPairEq n m o p = Eq (Nat * Nat) (n , m) (o , p)

Hyp2a : Set
Hyp2a = forall (q r : Nat) -> NPairEq q q r r -> NListEq (q , nil) (r , nil)

Silly2a : Nat -> Nat -> Set
Silly2a n m = NPairEq n n m m -> Hyp2a -> NListEq (n , nil) (m , nil)

silly2a : forall (n m : Nat) -> Silly2a n m
silly2a .m m refl hyp = refl
\end{code}

The next is a exercice

\begin{code}
SillyEx : Set
SillyEx = forall (n : Nat) -> evenb n == True -> oddb (suc n) == True

sillyEx : SillyEx -> evenb 3 == True -> oddb 4 == True
sillyEx silly = silly (suc (suc (suc zero)))
\end{code}

\begin{code}
silly3 : forall (n : Nat) -> True == beqNat n 5 -> beqNat (suc (suc n)) 7 == True
silly3 n = sym
\end{code}

Another exercice. Need revInvolutive property.

\begin{code}
revExercice1 : forall (l l' : List Nat) -> l == rev l' -> l' == rev l
revExercice1 l l' = {!!}
\end{code}

These next examples are used to justify the apply with tactic.

\begin{code}
transEqExample : forall (a b c d e f : Nat) -> NListEq (a , b , nil) (c , d , nil) ->
                                               NListEq (c , d , nil) (e , f , nil) ->
                                               NListEq (a , b , nil) (e , f , nil)
transEqExample a b .a .b .a .b refl refl = refl
\end{code}

Now, using |trans|.

\begin{code}
transEqExample' : forall (a b c d e f : Nat) -> NListEq (a , b , nil) (c , d , nil) ->
                                                NListEq (c , d , nil) (e , f , nil) ->
                                                NListEq (a , b , nil) (e , f , nil)
transEqExample' a b c d e f eq1 eq2 = trans eq1 eq2
\end{code}

\section{Inversion}

Explanation. Pattern matching and emacs mode rocks.

\begin{code}
eqAddSuc : forall {n m : Nat} -> suc n == suc m -> n == m
eqAddSuc refl = refl
\end{code}

\begin{code}
silly4 : forall (n m : Nat) -> NListEq (n , nil) (m , nil) -> n == m
silly4 .m m refl = refl
\end{code}

\begin{code}
silly5 : forall (n m o : Nat) -> NListEq (n , m , nil) (o , o , nil) -> NListEq (n , nil) (m , nil)
silly5 .o .o o refl = refl
\end{code}

now starts sillyex1. Need to explain absurd patterns.

\begin{code}
sillyex1 : forall {l}(A : Set l)(x y z : A)(l j : List A) -> Eq (List A) (x , y , l) (z , j) ->
                                                             Eq (List A) (y , l) (x , j)     ->
                                                             x == y
sillyex1 A .z y z l1 .(y , l1) refl ()
\end{code}

\begin{code}
silly6 : forall (n : Nat) -> suc n == 0 -> 2 + 2 == 5
silly6 n ()

silly7 : forall (n m : Nat) -> True == False -> NListEq (n , nil) (m , nil)
silly7 n m ()
\end{code}

silly ex2

\begin{code}
sillyex2 : forall {l}{A : Set l}(x y z : A)(l j : List A) -> 
           Eq (List A) (x , y , l) nil -> 
           Eq (List A) (y , l) (z , j) -> 
           x == z
sillyex2 x y z l j ()
\end{code}

\begin{spec}
cong : forall {A B : Set} (f : A -> B){x y : A} -> x == y -> f x == f y
cong f {x} {.x} refl = refl
\end{spec}

\begin{code}
lengthSnoc' : forall {A : Set}(v : A)(l : List A)(n : Nat) -> 
              length l == n -> length (snoc v l) == suc n
lengthSnoc' v nil n h1 = cong suc h1
lengthSnoc' v (x , l) zero () 
lengthSnoc' v (x , l) (suc n) p = cong suc (lengthSnoc' v l n (eqAddSuc p))
\end{code}

\begin{code}
beqNat0L : forall (n : Nat) -> beqNat 0 n == True -> n == 0
beqNat0L zero refl = refl
beqNat0L (suc n) ()

beqNat0R : forall (n : Nat) -> beqNat n 0 == True -> n == 0
beqNat0R zero refl = refl
beqNat0R (suc n) ()
\end{code}


\section{Using Tactics on Hypothesis}

\begin{code}
sucInj : forall (n m : Nat)(b : Bool) -> beqNat (suc n) (suc m) == b -> beqNat n m == b
sucInj n m b p = p
\end{code}


\begin{code}
Silly3' : Nat -> Set
Silly3' n = (beqNat n 5 == True -> beqNat (suc (suc n)) 7 == True) ->
            True == beqNat n 5 -> True == beqNat (suc (suc n)) 7

silly3' : forall (n : Nat) -> Silly3' n
silly3' n h p = p
\end{code}

an exercice

\begin{code}
plusNSucM : forall (n m : Nat) -> suc (n + m) == n + suc m
plusNSucM = {!!}

plusInjNN : forall (n m : Nat) -> n + n == m + m -> n == m
plusInjNN zero zero p = refl
plusInjNN zero (suc m) () 
plusInjNN (suc n) zero () 
plusInjNN (suc n) (suc m) p rewrite (sym (plusNSucM n n)) | (sym (plusNSucM m m)) 
               = cong suc (plusInjNN n m (eqAddSuc (eqAddSuc p)))
\end{code}

\section{Varying the Induction Hypothesis}

\begin{code}

double : Nat -> Nat
double zero = zero
double (suc n) = suc (suc (double n))

doubleInj : forall (n m : Nat) -> double n == double m -> n == m
doubleInj zero zero h = refl
doubleInj zero (suc m) () 
doubleInj (suc n) zero () 
doubleInj (suc n) (suc m) h = cong suc (doubleInj _ _ (eqAddSuc (eqAddSuc h)))
\end{code}

exercice

\begin{code}
beqNatTrue : forall (n m : Nat) -> beqNat n m == True -> n == m
beqNatTrue zero zero h = refl
beqNatTrue zero (suc m) ()
beqNatTrue (suc n) zero ()
beqNatTrue (suc n) (suc m) h = cong suc (beqNatTrue n m h)
\end{code}
