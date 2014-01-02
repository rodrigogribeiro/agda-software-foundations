\chapter{Propositions and Evidence}

In previous chapters, we have seen many examples of factual claims (propositions) 
and ways of presenting evidence of their truth (proofs). In particular, we have 
worked extensively with equality propositions of the form $e = e'$, with implications 
$P \to Q$, and with quantified propositions $\forall x. P(x)$.

This chapter will take us on a first tour of the propositional (logical) side of Agda. 
In particular, we will expand our repertoire of primitive propositions to include user-defined propositions, 
not just equality propositions.

%if False
\begin{code}
module Propositions where

open import Basics
open import Poly
--open import MoreAgda
\end{code}
%endif

\section{Inductively Defined Propositions}

As a running example, let's define a simple property of natural numbers — we'll call it ``beautiful.''
Informally, a number is \textit{beautiful} if it is 0, 3, 5, or the sum of two \textit{beautiful numbers}.
More pedantically, we can define beautiful numbers by giving four rules:
\begin{itemize}
  \item Rule $b_0$: The number 0 is beautiful.
  \item Rule $b_3$: The number 3 is beautiful.
  \item Rule $b_5$: The number 5 is beautiful.
  \item Rule $b_{sum}$: If n and m are both beautiful, then so is their sum.
\end{itemize}
We will see many definitions like this one during the rest of the course, and for purposes of 
informal discussions, it is helpful to have a lightweight notation that makes them easy to read and write. 
Inference rules are one such notation:
\[
  \begin{array}{c}
    \infer[(b_0)]
      {\textit{beautiful } 0}
      {}
      \\
      \\
    \infer[(b_3)]
      {\textit{beautiful } 3} 
      {}
      \\
      \\
    \infer[(b_5)]
      {\textit{beautiful } 5} 
      {}
      \\
      \\
    \infer[(b_{sum})]
      {\textit{beautiful } (n+m)}
      {\textit{beautiful } n & \textit{beautiful } m}
  \end{array}
\]
Each of the textual rules above is reformatted here as an inference rule; the intended reading is that, 
if the premises above the line all hold, then the conclusion below the line follows. For example, the 
rule $b_{sum}$ says that, if $n$ and $m$ are both beautiful numbers, then it follows that $n+m$ is 
beautiful too. If a rule has no premises above the line, then its conclusion hold unconditionally.

These rules define the property beautiful. That is, if we want to convince someone that some particular 
number is beautiful, our argument must be based on these rules. For a simple example, suppose we claim 
that the number 5 is beautiful. To support this claim, we just need to point out that rule $b_5$ says so. 
Or, if we want to claim that 8 is beautiful, we can support our claim by first observing that 3 and 5 are 
both beautiful (by rules $b_3$ and $b_5$) and then pointing out that their sum, 8, is therefore beautiful 
by rule $b_{sum}$. This argument can be expressed graphically with the following proof tree:
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
In Agda we can express the property \textit{beautiful} as an inductive data type:
\begin{code}
data Beautiful : Nat -> Set where
   b0   : Beautiful 0
   b3   : Beautiful 3
   b5   : Beautiful 5
   bsum : forall {n m} -> Beautiful n -> Beautiful m -> Beautiful (n + m)
\end{code}
The first line declares that beautiful is a type, or more formally a family of types ``indexed by'' natural numbers. 
(That is, for each number n, the claim that ``n is beautiful'' is a type.). Such a family of types
is often called a property of numbers. Each of the remaining lines embodies one of the rules for beautiful numbers.

As you would expect, we can also prove theorems that have hypotheses about beautiful.

\begin{code}
beautifulPlus8 : forall {n} -> Beautiful n -> Beautiful (8 + n)
beautifulPlus8 p = bsum (bsum b3 b5) p
\end{code}

\begin{exe}
Prove the following fact about beautiful numbers:
\begin{spec}
beautifulTimes : forall {n m} -> Beautiful n -> Beautiful (m * n)
beautifulTimes = (HOLE GAP 0)
\end{spec}
\end{exe}

\subsection{Induction Over Evidence}

Besides constructing evidence that numbers are beautiful, we can also reason about such evidence.
The fact that we introduced beautiful with an data type declaration tells Agda not only that the 
constructors $b_0$, $b_3$, $b_5$ and $b_{sum}$ are ways to build evidence, but also that these two constructors 
are the only ways to build evidence that numbers are beautiful.
In other words, if someone gives us evidence $E$ for the assertion \textit{beautiful} $n$, then we know that $E$ 
must have one of four shapes:

\begin{itemize}
  \item $E$ is $b_0$ (and $n$ is $O$),
  \item $E$ is $b_3$ (and $n$ is $3$),
  \item $E$ is $b_5$ (and $n$ is $5$),
  \item $E$ is $b_{sum}$ $n_1$ $n_2$ $E_1$ $E_2$ (and $n$ is $n1+n2$, where $E_1$ is evidence that $n_1$ is 
         beautiful and $E_2$ is evidence that $n_2$ is beautiful).
\end{itemize}

This permits us to analyze any hypothesis of the form \textit{beautiful} $n$ to see how it was constructed, 
using pattern matching. In particular, we can use the advanced features of Agda's pattern matching mechanism
to analyse inductive properties.

To illustrate this, let's define another property of numbers:

\begin{code}
data Gorgeous : Nat -> Set where
  g0 : Gorgeous 0
  g3 : forall {n} -> Gorgeous n -> Gorgeous (3 + n)
  g5 : forall {n} -> Gorgeous n -> Gorgeous (5 + n)
\end{code}

\begin{exe}
Prove the following fact:
\begin{spec}
gorgeousPlus13 : forall {n} -> Gorgeous n -> Gorgeous (13 + n)
gorgeousPlus13 = (HOLE GAP 0)
\end{spec}
\end{exe}
It seems intuitively obvious that, although gorgeous and beautiful are presented using 
slightly different rules, they are actually the same property in the sense that they are 
true of the same numbers. Indeed, we can prove this.
\begin{code}
gorgeousBeautiful : forall {n} -> Gorgeous n -> Beautiful n
gorgeousBeautiful g0 = b0
gorgeousBeautiful (g3 p) = bsum b3 (gorgeousBeautiful p)
gorgeousBeautiful (g5 p) = bsum b5 (gorgeousBeautiful p)
\end{code}
Let's see what happens if we try to prove this by induction on $n$ instead of induction 
on the evidence |Gorgeous n|.
\begin{spec}
gorgeousBeautiful' : forall n -> Gorgeous n -> Beautiful n
gorgeousBeautiful' zero p = b0
gorgeousBeautiful' (suc n) p = (HOLE GAP 0)
\end{spec}
The problem here is that doing induction on n doesn't yield a useful induction hypothesis. 
Knowing how the property we are interested in behaves on the predecessor of $n$ doesn't help 
us prove that it holds for $n$. Instead, we would like to be able to have induction hypotheses 
that mention other numbers, such as $n - 3$ and $n - 5$. This is given precisely by the shape 
of the constructors for gorgeous.
\begin{exe}
Prove the following fact:
\begin{spec}
gorgeousSum : forall {n m} -> Gorgeous n -> Gorgeous m -> Gorgeous (n + m)
gorgeousSum = (HOLE GAP 0)
\end{spec}
\end{exe}

\begin{exe}
Prove the following fact:
\begin{spec}
beautifulGorgeous : forall {n} -> Beautiful n -> Gorgeous n
beautifulGorgeous = (HOLE GAP 0)
\end{spec}
\end{exe}

\subsection{From Boolean Functions to Propositions}

In chapter Basics we defined a function |evenb| that tests a number for evenness, 
yielding |True| if so. We can use this function to define the type that some number |n| is even:
\begin{code}
even : Nat -> Set
even n = evenb n == True
\end{code}
That is, we can define ``n is even'' to mean ``the function |evenb| returns |True| when applied to |n|.''

Note that here we have defined a type just as a function! Since, in Agda, types are first class values, we
can create types dynamically. This isn't a fundamentally a new type; it is still just an equality.

Another alternative is to define the concept of evenness directly. Instead of going via the |evenb| function 
(``a number is even if a certain computation yields true''), we can say what the concept of evenness means by 
giving two different ways of presenting evidence that a number is even.
\begin{code}
data Ev : Nat -> Set where
  ev0  : Ev 0
  evss : forall {n} -> Ev n -> Ev (suc (suc n))
\end{code}
This definition says that there are two ways to give evidence that a number m is even. First, 0 is even, and 
|ev0| is evidence for this. Second, if |m = suc (suc n)| for some |n| and we can give evidence |e| that |n| is 
even, then |m| is also even, and |evss e| is the evidence.
\begin{exe}
Prove the following fact:
\begin{spec}
doubleEven : forall n -> Ev (double n)
doubleEven = (HOLE GAP 0)
\end{spec}
\end{exe}

\subsection{Discussion: Computational vs. Inductive Definitions}

We have seen that the proposition ``n is even'' can be phrased in two different ways --- indirectly, via a 
boolean testing function |evenb|, or directly, by inductively describing what constitutes evidence for evenness. 
These two ways of defining evenness are about equally easy to state and work with. Which we choose is basically 
a question of taste.

However, for many other properties of interest, the direct inductive definition is preferable, since writing a 
testing function may be awkward or even impossible.

One such property is beautiful. This is a perfectly sensible definition of a set of numbers, but we cannot translate 
its definition directly into a Agda recursive function. We might be able to find a clever way of testing this 
property using a function (indeed, it is not too hard to find one in this case), but in general this could require 
arbitrarily deep thinking. In fact, if the property we are interested in is uncomputable, then we cannot define 
it as a function no matter how hard we try, because Agda requires that all functions correspond to terminating computations.

On the other hand, writing an inductive definition of what it means to give evidence for the property beautiful is straightforward.

Here is a proof that the inductive definition of evenness implies the computational one.

\begin{code}
evEven : forall {n} -> Ev n -> even n
evEven ev0 = refl
evEven (evss p) = evEven p
\end{code}

\begin{exe}
Prove the following fact:
\begin{spec}
evSum : forall {n m} -> Ev n -> Ev m -> Ev (n + m)
evSum = (HOLE GAP 0)
\end{spec}
\end{exe}

\subsection{Pattern Matching on Evidence}

Another situation where we want to analyze evidence for evenness is when proving that, 
if n is even, then pred (pred n)) is too. In this case, all we need is pattern matching:
\begin{code}
evMinus2 : forall {n} -> Ev n -> Ev (pred (pred n))
evMinus2 ev0 = ev0
evMinus2 (evss e) = e
\end{code}

Another example, in which pattern matching helps narrow down to the relevant cases.
\begin{code}
evSSEven : forall {n} -> Ev (suc (suc n)) -> Ev n
evSSEven (evss e) = e
\end{code}

\begin{exe}
Finding the appropriate thing to do induction on is a bit tricky here:
\begin{spec}
sumEv : forall {n m} -> Ev (n + m) -> Ev n -> Ev m
sumEv = (HOLE GAP 0)
\end{spec}
\end{exe}

\begin{exe}
Here's an exercise that just requires applying existing lemmas. No induction 
or even case analysis is needed, but some of the rewriting may be tedious.
\begin{spec}
evPlusPlus : forall {n m p} -> Ev (n + m) -> Ev (n + p) -> Ev (m + p)
evPlusPlus = (HOLE GAP 0)
\end{spec}
\end{exe}


\section{Additional Exercises}

\begin{exe}[Palindromes]
A palindrome is a sequence that reads the same backwards as forwards.
\begin{enumerate}
  \item Define an inductive type |Palindrome| indexed by |List A| that captures what it means to be a palindrome.
        (Hint: You'll need three cases. Your definition should be based on the structure of the list; just having
         a single constructor |c : forall l -> l == rev l -> Palindrome l| may seem obvious, but will not work very well.)
  \item Prove that |forall l -> Palindrome (l ++ rev l)|
  \item Prove that |forall l -> Palindrome l -> l == rev l| 
\end{enumerate}
\end{exe}

\begin{exe}[Subsequences]
A list is a subsequence of another list if all of the elements in the first list occur in the same order in the 
second list, possibly with some extra elements in between. For example,
|(1 , 2 , 3, nil)|
is a subsequence of each of the lists
    |(1 , 2 , 3 , nil)|
    |(1 , 1 , 1 , 2 , 2 , 3 , nil)|
    |(1 , 2 , 7 , 3 , nil)|
    |(5 , 6 , 1 , 9 , 9 , 2 , 7 , 3 , 8 , nil)|
but it is not a subsequence of any of the lists
    |(1 , 2 , nil)|
    |(1 , 3 , nil)|
\begin{enumerate}
  \item Define an inductive proposition |SubSeq| on |List Nat| that captures what it means to be a subsequence. 
        (Hint: You'll need three cases.)
  \item Prove that for any lists |l_1|, |l_2|, and |l_3|, if |l_1| is a subsequence of |l_2|, then |l_1| is also a subsequence of |l_2 ++ l_3|.
  \item Prove that subsquence is a transitive relation on lists.
\end{enumerate}
\end{exe}
