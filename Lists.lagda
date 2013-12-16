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

\begin{code}
head : NList -> (default : Nat) -> Nat
head <>      d = d
head (x , _) d = x

tail : NList -> NList
tail <>       = <>
tail (_ , xs) = xs
\end{code}

\begin{exe}[Definition of |nonZeros|]
Define the function |nonZeros| that remove all |zero| values from a |NList|. Implement your function
in such a way that |testNonZeros| be a type correct term.
\begin{spec}
nonZeros : NList -> NList
nonZeros = (HOLE GAP 0)

testNonZeros : (0 , 1 , 0 , 2 , 0 , <>) == (1 , 2 , <>)
testNonZeros = refl
\end{spec}
\end{exe}

\begin{exe}[Definition of |oddMembers|]
Define the function |oddMembers| that remove all even values from a |NList|. Implement your function
in such a way that |testOddMembers| be a type correct term.
\begin{spec}
oddMembers : NList -> NList
oddMembers = (HOLE GAP 0)

testOddMembers : (0 , 1 , 0 , 3 , 0 , <>) == (1 , 3 , <>)
testOddMembers = refl
\end{spec}
\end{exe}

\begin{exe}[Definition of |alternate|]
Implement |alternate| that alternates two given |NLists| into one.
\begin{spec}
alternate : NList -> NList -> NList
alternate = (HOLE GAP 0)
\end{spec}
\end{exe}

%if False
This really simple example does not pass throught Coq's termination checker!

\begin{code}
alternate : NList -> NList -> NList
alternate <> l2 = l2
alternate l1 <> = l1
alternate (x , l1) (y , l2) = x , y , alternate l1 l2
\end{code}
%endif

\section{Bag via Lists}

A bag (or multiset) is like a set, but each element can appear multiple times instead of just once. 
One reasonable implementation of bags is to represent a bag of numbers as a list.
\begin{code}
Bag : Set
Bag = NList
\end{code}
Note that |Bag| is explicitly annotated with type |Set|, that is the type of ``types''.
\begin{exe}[Functions over bags]
Complete the following definitions for the functions |count|, |sum|, |add|, and |member| for bags.
Again, implement your functions in a way that the test cases are typeable by Agda.
\begin{spec}
count : Bag -> Bag
count = (HOLE GAP 0)

testCount1 : count 1 (1 , 2 , 1 , <>) == 2
testCount1 = refl

testCount2 : count 3 (1 , 2 , 1 , <>) == 0
testCount2 = refl

sum : Bag -> Nat
sum = (HOLE GAP 0)

testSum : sum (1 , 2 , 1 , <>) == 6
testSum = refl

add : Nat -> Bag -> Bag
add = (HOLE GAP 0)

testAdd : count 1 (add 1 (1 , 2 , 1 , <>)) == 3
testAdd = refl

member : Nat -> Bag -> Bool
member = (HOLE GAP 0)

testMember1 : member 1 (1 , 2 , 1 , <>) == True
testMember1 = refl

testMember2 : member 3 (1 , 2 , 1 , <>) == False
testMember2 = refl
\end{spec}
\end{exe}

\begin{exe}[More |bag| functions]
Here are some more bag functions for you to practice with.
\begin{spec}
removeOne : Nat -> Bag -> Bag
removeOne = (HOLE GAP 0)

testRemoveOne1 : count 1 (removeOne 1 (1 , 2 , 1 , <>)) == 1
testRemoveOne1 = refl

testRemoveOne2 : count 1 (removeOne 1 (1 , 2 , 1 , <>)) == 2
testRemoveOne2 = refl

removeAll : Nat -> Bag -> Bag
removeAll = (HOLE GAP 0)

testRemoveAll : count 1 (removeAll 1 (1 , 2 , 1 , <>)) == 0
testRemoveAll = refl

subset : Bag -> Bag -> Bool
subset = (HOLE GAP 0)

testSubset1 : subset (1 , 2 , <>) (3 , 1 , 2 , <>) == True
testSubset1 = refl

testSubset2 : subset (2 , 3 , <>) (1 , 2 , 4 , <>) == False
testSubset2 = refl
\end{spec}
\end{exe}

\begin{exe}
Write down an interesting theorem about bags involving the functions |count| and |add|, 
and prove it. Note that, since this problem is somewhat open-ended, it's possible that 
you may come up with a theorem which is true, but whose proof requires techniques you 
haven't learned yet. Feel free to ask for help if you get stuck!
\end{exe}

\section{Reasoning about Lists}

Just as with numbers, simple facts about list-processing functions can sometimes be 
proved entirely by simplification. For example, the simplification performed by |refl| 
is enough for this theorem...
\begin{code}
nilAppL : forall (n : NList) -> <> ++ n == n
nilAppL n = refl
\end{code}
... because the |<>| is substituted into the match position in the definition of |++|, 
allowing the match itself to be simplified.

Also, as with numbers, it is sometimes helpful to perform case analysis on the 
possible shapes (empty or non-empty) of an unknown list, as shown in this little theorem:
\begin{code}
tailLengthPred : forall (n : NList) -> pred (length n) == length (tail n)
tailLengthPred <>      = refl
tailLengthPred (x , n) = refl
\end{code}
Usually, though, interesting theorems about lists require induction for their proofs.

\subsection{Micro-sermon}

Simply reading example proofs will not get you very far! It is very important to work 
through the details of each one, using Agda and thinking about what each step of the 
proof achieves. Otherwise it is more or less guaranteed that the exercises will make no sense.

\subsection{Induction on Lists}

Proofs by induction over datatypes like |NList| are perhaps a little less familiar than standard 
natural number induction, but the basic idea is equally simple. Each data type declaration defines 
a set of data values that can be built up from the declared constructors: a boolean can be either 
|True| or |False|; a number can be either |zero| or |suc| applied to a number; a list can be 
either |<>| or |,| applied to a number and a list.

Moreover, applications of the declared constructors to one another are the only possible shapes that 
elements of a inductively defined set can have, and this fact directly gives rise to a way of reasoning 
about inductively defined sets: a number is either |zero| or else it is |suc| applied to some smaller number; a list 
is either |<>| or else it is |,| applied to some number and some smaller list; etc. So, if we have in mind 
some proposition |P| that mentions a list |l| and we want to argue that |P| holds for all lists, we can reason as follows:
\begin{itemize}
  \item First, show that |P| is true of |l| when |l| is |<>|.
  \item Then show that |P| is true of |l| when |l| is |n , l'| for some number |n| and some smaller list |l'|, assuming that 
        |P| is true for |l'|.
\end{itemize}
Since larger lists can only be built up from smaller ones, eventually reaching |<>|, these two things 
together establish the truth of |P| for all lists |l|. Here's a concrete example:
\begin{code}
appAssoc : forall (l1 l2 l3 : NList) -> l1 ++ (l2 ++ l3) == (l1 ++ l2) ++ l3
appAssoc <> l2 l3 = refl
appAssoc (x , l1) l2 l3 = 
    ((x , l1) ++ (l2 ++ l3)) ==[ refl ]
    (x , (l1 ++ (l2 ++ l3))) ==[ cong (\p -> x , p) (appAssoc l1 l2 l3) ]
    (x , ((l1 ++ l2) ++ l3)) 
  QED
\end{code}
Here we use Agda infix operators to do some equational reasoning in proofs, that allow us to argue in a 
pencil and paper fashion. The operator |==[?]| acts like a
equality that uses the term between brackets to rewrite the current term and |QED| finish the proof.

The same proof can be done in the following way, in a paper:

\begin{theorem}
For all |NList|s |l1|, |l2| and |l3|, we have |l1 ++ (l2 ++ l3) == (l1 ++ l2) ++ l3|.
\end{theorem}
\begin{proof}
We will proceed by induction on |l1|.
\begin{enumerate}
  \item Case |l1 = <>|: In this case we have: |<>| $|++| (l2 |++| l3) \equiv l2 |++| l3 \equiv$ $($|<>| $|++| l2) |++| l3$, as required.
  \item Case |l1 = x , l1'|: We have that:
  \begin{center}
  \begin{tabular}{lcl}
    (x , l1') ++ (l2 ++ l3) & $\equiv$ & \{by def.\}\\
    x , (l1' ++ (l2 ++ l3)) & $\equiv$ & \{by I.H.\}\\
    x , ((l1' ++ l2) ++ l3  & $\equiv$ & \{by def.\}\\
    ((x , l1') ++ l2) ++ l3 & $\Box$  
  \end{tabular}
  \end{center}
  as required.
\end{enumerate}
\end{proof}

Here's another simple example:

\begin{code}
appLength : forall (n n' : NList) -> length (n ++ n') == length n + length n'
appLength <> n' = refl
appLength (x , xs) n' = 
    length ((x , xs) ++ n')     ==[ refl ]
    length (x , (xs ++ n'))     ==[ refl ]
    suc (length (xs ++ n'))     ==[ cong suc (appLength xs n') ]
    suc (length xs + length n') ==[ refl ]
    length (x , xs) + length n'
    QED
\end{code}

\begin{exe}[Practice informal proof]
Prove |appLength| theorem using a informal style, like the proof for |appAssoc|.
\end{exe}

For a slightly more involved example of an inductive proof over lists, suppose we define a 
``cons on the right'' function snoc like this...

\begin{code}
snoc : Nat -> NList -> NList
snoc n <> = n , <>
snoc n (x , xs) = x , (snoc n xs)
\end{code}

... and use it to define a list-reversing function |rev| like this:

\begin{code}
rev : NList -> NList
rev <> = <>
rev (x , xs) = snoc x (rev xs)
\end{code}

Now let's prove some more list theorems using our newly defined snoc and rev. For something a 
little more challenging than the inductive proofs we've seen so far, let's prove that 
reversing a list does not change its length. Our first attempt at this proof gets stuck in the successor case...

\begin{spec}
revLength : forall (n : NList) -> length (rev n) == length n
revLength <> = refl
revLength (x , xs) =
      length (rev (x , xs)) ==[ refl ]
      length (snoc x (rev xs)) ==[ (HOLE GAP 0) ]
      suc (length (rev xs))    ==[ (HOLE GAP 1) ]
      suc (length xs)          ==[ (HOLE GAP 2) ]
      length (x , xs)
      QED
\end{spec}

So let's take the equation about snoc that would have enabled us to make progress and prove it as a separate lemma.

\begin{code}
lengthSnoc : forall (n : Nat)(l : NList) -> length (snoc n l) == suc (length l)
lengthSnoc n <> = refl
lengthSnoc n (x , xs) =
      length (snoc n (x , xs)) ==[ refl ]
      length (x , (snoc n xs)) ==[ refl ]
      suc (length (snoc n xs)) ==[ cong suc (lengthSnoc n xs) ]
      suc (length (x , xs))
      QED
\end{code}

Note that we make the lemma as general as possible: in particular, we quantify over all natlists, not just those 
that result from an application of |rev|. This should seem natural, because the truth of the goal clearly doesn't 
depend on the list having been reversed. Moreover, it is much easier to prove the more general property.

Now we can complete the original proof.

\begin{code}
revLength : forall (l : NList) -> length (rev l) == length l
revLength <> = refl
revLength (x , xs) =
      length (rev (x , xs))    ==[ refl ]
      length (snoc x (rev xs)) ==[ lengthSnoc x (rev xs) ]
      suc (length (rev xs))    ==[ cong suc (revLength xs) ]
      suc (length xs)          ==[ refl ]
      length (x , xs)
      QED
\end{code}

\begin{theorem}
For all numbers n and lists l, length (snoc n l) = suc (length l).
\end{theorem}
\begin{proof}
We will proceed by induction |l|.
\begin{itemize}
  \item Caso |l = <>|. We have that:
  \begin{center}
    \begin{tabular}{lcl}
      |length (snoc n <>)| & $\equiv$ & \{by def.\} \\
      |length (n , <>)|    & $\equiv$ & \{by def.\} \\
      |suc zero|           & $\equiv$ & \{by def.\} \\
      |suc (length <>)|
    \end{tabular}
  \end{center}
  as required.
  \item Caso |l = x , xs|. We have that:
  \begin{center}
    \begin{tabular}{lcl}
      |length (snoc n (x , xs))| & $\equiv$ & \{by def.\} \\
      |length (x , snoc n xs) |  & $\equiv$ & \{by def.\} \\
      |suc (length (snoc n xs))| & $\equiv$ & \{by def.\} \\
      |suc (suc (length xs))|    & $\equiv$ & \{by I.H.\} \\
      |suc (length (x , xs))| 
    \end{tabular}
  \end{center}
  as required.
\end{itemize}
\end{proof}

\begin{theorem}
Theorem: For all lists l, length (rev l) = length l.
\end{theorem}
\begin{proof}
We will proceed by induction |l|.
\begin{itemize}
  \item Case |l = nil|. We have that:
  \begin{center}
    \begin{tabular}{lcl}
      |length (rev <>)| & $\equiv$ & \{by def.\} \\
      |length <>|       & $\equiv$ & \{by def.\} \\
      |zero|            & $\equiv$ & \{by def.\} \\
      |length <>|
    \end{tabular}
  \end{center}
  as required.
  \item Case |l = x , xs|. We have that:
  \begin{center}
    \begin{tabular}{lcl}
      length (rev (x , xs)) & $\equiv$ & \{by def.\} \\
      length (snoc x (rev xs)) & $\equiv$ & \{by lengthSnoc\} \\
      suc (length (rev xs)) & $\equiv$ & \{by I.H.\} \\
      suc (length xs)
    \end{tabular}
  \end{center}
  as required.
\end{itemize}
\end{proof}

\subsection{List Exercices, Part 1}

More practice with lists.

\begin{spec}
appNilEnd : forall (l : NList) -> l ++ <> == l
appNilEnd = (HOLE GAP 0)

revInvolutive : forall (l : NList) -> rev (rev l) == l
revInvolutive = (HOLE GAP 1)
\end{spec}

There is a short solution to the next exercise. If you find yourself getting tangled up, 
step back and try to look for a simpler way.

\begin{spec}
appAss4 : forall (l1 l2 l3 l4 : NList) -> l1 ++ (l2 ++ (l3 ++ l4)) == ((l1 ++ l2) ++ l3) ++ l4
appAss4 = (HOLE GAP 0)

snocApp : forall (l : NList) -> snoc n l == l ++ (n , <>)
snocApp = (HOLE GAP 1)

distrRev : forall (l1 l2 : NList) -> rev (l1 ++ l2) == rev l2 ++ rev l1
distrRev = (HOLE GAP 2)

revInjective : forall (l l' : NList) -> rev l == rev l' -> l == l'
revInjective = (HOLE GAP 3)
\end{spec}

\section{Maybe}

Here is another type definition that is often useful in day-to-day programming:
\begin{code}
data NatMaybe : Set where
  Just : Nat -> NatMaybe
  Nothing : NatMaybe
\end{code}
One use of natoption is as a way of returning ``error codes'' from functions. 
For example, suppose we want to write a function that returns the nth element of some list. 
If we give it type |Nat -> NList -> Nat|, then we'll have to return some number when the list is too short!
\begin{code}
indexBad : Nat -> NList -> Nat
indexBad _ <> = 42 -- arbitrary...
indexBad zero (x , xs) = x
indexBad (suc n) (_ , xs) = indexBad n xs
\end{code}
On the other hand, if we give it type |Nat -> NList -> NatMaybe|, then we can return |Nothing| when the 
list is too short and |Just a| when the list has enough members and |a| appears at position |n|.
\begin{code}
index : Nat -> NList -> NatMaybe
index _ <> = Nothing
index zero (x , _) = Just x
index (suc n) (_ , xs) = index n xs
\end{code}

\begin{exe}[Head]
Implement the function |head| from earlier so we don't have to pass a default element for the |<>| case.
\end{exe}

\begin{exe}[Equality of NLists]
Define a function |beqNList| that tests the equality of two given |NList|s and prove the following property:

\begin{spec}
beqNList : forall (l : NList) -> beqNList l l
beqNList = (HOLE GAP 0)
\end{spec}
\end{exe}


