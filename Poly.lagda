\chapter{Polymorphism and High-Order Functions}

In this chapter we continue our development of basic concepts of functional programming. 
The critical new ideas are polymorphism (abstracting functions over the types of the data 
they manipulate) and higher-order functions (treating functions as data).
%if False
\begin{code}
module Poly where

open import Basics hiding (_*_)
open import Lists hiding (length;_++_;snoc;rev;fst;snd;index)
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
data List  {l}(A : Set l) : Set l where
  nil : List A
  _,_ : A -> List A -> List A
\end{code}

This is exactly like the definition of |NList| from the previous chapter, except that the 
|Nat| argument to the |,| constructor has been replaced by an arbitrary type |A|, a binding for |A| 
has been added to the header, and the occurrences of |NList| in the types of the constructors have 
been replaced by |List' A|.

What sort of thing is list itself? One good way to think about it is that list is a function 
from types (|Set|s) to type definitions; or, to put it another way, list is a function from |Set|s to |Set|s. 
For any particular type |A|, the type |List' A| is an inductively defined set of lists whose elements are 
things of type |A|.

We can now go back and make polymorphic (or ``generic'') versions of all the list-processing functions that 
we wrote before. Here is |length|, for example:
\begin{code}
length' : (A : Set) -> List A -> Nat
length' A nil      = zero
length' A (_ , xs) = suc (length' A xs)
\end{code}
Note that the uses of |nil| and |,| in patterns do not require any type annotations: Agda
already knows that the list contains elements of type |A|, so there's no reason to include |A| 
in the pattern. (More precisely, the type |A| is a parameter of the whole definition of list, 
not of the individual constructors. We'll come back to this point later.)

To use our length with other kinds of lists, we simply instantiate it with an appropriate type parameter:
\begin{code}
testLengthBool : length' Bool (True , False , nil) == 2
testLengthBool = refl
\end{code}
Let's close this subsection by re-implementing a few other standard list functions on our new polymorphic lists:
\begin{code}
_++'_ : (A : Set) -> List A -> List A -> List A
_++'_ A nil ys = ys
_++'_ A (x , xs) ys = x , (_++'_ A xs ys)

snoc' : (A : Set) -> A -> List A -> List A
snoc' A x nil = x , nil
snoc' A x (y , ys) = y , (snoc' A x ys)

rev' : (A : Set) -> List A -> List A
rev' A nil = nil
rev' A (x , xs) = snoc' A x (rev' A xs)
\end{code}


\subsection{Type Annotation Inference}

Unlike Coq, in Agda we must provide type annotations for functions, only in very simple and specific cases 
type annotations can be ommited. As an example:
\begin{code}
Age = Nat
\end{code}
Here we are defining that |Age| is a type and we don't need to explicitly write |Age : Set|. But, we cannot
write a list concatenation function without write its type signature. This is rejected by Agda:
\begin{spec}
app' A nil ys = ys
app' A (x , xs) ys = x , (app' A xs ys)
\end{spec}

\subsection{Type Argument Synthesis}

Whenever we use a polymorphic function, we need to pass it one or more types in addition to its other 
arguments. For example, the recursive call in the body of the |length'| function above must pass along 
the type |A|. But just like providing explicit type annotations everywhere, this is heavy and verbose. 
Since the second argument to |length| is a list of |A|s, it seems entirely obvious that the first 
argument can only be |A| --- why should we have to write it explicitly?

Fortunately, Coq permits us to avoid this kind of redundancy. In place of any type argument we can write the 
``implicit argument'' \_, which can be read as ``Please figure out for yourself what type belongs here.'' More 
precisely, when Agda encounters a \_, it will attempt to unify all locally available information --- 
the type of the function being applied, the types of the other arguments, and the type expected by the context in 
which the application appears --- to determine what concrete type should replace the \_.

Using implicit arguments, the |length| function can be written like this
\begin{code}
length1 : (A : Set) -> List A -> Nat
length1 A nil      = zero
length1 A (_ , xs) = suc (length1 _ xs)
\end{code}
In this case we don't need to write much \_, but in some cases this is significant. But, we can do better using
implicit arguments.

\subsection{Implicit Arguments}

To avoid having to sprinkle \_'s throughout our programs, we can tell Agda always to infer the type argument(s) 
of a given function. To this we need just to say that the type parameter of the function is implicit surrounding it
using curly braces:

\begin{code}
length : {A : Set} -> List A -> Nat
length nil      = zero
length (_ , xs) = suc (length xs)
\end{code}

Note that we didn't even have to provide a type argument to the recursive call to |length|; indeed, we can provide it by
surrounding it in curly braces in the pattern and in the recursive call, as follows:
\begin{spec}
length : {A : Set} -> List A -> Nat
length {A} nil      = zero
length {A} (_ , xs) = suc (length {A} xs)
\end{spec}
The |{A}| in the left hand side of the equation is a implicit pattern and we can pattern match on implicit parameters by 
just writing them in curly braces. The same idea is used to pass an implicit parameter as a function argument.

\subsection{Exercises: Polymorphic Lists}

Here are a few simple exercises, just like ones in the Lists chapter, for practice with polymorphism. 
Fill in the definitions and complete the proofs below.
\begin{spec}
repeat : {A : Set}(n : A)(count : Nat) : List A 
repeat = (HOLE GAP 0)

testRepeat : repeat True 2 == True , (True , nil)
testRepeat = refl

_++_ : {A : Set} -> List A -> List A -> List A
nil ++ ys = ys
(x , xs) ++ ys = x , (xs ++ ys)

snoc : {A : Set} -> A -> List A -> List A
snoc x nil = x , nil
snoc x (y , ys) = y , (snoc x ys)

rev : {A : Set} -> List A -> List A
rev nil = nil
rev (x , xs) = snoc' A x (rev' A xs)

nilApp : forall {A : Set}(l : List A) -> [] ++ l == l
nilApp = (HOLE GAP 0)

revSnoc : forall {A : Set}(v : A)(s : List A) -> rev (snoc v s) == v , (rev s)
revSnoc = (HOLE GAP 0)

revInvolutive : forall {A : Set}(l : List A) -> rev (rev l) == l
revInvolutive = (HOLE GAP 0)

snocWithApp : {A : Set}(l1 l2 : List A)(v : A) -> snoc v (l1 ++ l2) == l1 ++ (snoc v l2)
snocWithApp = (HOLE GAP 0)
\end{spec}

\subsection{Polymorphic Pairs}

Following the same pattern, the type definition we gave in the last chapter 
for pairs of numbers can be generalized to polymorphic pairs (or products):
\begin{code}
data _*_ (A B : Set) : Set where
  _,_ : A -> B -> A * B
\end{code}
The first and second projection functions are defined as in any 
functional programming language.
\begin{code}
fst : {A B : Set} -> A * B -> A
fst (x , _) = x

snd : {A B : Set} -> A * B -> B
snd (_ , y) = y
\end{code}
The following function takes two lists and combines them into a list of pairs. 
In Coq, this functions is called \textit{combine}.
\begin{code}
zip : {A B : Set} -> List A -> List B -> List (A * B)
zip nil _ = nil
zip _ nil = nil
zip (x , xs) (y , ys) = (x , y) , zip xs ys
\end{code}

\begin{exe}[Unzip]
The function |unzip| is the right inverse of |zip|: it takes a list of pairs and 
returns a pair of lists. 
\begin{spec}
unzip : {A B : Set} -> List (A * B) -> (List A * List B)
unzip = (HOLE GAP 0)
\end{spec}
\end{exe}

\subsection{Polymorphic Maybe}

One last polymorphic type for now: \textit{polymorphic options}. The type declaration generalizes 
the one for |NatMaybe| in the previous chapter:
\begin{code}
data Maybe (A : Set) : Set where
  Just : A -> Maybe A
  Nothing : Maybe A
\end{code}
We can now rewrite the |index| function so that it works with any type of lists.
\begin{code}
index : {A : Set} -> Nat -> List A -> Maybe A
index n nil = Nothing
index zero (x , _) = Just x
index (suc n) (_ , xs) = index n xs
\end{code}

\section{Functions as Data}

\subsection{High-Order Functions}

Like many other modern programming languages --- including all functional languages 
(ML, Haskell, Scheme, etc.) --- Agda treats functions as first-class citizens, allowing 
functions to be passed as arguments to other functions, returned as results, stored in 
data structures, etc.

Functions that manipulate other functions are often called higher-order functions. 
Here's an example:
\begin{code}
doIt3Times : {A : Set} -> (A -> A) -> A -> A
doIt3Times f x = f (f (f x))
\end{code}
The argument |f| here is itself a function (from |A| to |A|); the body of |doIt3Times| 
applies |f| three times to some value |x|.

\subsection{Partial Application}

In fact, the multiple-argument functions we have already seen are also examples of 
passing functions as data. To see why, recall the type of |+|:
\begin{spec}
+ : Nat -> Nat -> Nat
\end{spec}
Each |->| in this expression is actually a binary operator on types. (This is the same as 
saying that Agda primitively supports only one-argument functions --- do you see why?) 
This operator is right-associative, so the type of |+| is really a shorthand for 
|Nat -> (Nat -> Nat)| --- i.e., it can be read as saying that ``|+| is a one-argument 
function that takes a |Nat| and returns a one-argument function that takes another |Nat| 
and returns a |Nat|.'' In the examples above, we have always applied |+| to both of its 
arguments at once, but if we like we can supply just the first. This is called 
\textit{partial application}. 

The next source code piece shows the definition |plus3| that uses |+| partially applied fixing
the parameter |3|.
\begin{code}
plus3 : Nat -> Nat
plus3 = _+_ 3

testPlus3 : plus3 4 == 7
testPlus3 = refl
\end{code}

\subsection{Digression: Currying}

In Agda, a function |f : A -> B > C| really has the type |A -> (B -> C)|. That is, if you give |f|
a value of type |A|, it will give you function |f' : B -> C|. If you then give |f'| a value of type |B|, 
it will return a value of type |C|. This allows for partial application, as in |plus3|. Processing a 
list of arguments with functions that return functions is called \textit{currying}, in honor of the 
logician Haskell Curry.
Conversely, we can reinterpret the type |A -> B -> C| as |(A * B) -> C|. This is called uncurrying. 
With an uncurried binary function, both arguments must be given at once as a pair; there is no 
partial application. We can define currying as follows:
\begin{code}
curry : {A B C : Set} -> (A -> B -> C) -> (A * B) -> C
curry f (x , y) = f x y
\end{code}
The uncurry function can be defined in similarly:
\begin{code}
uncurry : {A B C : Set} -> ((A * B) -> C) -> A -> B -> C
uncurry f x y = f (x , y)
\end{code}

%if False
More stuff used in latter chapters...
\begin{code}
id : {A : Set} -> A -> A
id x = x

snoc : {A : Set} -> A -> List A -> List A
snoc x nil = x , nil
snoc x (y , ys) = y , (snoc x ys)

rev : {A : Set} -> List A -> List A
rev nil = nil
rev (x , xs) = snoc x (rev xs)
\end{code}
%endif

\begin{exe}[Curry and Uncurry are inverses]
Now prove the following facts that state, together, that |curry| and |uncurry| are
inverses of each other:
\begin{spec}
uncurryCurry : forall {A B C : Set} (f : A -> B -> C) x y -> curry (uncurry f) x y == f x y
uncurryCurry = (HOLE GAP 0)

curryUncurry : forall {A B C : Set}(f : (A * B) -> C)) (p : A * B) -> uncurry (curry f) p == f p
curryUncurry = (HOLE GAP 1)
\end{spec}
\end{exe}

\subsection{Filter}

Here is a useful higher-order function, which takes a list of |A|s and a predicate on |A| 
(a function from |A| to |Bool|) and ``filters'' the list, returning a new list containing 
just those elements for which the predicate returns |True|.
\begin{code}
filter : {A : Set} -> (A -> Bool) -> List A -> List A
filter p nil = nil
filter p (x , xs) with p x
filter p (x , xs) | True  = x , filter p xs
filter p (x , xs) | False = filter p xs
\end{code}
Note that in this definition we use the construct |with| to pattern match on the result |p x|.
The with allows us to pattern match on intermediate results of a computation. This is very useful
when pattern matching involves dependent types.

For example, if we apply |filter| to the predicate |evenb| and a list of numbers l, it returns a 
list containing just the even members of l.
\begin{code}
testFilterEven : filter evenb (1 , 2 , 0 , 3 , nil) == (2 , 0 , nil)
testFilterEven = refl
\end{code}
We can use |filter| to give a concise version of the |countoddmembers| function from the Lists chapter.
\begin{code}
countoddmembers' : List Nat -> Nat
countoddmembers' l = length (filter oddb l)  

testCountOddMembers' : countoddmembers' (1 , 2 , 3 , nil) == 2
testCountOddMembers' = refl
\end{code}

\subsection{Anonymous Functions}

Consider the following example:
\begin{code}
lengthIs1 : {A : Set} -> List A -> Bool
lengthIs1 l = beqNat (length l) 1

testFilter1 : filter lengthIs1 ((1 , 2 , nil) , (1 , nil) , nil) == ((1 , nil) , nil)
testFilter1 = refl
\end{code}
Note that to filter lists whose length is 1, we need to define a function |lengthIs1| that
is used only as a predicate to |filter|. This is a bit annoying.
Moreover, this is not an isolated example. When using higher-order functions, we often want 
to pass as arguments ``one-off'' functions that we will never use again; having to give each 
of these functions a name would be tedious.

Fortunately, there is a better way. It is also possible to construct a function ``on the fly'' 
without declaring it at the top level or giving it a name; this is analogous to the notation 
we've been using for writing down constant lists, natural numbers, and so on.
\begin{code}
testAnonymous : (doIt3Times {Nat} (\ x -> x + x) 2) == 16
testAnonymous = refl
\end{code}
Here is the motivating example from before, rewritten to use an anonymous function.
\begin{code}
testFilter2 : filter (\ x -> beqNat (length x) 1) ((1 , 2 , nil) , (1 , nil) , nil) == ((1 , nil) , nil)
testFilter2 = refl
\end{code}
\begin{exe}
Use |filter| to write a function filterEvenGt7 that takes a list of natural numbers as input and 
returns a list of just those that are even and greater than 7.
\end{exe}
\begin{exe}[Partition]
Use filter to write a Agda function partition:
\begin{spec}
partition : {A : Set} -> (A -> Bool) -> List A (List A * List A)
\end{spec}
Given a set |A|, a test function of type |A -> Bool| and a |List A|, |partition| should return a pair of lists. 
The first member of the pair is the sublist of the original list containing the elements that satisfy the test, 
and the second is the sublist containing those that fail the test. The order of elements in the two sublists 
should be the same as their order in the original list.
\end{exe}

\subsection{Map}

Another handy higher-order function is called |map|.
\begin{code}
map : {A B : Set} -> (A -> B) -> List A -> List B
map f nil = nil
map f (x , xs) = f x , map f xs
\end{code}
It takes a function |f| and a list |l = n1, n2, n3, ...| and returns the list |f n1, f n2, f n3,...| , where 
|f| has been applied to each element of |l| in turn. For example:
\begin{code}
testMap : map plus3 (1 , 2 , nil) == (4 , 5 , nil)
testMap = refl
\end{code}
The element types of the input and output lists need not be the same (map takes two type arguments, |A| and |B|). 
This version of |map| can thus be applied to a list of numbers and a function from numbers to booleans to yield a 
list of booleans:
\begin{code}
testMap1 : map evenb (1 , 2 , 3 , nil) == (False , True , False , nil)
testMap1 = refl
\end{code}
\begin{exe}[|map| and |rev| commutes]
Show that |map| and |rev| commute. You may need to define an auxiliary lemma.
\begin{spec}
mapRevComm : forall {A B : Set}(f : A -> B)(l : List A) -> map f (rev l) == rev (map f l)
\end{spec}
\end{exe}

\begin{exe}[|concatMap|]
The function |map| maps a |List A| to a |List B| using a function of type |A -> B|. We can define 
a similar function, |concatMap|, which maps a |List A| to a |List B| using a function |f| of type 
|A -> List B|. Your definition should work by 'flattening' the results of f, like so:
\begin{spec}
 concatMap (\ n -> (n , n+1 , n+2 , nil)) (1 , 5 , 1 , nil) 
      = (1 , 2 ,  3 , 5 , 6 , 7 , 10 , 11 , 12 , nil).
\end{spec}
\end{exe}

Lists are not the only inductive type that we can write a |map| function for. 
Here is the definition of |map| for the |Maybe| type:

\begin{code}
mapMaybe : {A B : Set} -> (A -> B) -> Maybe A -> Maybe B
mapMaybe f Nothing = Nothing
mapMaybe f (Just x) = Just (f x)
\end{code}

\subsection{Fold}

An even more powerful higher-order function is called |fold|. This function is 
the inspiration for the ``reduce'' operation that lies at the heart of Google's 
|map|/|reduce| distributed programming framework.
\begin{code}
fold : {A B : Set} -> (A -> B -> B) -> B -> List A -> B
fold f v nil = v
fold f v (x , xs) = f x (fold f v xs)
\end{code}
Intuitively, the behavior of the fold operation is to insert a given binary operator 
|f| between every pair of elements in a given list. For example, |fold plus (1 , 2 , 3 , 4 , nil)| 
intuitively means |1+2+3+4|. To make this precise, we also need a ``starting element'' that serves as 
the initial second input to |f|. So, for example,
\begin{spec}
 fold plus (1 , 2 , 3 , 4 , nil) 0
\end{spec}
yields
\begin{spec}
1 + (2 + (3 + (4 + 0)))
\end{spec}.

\subsection{Functions For Constructing Functions}

Most of the higher-order functions we have talked about so far take functions as arguments. Now let's 
look at some examples involving returning functions as the results of other functions.

To begin, here is a function that takes a value x (drawn from some type |A|) and returns a function 
from |Nat| to |A| that yields |x| whenever it is called, ignoring its nat argument.

\begin{code}
constFun : {A : Set} -> A -> Nat -> A 
constFun x n = x

ftrue : Nat -> Bool
ftrue = constFun True

testFtrue1 : ftrue 0 == True
testFtrue1 = refl
\end{code}

Similarly, but a bit more interestingly, here is a function that takes a function |f| from numbers to some 
type |A|, a number |k|, and a value |x|, and constructs a function that behaves exactly like |f| except 
that, when called with the argument |k|, it returns |x|.
\begin{code}
override : {A : Set} -> (Nat -> A) -> Nat -> A -> Nat -> A
override f k x k' = if beqNat k k' then x else f k'
\end{code}
For example, we can apply override twice to obtain a function from numbers to booleans that returns |False| on 
1 and 3 and returns |True| on all other arguments.
\begin{code}
fMostlyTrue : Nat -> Bool
fMostlyTrue = override (override ftrue 1 False) 3 False

testFMostlyTrue1 : fMostlyTrue 0 == True
testFMostlyTrue1 = refl

testFMostlyTrue2 : fMostlyTrue 1 == False
testFMostlyTrue2 = refl
\end{code}

\begin{exe}[Override example]
Before starting to work on the following proof, make sure you understand exactly what the theorem is saying and 
can paraphrase it in your own words. The proof itself is straightforward.
\begin{spec}
overrideExample : forall (b : Bool) -> (override (constFun b) 3 True) 2 = b.
overrideExample = (HOLE GAP 0)
\end{spec}
\end{exe}
We'll use function overriding heavily in parts of the rest of the course, and we will end up needing to know quite 
a bit about its properties. Unlike Coq, Agda doesn't have a special tactic to ``unfold'' definitions. These are
automatically unfolded by Agda's type checker.

\section{Additional Exercices}

\begin{exe}
Many common functions on lists can be implemented in terms of |fold|. 
For example, here is an alternative definition of |length|:
\begin{spec}
foldLength : forall {A : Set} -> List A -> Nat
foldLength = fold (\ _ ac -> suc ac) 0
\end{spec}
Prove that
\begin{spec}
theoremLength : forall {A : Set}(l : List A) -> length l == foldLength l
theoremLength = (HOLE GAP 0)
\end{spec}
\end{exe}

\begin{exe}
We can also define |map| in terms of |fold|. Give a definition of |map| using |fold| and prove that it is correct with
respect to the original |map| definition.
\end{exe}





