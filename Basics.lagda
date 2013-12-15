%if False
\begin{code}
module Basics where
\end{code}
%endif

\chapter{Basic Functional Programming in Agda}

\section{Introduction}

The functional programming style brings programming closer to mathematics: 
If a procedure or method has no side effects, then pretty much all you need 
to understand about it is how it maps inputs to outputs --- that is, you can 
think of its behavior as just computing a mathematical function. This is one 
reason for the word ``functional'' in ``functional programming.'' This direct 
connection between programs and simple mathematical objects supports both sound 
informal reasoning and formal proofs of correctness.

The other sense in which functional programming is ``functional'' is that it 
emphasizes the use of functions (or methods) as \textit{first-class values} --- i.e., 
values that can be passed as arguments to other functions, returned as results, 
stored in data structures, etc. The recognition that functions can be treated 
as data in this way enables a host of useful idioms, as we will see.
Other common features of functional languages include \textit{algebraic data types} and 
\textit{pattern matching}, which make it easy to construct and manipulate rich data 
structures, and sophisticated \textit{polymorphic type systems} that support abstraction 
and code reuse. Agda shares all of these features.

\section{Enumerated Types}

One unusual aspect of Coq is that its set of built-in features is extremely small. For 
example, instead of providing the usual palette of atomic data types (booleans, integers, strings, etc.), 
Agda offers an extremely powerful mechanism for defining new data types from scratch --- so powerful that 
all these familiar types arise as instances.

Agda has a standard library that comes with definitions of booleans, numbers, and many common data structures 
like lists. But there is nothing magic or primitive about these library definitions: they are ordinary user code.
To see how this works, let's start with a very simple example.

\subsection{Days of Week}

The following declaration tells Agda that we are defining a new set of data values --- a type.

\begin{code}
data Day : Set where
  Monday    : Day
  Tuesday   : Day
  Wednesday : Day
  Thursday  : Day
  Friday    : Day
  Saturday  : Day
  Sunday    : Day
\end{code}

The type is called Day, and its members are Monday, Tuesday, etc. The second through eighth 
lines of the definition can be read ``monday is a day, tuesday is a day, etc.''

Having defined Day, we can write functions that operate on days.

\begin{code}
nextDay : Day -> Day
nextDay Monday    = Tuesday
nextDay Tuesday   = Wednesday
nextDay Wednesday = Thursday
nextDay Thursday  = Friday
nextDay Friday    = Saturday
nextDay Saturday  = Sunday
nextDay Sunday    = Monday
\end{code}

One thing to note is that the argument and return types of this function are explicitly 
declared. Like most functional programming languages, Agda can often work out these types 
even if they are not given explicitly --- i.e., it performs some type inference --- but 
we'll always include them to make reading easier.

Having defined a function, we should check that it works on some examples. There are 
actually two different ways to do this in Agda. One uses the notion of equality and
another uses the interactive emacs mode. To test the new defined |nextDay| function,
just type C-c C-n and type |nextDay| |Friday| on the emacs buffer in order to Agda evaluate
the expression to |Saturday|.

\subsection{Booleans}

In a similar way, we can define the type |Bool| of booleans, with members true and false.

\begin{code}
data Bool : Set where
  True  : Bool
  False : Bool
\end{code}

Although we are rolling our own booleans here for the sake of building up everything from 
scratch, Agda does, of course, provide a default implementation of the booleans in its standard 
library, together with a multitude of useful functions and lemmas. 
Whenever possible, we'll name our own definitions and theorems so that they exactly coincide 
with the ones in the standard library.

Functions over booleans can be defined in the same way as above:

\begin{code}
not : Bool -> Bool
not True  = False
not False = True

and : Bool -> Bool -> Bool
and True t  = t
and False _ = False

or : Bool -> Bool -> Bool
or True _  = True
or False t = t 
\end{code}

Agda supports the so called mixfix operator syntax and unicode identifiers that are extensively used 
in the standard library. We believe that using these only serves as an additional barrier for newbies
learning Agda. So, we will avoid it.

Again, we can test these definitions using the emacs mode through the command C-c C-n.

\begin{exe}[The nand logic operator]
Define the following function to represent the nand logic operator. Nand connective is defined using
the following truth table:
\begin{center}
\begin{tabular}{ccc}
$A$       & $B$        & |nand| $A$ $B$\\
|False| & |False|  &  |True| \\
|False| & |True|   &  |True| \\
|True|  & |False|  &  |True| \\
|True|  & |True|   &  |False| \\
\end{tabular}
\end{center}
\begin{spec}
nand : Bool -> Bool -> Bool
nand a b = ?
\end{spec}
\end{exe}

\begin{exe}[The and3 function]
Implement the |and3| function that returns the conjunction of 3 boolean values.
\begin{spec}
and3 : Bool -> Bool -> Bool -> Bool
and3 a b c = ?
\end{spec}
\end{exe}

\subsection{Function Types}

We can use the emacs interactive mode to deduce an expression types. Just type
C-c C-d and enter a expression in the emacs buffer to Agda give this expression type.

As an example, entering the expression |and| |True|, Agda will return the type
|Bool -> Bool|. Entering |not|, will also return |Bool -> Bool|.

\subsection{Numbers}

The types we have defined so far are examples of ``enumerated types'': their definitions 
explicitly enumerate a finite set of elements. A more interesting way of defining a type 
is to give a collection of ``inductive rules'' describing its elements. For example, we 
can define the natural numbers as follows:

\begin{code}
data Nat : Set where
  zero : Nat
  suc  : Nat -> Nat
\end{code}

The clauses of this definition can be read:
\begin{itemize}
  \item |zero| is a natural number.
  \item |suc|  is a ``constructor'' that takes a natural number and yields another one --- 
        that is, if |n| is a natural number, then |suc n| is too.
\end{itemize}

Agda compiler provides some pragmas to enable numeric literals, in order to avoid the
verbose notation of $n$-aries |suc|s.

\begin{code}
{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}
\end{code}

Let's look at this in a little more detail. 

Every inductively defined set (Day, Nat, Bool, etc.) is actually a set of expressions. 
The definition of |Nat| says how expressions in the set |Nat| can be constructed:
\begin{itemize}
  \item the expression |zero| belongs to the set |Nat|;
  \item if |n| is an expression belonging to the set |Nat|, then |suc n| is also an 
        expression belonging to the set |Nat|; and expressions formed in these two ways 
        are the only ones belonging to the set |Nat|.
\end{itemize}
The same rules apply for our definitions of |Day| and |Bool|. The annotations we used 
for their constructors are analogous to the one for the |zero| constructor, and indicate 
that each of those constructors doesn't take any arguments.

These three conditions are the precise force of the inductive declaration. They imply 
that the expression |zero|, the expression |suc zero|, the expression |suc (suc zero)|, 
the expression |suc (suc (suc zero))|, and so on all belong to the set |Nat|, while other 
expressions like |True|, |and True False|, and |suc (suc False)| do not.

We can write simple functions that pattern match on natural numbers just as we did above --- 
for example, the predecessor function:

\begin{code}
pred : Nat -> Nat
pred zero    = zero
pred (suc n) = n
\end{code}

These are all things that can be applied to a number to yield a number. However, there 
is a fundamental difference: functions like pred and minustwo come with computation rules 
--- e.g., the definition of |pred| says that |pred 2| can be simplified to 1 --- while 
the definition of |suc| has no such behavior attached. Although it is like a function 
in the sense that it can be applied to an argument, it does not do anything at all!

For most function definitions over numbers, pure pattern matching is not enough: we 
also need recursion. For example, to check that a number |n| is even, we may need 
to recursively check whether $n-2$ is even. 

\begin{code}
evenb : Nat -> Bool
evenb zero          = True
evenb (suc zero)    = False
evenb (suc (suc n)) = evenb n
\end{code}

We can define |oddb|, a function that tests if a natural number is odd, similarly or using
|evenb|.

\begin{exe}{Defining |oddb|}
Define the function |oddb| that tests if a number is odd, without recursion.
\begin{spec}
oddb : Nat -> Bool
oddb n = ?
\end{spec}
\end{exe}

Naturally, we can also define multi-argument functions by recursion.

%if False
\begin{code}
infixr 4 _+_
infixr 4 _*_
\end{code}
%endif

\begin{code}
_+_ : Nat -> Nat -> Nat
zero + m = m
suc n + m = suc (n + m)
\end{code}

Adding three to two now gives us five, as we'd expect --- You can test it using C-c C-n, as you know.

The simplification that Coq performs to reach this conclusion can be visualized as follows:
\begin{flushleft}
\begin{tabular}{lc}
|suc (suc (suc zero)) + suc (suc zero)| & $\Rightarrow$\\
|suc (suc zero) + suc (suc (suc zero))| & $\Rightarrow$\\
|suc zero + suc (suc (suc (suc zero)))| & $\Rightarrow$\\
|zero + suc (suc (suc (suc (suc zero))))| & $\Rightarrow$\\
|suc (suc (suc (suc (suc zero))))| & \\
\end{tabular}
\end{flushleft}

Multiplication and subtraction over naturals are defined straightforwardly, by pattern matching.
The underscore represents a \textit{wildcard} pattern. Writing underscores in a pattern is the same as 
writing some variable that doesn't get used on the right-hand side. This avoids the need to invent 
a bogus variable name.

\begin{code}
_*_ : Nat -> Nat -> Nat
zero * m  = zero
suc n * m = m + (n * m)

_-_ : Nat -> Nat -> Nat
zero  - _     = zero
n     - zero  = n
suc n - suc m = suc (n - m)
\end{code}

\begin{exe}[factorial function]
Define a function to compute the factorial of a given natural number.
\begin{spec}
factorial : Nat -> Nat
factorial n = ?
\end{spec}
\end{exe}

When we say that Agda comes with nothing built-in, we really mean it: 
even equality testing for numbers is a user-defined operation! The |beq_nat| function tests natural 
numbers for equality, yielding a boolean. 

\begin{code}
beqNat : Nat -> Nat -> Bool
beqNat zero    zero    = True
beqNat zero    (suc _) = False
beqNat (suc _) zero    = False
beqNat (suc n) (suc m) = beqNat n m
\end{code}

Similarly, the |ble_nat| function tests natural numbers for less-or-equal, yielding a boolean.

\begin{code}
bleNat : Nat -> Nat -> Bool
bleNat zero    _       = True
bleNat (suc n) zero    = False
bleNat (suc n) (suc m) = bleNat n m
\end{code}

\begin{exe}[Definition of |blt_nat|]
The |blt_nat| function tests natural numbers for less-than, yielding a boolean. 
\begin{spec}
bltNat : Nat -> Nat -> Bool
bltNat n m = ?
\end{spec}
\end{exe}

\section{Proof by Simplification}

\textbf{Little digression:}  In type theory based proof assistants, like Agda and Coq, there are
(at least) two notions of equality: the definitional equality and the propositional equality.
I need to put here some explanation about propositional equality. \textbf{End of little digression}.

%if False
\begin{code}
postulate Level : Set
postulate LZero : Level
postulate LSuc  : Level -> Level
postulate LMax  : Level -> Level -> Level

{-# BUILTIN LEVEL Level #-}
{-# BUILTIN LEVELZERO LZero #-}
{-# BUILTIN LEVELSUC LSuc #-}
{-# BUILTIN LEVELMAX LMax #-}

data _==_ {l}{A : Set l}(x : A) : A -> Set l where
  refl : x == x

{-# BUILTIN EQUALITY _==_ #-}
{-# BUILTIN REFL refl #-}

infixl 4 _==_ 
\end{code}
%endif

Now that we've defined a few datatypes and functions, let's turn to the question of how to 
state and prove properties of their behavior. Actually, in a sense, we've already started 
doing this: each time we use C-c C-n in the previous sections makes a precise claim about the behavior 
of some function on some particular inputs. The proofs of these claims were always the same: 
use |refl| --- that has type |x == x|, for each |x| --- to check that both sides of the = simplify to identical values.

The same sort of ``proof by simplification'' can be used to prove more interesting properties as well. 
For example, the fact that 0 is a ``neutral element'' for |+| on the left can be proved just by 
observing that |0 + n| reduces to |n| no matter what |n| is, a fact that can be read directly off the definition of |+|.

\begin{code}
lemmaPlus0N : forall (n : Nat) -> 0 + n == n
lemmaPlus0N n = refl
\end{code}

Agda emacs mode uses some unicode notation for symbols. More information about unicode notation can be found at Agda wiki.

Agda follows the so-called \textit{Curry-Howard isomorphism} where types denote logical formulas and terms proofs. So, a proof
of a theorem just correspond to a function whose type denotes the formula being proved by the term defining the function.

Note that we've added the quantifier |forall (n : Nat)|, so that our theorem talks about all natural numbers |n|. 
In order to prove theorems of this form, we need to to be able to reason by assuming the existence of an arbitrary 
natural number |n|. This is achieved in the proof by considering the quantified variable |n| as a function parameter, 
putting it on the context as an hypothesis. With this, we can start the proof by saying "OK, suppose n is some arbitrary number."

Agda does not have tactics like Coq, so in order to prove theorems we need to fully construct terms with the type of the theorem
being proved. The next definitions are simple examples of proofs:

\begin{code}
lemmaPlus1L : forall (n : Nat) -> 1 + n == suc n
lemmaPlus1L n = refl

lemmaMult0L : forall (n : Nat) -> 0 * n == 0
lemmaMult0L n = refl
\end{code}

\section{Proof by Rewriting}

Here is a slightly more interesting theorem:

\begin{spec}
plusIdExample : forall (n m : Nat) -> n == m -> n + n == m + m
\end{spec}

Instead of making a completely universal claim about all numbers n and m, 
this theorem talks about a more specialized property that only holds when |n == m|. 
The arrow symbol is pronounced ``implies.''
As before, we need to be able to reason by assuming the existence of some numbers |n| 
and |m|. We also need to assume the hypothesis |n == m|. 

Before we show the real proof of this little theorem, we need to learn how to use 
Agda emacs mode in order to interactively construct proofs. When building a term, 
we can use holes, ?, as parts of a term that will need to be filled with a type correct term
in order to finish the definition. 
Loading the file with |[C-c C-l]|, we find that Agda
checks the unfinished program, turning the |?| into labelled braces,
\begin{spec}
plusIdExample : forall (n m : Nat) -> n == m -> n + n == m + m
plusIdExample n m = (HOLE GAP 0)
\end{spec}
and tells us, in the information window,
\begin{spec}
?0 : n == m -> n + n == m + m
\end{spec}
that the type of the `hole' corresponds to the return type we wrote.
In order to prove this, we need to put the equality |n == m| in context
to use it as an hypothesis. To this we can add another parameter to
|plusIdExample| to represent the hypothesis of type |n == m|. 
This can be expessed as:
\begin{spec}
plusIdExample : forall (n m : Nat) -> n == m -> n + n == m + m
plusIdExample n m prf = (HOLE GAP 0)
\end{spec}
leaving the following hole:
\begin{spec}
?0 : n + n == m + m
\end{spec}
To finish this proof we need to use the equality constructor |refl|, but
the hole doesn't have the shape |x == x|. In order to make the hole type
fit the |refl| type, we need to \textit{pattern match} on the proof that |n == m|.
When the pattern matches occurs, the equality |n == m| is rewritten in the hole type,
making it equal to |m + m == m + m| that matches |refl| type.

Agda mode can automate the generatiion of total pattern matching in definitions. Putting
the variable on which we want to pattern match on the hole and pressing C-c C-c.

In this proof, we want to pattern match on the equality |n == m|, so we put the variable |prf|
on the hole and trigger Agda mode case spliting:
\begin{spec}
plusIdExample : forall (n m : Nat) -> n == m -> n + n == m + m
plusIdExample n m prf = {!prf!}
\end{spec}
Emacs will change the definition of |plusIdExample| to:
\begin{spec}
plusIdExample : forall (n m : Nat) -> n == m -> n + n == m + m
plusIdExample .m m refl = {!!}
\end{spec}
in which the hole has the following type
\begin{spec}
?0 : m + m == m + m
\end{spec}
that matches |refl| type. A important part of this definition is that the left-hand side of
the definition has what we call a dotted pattern. Dotted patterns specify equality constraints
to be used by the type checker of Agda, when verifying a term. In this example, the dotted pattern
is used to specify that the first and the second argument of |plusIdExample| must be the same, in
order to |refl| be valid.

To finish the proof, we can just type |refl| in the hole and press C-c C-g or use Agda mode 
proof search search, by pressing C-c C-a.

\begin{code}
plusIdExample : forall (n m : Nat) -> n == m -> n + n == m + m
plusIdExample .m m refl = refl
\end{code}

\begin{exe}[A simple equality proof]
Prove the following simple equality:
\begin{spec}
plusIdExercice : forall (n m o : Nat) -> n == m -> m == o -> n + m == m + o
plusIdExercice = (HOLE GAP 0)
\end{spec}
\end{exe}

Holes can be used whenever we want to skip trying to prove a theorem and just accept it as a given. 
This can be useful for developing longer proofs, since we can state subsidiary facts that we believe will be 
useful for making some larger argument, use holes to accept them on faith for the moment, 
and continue thinking about the larger argument until we are sure it makes sense; then we can 
go back and fill in the proofs we skipped. Be careful, when we leave unfinished terms we leave
a door open for total nonsense to enter Agda's nice, rigorous, formally checked world!

As another example of equality proof, consider the following simple code piece:

\begin{code}
mult0Plus : forall (n m : Nat) -> (0 + n) * m == n * m
mult0Plus n m = refl
\end{code}

Agda is able to determine that |(0 + n) * m| is definitionally equal to |n * m|, so we can just prove
|mult0Plus| using |refl|.

\section{Proof by Case Analysis}

Of course, not everything can be proved by simple calculation: In general, unknown, hypothetical 
values (arbitrary numbers, booleans, lists, etc.) can block the calculation. For example, if we try 
to prove the following fact using reduction as above, we get stuck.

\begin{spec}
beqNatN+1=0 : forall (n : Nat) -> beqNat (n + 1) 0 == False
beqNatN+1=0 n = (HOLE GAP 0)
\end{spec}

The reason for this is that the definitions of both |beqNat| and |+| begin by performing a match on 
their first argument. But here, the first argument to |+| is the unknown number |n| and the argument 
to |beqNat| is the compound expression |n + 1|; neither can be simplified.

What we need is to be able to consider the possible forms of |n| separately. If |n| is |zero|, then we can 
calculate the final result of |beqNat (n + 1) 0| and check that it is, indeed, false. And if |n == suc n'| 
for some |n'|, then, although we don't know exactly what number |n + 1| yields, we can calculate that, 
at least, it will begin with one |suc|, and this is enough to calculate that, again, |beqNat (n + 1) 0| 
will yield |False|.

To consider, separately, the cases where |n == 0| and where |n == S n'| we can just pattern match on |n|,
getting:

\begin{code}
beqNatN+1=0 : forall (n : Nat) -> beqNat (n + 1) 0 == False
beqNatN+1=0 zero    = refl
beqNatN+1=0 (suc n) = refl
\end{code}

Proofs by case analysis (pattern matching) works for any data type, like |Bool|:

\begin{code}
notInvolutive : forall (b : Bool) -> not (not b) == b
notInvolutive False = refl
notInvolutive True  = refl
\end{code}

\begin{exe}[Proof by case analysis]
Prove the following simple fact:
\begin{spec}
zeroNBeq+1 : forall (n : Nat) -> beqNat 0 (n + 1) == False
zeroNBeq+1 n = (HOLE GAP 0)
\end{spec}
\end{exe}


\section{More Exercices}

Use what you have learned so far to prove the following theorems.
\begin{exe}
Prove the following:
\begin{spec}
identityFnAppliedTwice : forall (f : Bool -> Bool)
                         (forall (b : Bool) -> f x == x) -> forall (b : Bool) -> f (f b) == b
identityFnAppliedTwice = (HOLE GAP 0)
\end{spec}
Now state and prove a theorem |negationFnAppliedTwice| similar to the previous one but where the second 
hypothesis says that the function f has the property that f x = not x.
\end{exe}

\begin{exe}
Prove the following lemma. (You may want to first prove a subsidiary lemma or two.)
\begin{spec}
lemma : forall (b c : Bool) -> (and b c == or b c) -> b == c
lemma = (HOLE GAP 0)
\end{spec}
\end{exe}

\begin{exe}[Binary Numbers]
Consider a different, more efficient representation of natural numbers using a binary 
rather than unary system. That is, instead of saying that each natural number is either 
zero or the successor of a natural number, we can say that each binary number is either
zero, twice a binary number, or one more than twice a binary number.
\begin{enumerate}
  \item  First, write an inductive definition of the type bin corresponding to this description of binary numbers.
  \item  Next, write an increment function for binary numbers, and a function to convert binary numbers to unary numbers.
\end{enumerate}
\end{exe}
