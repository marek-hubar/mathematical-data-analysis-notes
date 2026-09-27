#import "/template.typ": *

= The Statistical Learning Problem <sec:learn>

Machine learning is, at its core, the art of predicting from examples. We are shown a finite collection of
inputs together with the outputs that were observed for them, and we are asked to produce a rule that
predicts the output for inputs that we have never seen. Spam filters, medical risk scores, price estimates
and handwriting recognizers all fit this pattern. The mathematical question behind all of them is deceptively
simple: _in what sense can a finite data set tell us anything about unseen cases, and how should a
prediction rule be computed from it?_

This chapter sets up the language in which this question can be asked precisely, and it explains why the
rest of the book is about a particular answer: regularized risk minimization over reproducing kernel Hilbert
spaces. We model the data as independent draws from an unknown probability distribution $P$
(@sec:learn-distribution), measure the quality of a prediction by a loss function and the quality of a
prediction rule by its average loss, the _risk_ (@sec:learn-risk). The best achievable risk is the _Bayes
risk_; for the most common losses we can describe the optimal rule explicitly (@sec:learn-examples). Since
$P$ is unknown, the only thing we can compute is the average loss on the data, the _empirical risk_. We
will see in @sec:learn-overfitting that blindly minimizing the empirical risk over all functions is useless:
it memorizes the data and learns nothing. The remedy, discussed in @sec:learn-remedies, is to restrict or to
penalize the complexity of the candidate functions, and a few natural requirements on the penalty lead
directly to Hilbert spaces of functions in which point evaluations are continuous. The chapter ends with a
roadmap of the whole book, organized around eight guiding questions (@sec:learn-roadmap).

== From data to predictions <sec:learn-data>

Let us start with three typical situations.

- *Regression.* An input $x in RR^d$ collects features of an apartment (floor area, number of rooms, year
  of construction, distance to the city centre, ...) and the output $y in RR$ is its selling price. Given
  the records of $N$ past sales, we want to predict the price of an apartment that has just come on the
  market.
- *Binary classification.* An input $x$ is an e-mail (or an image, or the result of a blood test) and the
  output $y in {-1, 1}$ says whether it is spam (whether the image shows a cat, whether the patient
  develops a certain disease). We want a rule that labels new e-mails correctly as often as possible.
- *Unsupervised learning.* Only inputs $x_1, ..., x_N$ are observed, e.g. measurements from a machine in
  normal operation. We want to describe the region in which the data concentrate, so that a new measurement
  falling outside this region can be flagged as an _anomaly_.

In the first two cases the data come in pairs $(x_i, y_i)$ and the task is to find a function $f$ such that
$f(x)$ is a good prediction of the output $y$ belonging to a new input $x$; this is _supervised_ learning.
Note that the inputs can be very different objects: vectors, texts, images, graphs. For the moment we
assume nothing about the input set except that it carries a $sigma$-algebra; additional structure will be
introduced only when it is needed. That kernel methods can work with such abstract inputs is one of
their main attractions.

=== Why a deterministic model is not enough

The most naive model of supervised data would be: there is an unknown function $f^*$ such that
$y_i = f^*(x_i)$ for all $i$, and learning means reconstructing $f^*$ from its values at $x_1, ..., x_N$.
This model is inadequate for several reasons.

+ *Noise.* Outputs are measured with errors: prices are rounded, labels are assigned by humans who
  occasionally make mistakes.
+ *Missing information.* The input rarely contains everything that determines the output. Two
  apartments with identical recorded features can sell at different prices, because the buyers, the
  state of the kitchen or the view from the balcony were not recorded. Two patients with identical test
  results can have different outcomes.
+ *Contradictory data.* Consequently, a data set may contain the same input twice with different outputs,
  and then no function $f^*$ reproduces the data.
+ *What is a "new" input?* To judge a prediction rule by its performance on future inputs, we need to know
  something about how future inputs arise. A rule that is excellent for small apartments and terrible for
  large ones may be good or bad depending on which apartments are actually sold.

All four points are addressed at once by a probabilistic model: the pairs $(x, y)$ are random, drawn from a
fixed but unknown distribution $P$. The randomness of $x$ describes which inputs occur and how often; the
randomness of $y$ _given_ $x$ describes noise and missing information. The deterministic model survives as
the special case in which $y$ is a function of $x$ (@ex:learn-conditional-examples (ii) below), and the role
of $f^*$ will be taken over by the _Bayes decision function_ (@def:learn-bayes).

With this model, the two basic questions of learning theory are:

+ Can we compute from the data $D$ a function $f_D$ whose average loss on new data is close to the smallest
  possible average loss?
+ Does $f_D$ get closer to optimal as the number $N$ of data points grows?

The next two sections make "average loss" and "smallest possible average loss" precise.

== The data-generating distribution <sec:learn-distribution>

Throughout this book we use the following setting.

- The *input space* $(X, cal(A))$ is a measurable space. No topology or metric is assumed unless stated
  otherwise.
- The *output space* $Y subset.eq RR$ is a closed subset of the real line, equipped with its Borel
  $sigma$-algebra $borel(Y)$. Typical choices are $Y = RR$, $Y = [a, b]$ and $Y = {-1, 1}$. Being a
  closed subset of the complete separable metric space $RR$, the space $Y$ is itself complete and
  separable, i.e. a _Polish_ space; we will see in a moment why this matters.
- The *distribution* $P$ is a probability measure on $X times Y$ with respect to the product
  $sigma$-algebra $cal(A) times.o borel(Y)$. It is fixed but unknown.
- A *data set* is a finite sequence $D = ((x_1, y_1), ..., (x_N, y_N)) in (X times Y)^N$ of length
  (_sample size_) $N in NN$. It is modelled as a realization of independent random variables
  $(x_1, y_1), ..., (x_N, y_N)$, each with distribution $P$; equivalently, $D$ is distributed according to
  the product measure $P^N$ on $(X times Y)^N$. We say that $D$ is an _i.i.d. sample_ from $P$.

We use the same letters for the random variables and for their realizations; this is common in learning
theory and should not cause confusion. Note that a data set is a _sequence_, not a set: points may repeat.

=== Marginal and conditional distributions

To separate the two sources of randomness we decompose $P$. Let $pi: X times Y -> X$, $pi(x, y) = x$, be
the projection onto the input space; it is measurable. The *marginal distribution* of $P$ on $X$ is the
image measure
$ P_X (A) := P(pi^(-1)(A)) = P(A times Y), quad A in cal(A). $
It describes how the inputs are distributed, regardless of the outputs. The distribution of the output
_given_ the input is described by a conditional probability. Elementary conditioning,
$P(B | x) = P({x} times B) \/ P_X ({x})$, only makes sense if $P_X ({x}) > 0$, which fails for every $x$
as soon as, say, $X = RR^d$ and $P_X$ has a Lebesgue density. The right concept is the following.

#definition(title: [Regular conditional probability])[
  Let $(X, cal(A))$ be a measurable space, $Y subset.eq RR$ closed and $P$ a probability measure on
  $X times Y$. A map $P(dot | dot): borel(Y) times X -> [0, 1]$ is called a *regular conditional
  probability* of $P$ (given the input) if
  + for every $x in X$, the set function $P(dot | x): borel(Y) -> [0, 1]$ is a probability measure,
  + for every $B in borel(Y)$, the function $X -> [0, 1]$, $x |-> P(B | x)$, is $cal(A)$-measurable,
  + for all $A in cal(A)$ and $B in borel(Y)$,
    $ P(A times B) = integral_A P(B | x) dif P_X (x). $
] <def:learn-regular-conditional>

Properties (i) and (ii) say that $P(dot | dot)$ is a _probability kernel_ (Markov kernel) from $X$ to $Y$;
property (iii) says that it reconstructs $P$ from its marginal. The following lemma guarantees existence
and essential uniqueness, and it extends (iii) from rectangles to arbitrary integrands.

#lemma(title: [Regular conditional probabilities and disintegration])[
  Let $(X, cal(A))$ be a measurable space, let $Y$ be a Polish space with Borel $sigma$-algebra
  $borel(Y)$ (for instance a closed subset $Y subset.eq RR$), and let $P$ be a probability measure on
  $(X times Y, cal(A) times.o borel(Y))$ with marginal $P_X$. Then:
  + There exists a regular conditional probability $P(dot | dot)$ of $P$, i.e. a map with properties (i)–(iii)
    of @def:learn-regular-conditional (with $borel(Y)$ the Borel $sigma$-algebra of the Polish space $Y$).
  + It is unique up to $P_X$-null sets: if $Q(dot | dot)$ is another map with (i)–(iii), then there is a
    set $N_0 in cal(A)$ with $P_X (N_0) = 0$ such that $P(dot | x) = Q(dot | x)$ for all $x in X without N_0$.
  + (_Disintegration_) Let $g: X times Y -> [0, oo]$ be measurable. Then the function
    $x |-> integral_Y g(x, y) dif P(y | x)$ is $cal(A)$-measurable, and
    $ integral_(X times Y) g dif P = integral_X integral_Y g(x, y) dif P(y | x) dif P_X (x). $ <eq:learn-disintegration>
    The same holds for $P$-integrable $g: X times Y -> RR$, where the inner integral exists and is finite
    for $P_X$-almost every $x$.
] <lem:learn-regular-conditional>

#proof[
  (i) Existence is a classical but non-trivial theorem of measure theory, and we do not reprove it; see
  Section 10.2 of @dudley2002 and Chapter 6 of @kallenberg2002. For $Y subset.eq RR$ the idea is as
  follows. For each rational $q$, the Radon–Nikodym theorem gives a measurable function
  $F_q: X -> [0, 1]$ with $P(A times (Y inter (-oo, q])) = integral_A F_q dif P_X$ for all $A in cal(A)$.
  Countably many such versions can be modified on a common $P_X$-null set so that, for every $x$,
  $q |-> F_q (x)$ is non-decreasing, right-continuous along $QQ$ and has the limits $0$ and $1$ at
  $minus.plus oo$; it then extends to a distribution function, which defines the probability measure
  $P(dot | x)$. (For closed $Y$ one also checks that $P(dot | x)$ can be chosen to live on $Y$.) The
  general Polish case is reduced to this one, since every Polish space is Borel isomorphic to a Borel
  subset of $RR$. Countability of $QQ$ is essential here; this is where the regularity of $Y$ enters.

  (ii) Fix $B in borel(Y)$. Property (iii) of @def:learn-regular-conditional for both kernels gives
  $ integral_A (P(B | x) - Q(B | x)) dif P_X (x) = P(A times B) - P(A times B) = 0 quad "for all" A in cal(A). $
  Choosing
  $A = {x : P(B | x) > Q(B | x)}$ (measurable by @def:learn-regular-conditional (ii)) shows that this set is a $P_X$-null set, and
  likewise for the reverse inequality; so $P(B | x) = Q(B | x)$ for $P_X$-almost all $x$. Now let
  $cal(C)$ be a countable family of Borel sets which is closed under finite intersections and generates
  $borel(Y)$. For $Y subset.eq RR$ we can take $cal(C) = {Y inter (-oo, q] : q in QQ}$; for a general
  Polish space take all finite intersections of the sets of a countable base of the topology. Taking the
  (countable) union of the exceptional null sets for $B in cal(C)$ we obtain a null set $N_0 in cal(A)$
  such that for $x in.not N_0$ the probability measures $P(dot | x)$ and $Q(dot | x)$ agree on $cal(C)$.
  By the uniqueness theorem for measures (a consequence of Dynkin's $pi$-$lambda$ theorem) they agree on
  $borel(Y) = sigma(cal(C))$.

  (iii) We first show that the formula holds for indicator functions. For $E in cal(A) times.o borel(Y)$ and
  $x in X$ let $E_x := {y in Y : (x, y) in E}$ be the section of $E$ at $x$; it is a Borel set (the sets
  with Borel sections form a $sigma$-algebra containing all rectangles). Let $cal(D)$ be the family of all
  $E in cal(A) times.o borel(Y)$ such that $x |-> P(E_x | x)$ is measurable and
  $P(E) = integral_X P(E_x | x) dif P_X (x)$.
  - $cal(D)$ contains every rectangle $E = A times B$: then $P(E_x | x) = ind_A (x) P(B | x)$ is measurable
    by @def:learn-regular-conditional (ii), and the integral identity is exactly (iii) of @def:learn-regular-conditional. In particular
    $X times Y in cal(D)$.
  - $cal(D)$ is closed under complements: $(E^c)_x = (E_x)^c$, so $P((E^c)_x | x) = 1 - P(E_x | x)$ is
    measurable and integrates to $1 - P(E) = P(E^c)$.
  - $cal(D)$ is closed under countable disjoint unions: if $E^1, E^2, ... in cal(D)$ are pairwise disjoint
    and $E = union.big_k E^k$, then the sections $E^k_x$ are pairwise disjoint, so
    $P(E_x | x) = sum_k P(E^k_x | x)$ is measurable as a series of nonnegative measurable functions, and by
    the monotone convergence theorem (@thm:app-convergence)
    $integral_X P(E_x | x) dif P_X (x) = sum_k P(E^k) = P(E)$.

  Thus $cal(D)$ is a Dynkin system containing the $pi$-system of rectangles, which generates
  $cal(A) times.o borel(Y)$. By Dynkin's $pi$-$lambda$ theorem, $cal(D) = cal(A) times.o borel(Y)$. Since
  $integral_Y ind_E (x, y) dif P(y | x) = P(E_x | x)$, this is @eq:learn-disintegration for $g = ind_E$. By
  linearity it holds for nonnegative simple functions. A general measurable $g >= 0$ is the pointwise limit
  of an increasing sequence of nonnegative simple functions $g_n$; for every $x$, the monotone convergence
  theorem gives $integral_Y g_n (x, y) dif P(y | x) arrow.t integral_Y g(x, y) dif P(y | x)$, so the inner
  integral is measurable in $x$ as a pointwise limit of measurable functions, and applying monotone
  convergence twice more (on $X times Y$ and on $X$) yields @eq:learn-disintegration. For $P$-integrable
  $g$ apply this to $g^+$ and $g^-$: since
  $integral_X integral_Y abs(g(x, y)) dif P(y | x) dif P_X (x) = integral abs(g) dif P < oo$, the inner
  integral of $abs(g)$ is finite outside a $P_X$-null set $N_g in cal(A)$. On $X without N_g$ the inner
  integral of $g$ is the difference of the (finite, measurable) inner integrals of $g^+$ and $g^-$; setting
  it to $0$ on $N_g$ gives a measurable function of $x$, and subtracting the two identities for $g^+$ and
  $g^-$ gives the claim.
]

#remark(title: [On the hypothesis on $Y$])[
  It is tempting to state this lemma for an arbitrary metric space $Y$. That is not possible: @ex:learn-exercise-no-conditional constructs a separable metric space $Y subset [0, 1]$ and a
  probability measure on $[0, 1] times Y$ without a regular conditional probability. Some regularity of $Y$
  is therefore essential; Polish spaces (more generally, standard Borel spaces) are the usual setting. Our
  standing assumption "$Y subset.eq RR$ closed" is made precisely so that we never have to worry about
  this.
]

#intuition[
  The disintegration formula @eq:learn-disintegration describes a two-stage random experiment: first draw
  an input $x$ from $P_X$, then draw an output $y$ from $P(dot | x)$. The uncertainty in the data thus
  splits into the uncertainty about _which inputs occur_ (described by $P_X$) and the uncertainty about
  _the output at a given input_ (described by $P(dot | x)$). Since $P(dot | x)$ is determined only for
  $P_X$-almost every $x$, all statements about it hold "for $P_X$-almost all $x$"; about inputs that
  (almost) never occur, the distribution contains no information.
]

#example[
  + *Additive noise.* Let $Y = RR$, let $f_0 in meas(X)$, and let $Q$ be a probability measure on $RR$.
    Suppose $x$ is drawn from some distribution $mu$ on $X$ and, independently, a noise variable
    $epsilon$ from $Q$, and set $y := f_0 (x) + epsilon$. Then $P_X = mu$ and
    $P(B | x) = Q(B - f_0 (x))$, where $B - t = {b - t : b in B}$. Indeed, by independence and Fubini's
    theorem,
    $P(A times B) = integral_A integral_RR ind_B (f_0 (x) + e) dif Q(e) dif mu(x) = integral_A Q(B - f_0 (x)) dif mu(x)$,
    and the same computation shows that $x |-> Q(B - f_0 (x))$ is measurable.
  + *Deterministic data.* If $P(dot | x) = delta_(f^*(x))$ for a measurable $f^*: X -> Y$, then almost
    surely $y = f^*(x)$: this is the naive deterministic model of @sec:learn-data.
  + *Binary classification.* If $Y = {-1, 1}$, every probability measure on $Y$ is determined by the mass
    it gives to ${1}$. Hence $P(dot | x)$ is encoded by the measurable function
    $eta(x) := P({1} | x) in [0, 1]$, the _conditional probability of the label $1$_; $P({-1} | x) = 1 - eta(x)$.
] <ex:learn-conditional-examples>

== Loss functions and risks <sec:learn-risk>

How good is a prediction $t in RR$ for an input $x$ whose true output turns out to be $y$? The answer
depends on the application: in price prediction an error of 1000 euros may be irrelevant for a villa and
serious for a parking space; in medical diagnosis a missed disease is worse than a false alarm. We therefore
leave the choice open and encode it in a _loss function_.

#definition(title: [Loss function])[
  Let $(X, cal(A))$ be a measurable space and $Y subset.eq RR$ closed. A *loss function* is a measurable
  function
  $ L: X times Y times RR -> [0, oo), $
  where $X times Y times RR$ carries the $sigma$-algebra $cal(A) times.o borel(Y) times.o borel(RR)$. The number
  $L(x, y, t)$ is the cost of predicting $t$ at the input $x$ when the true output is $y$. Two special cases
  are important:
  + a *supervised loss* is a measurable $L: Y times RR -> [0, oo)$; it is identified with the loss
    $(x, y, t) |-> L(y, t)$, which does not depend on $x$;
  + an *unsupervised loss* is a measurable $L: X times RR -> [0, oo)$; it is identified with the loss
    $(x, y, t) |-> L(x, t)$, which does not depend on $y$.
] <def:learn-loss>

Two comments on this definition. First, predictions are real numbers even when $Y$ is small: for
$Y = {-1, 1}$ we allow real-valued $f(x)$, whose sign is the predicted label and whose magnitude can be read
as a confidence. This is how SVMs and logistic regression work, and it makes the space of candidate functions
a vector space. Second, most losses in practice are supervised; the general form $L(x, y, t)$ covers
unsupervised problems such as density level detection (@ex:learn-density-level) and weighted problems in
which errors at some inputs matter more than at others. Many concrete losses are collected in @sec:loss
(@ex:loss-catalogue).

A prediction rule is a measurable function $f: X -> RR$. Its quality is its loss _on average over new data_,
where "average" refers to the data-generating distribution.

#definition(title: [Risk])[
  Let $L: X times Y times RR -> [0, oo)$ be a loss function and $P$ a probability measure on $X times Y$.
  For $f in meas(X)$ the *$L$-risk* of $f$ is
  $ risk(L, P)(f) := integral_(X times Y) L(x, y, f(x)) dif P(x, y) in [0, oo]. $
  The map $risk(L, P): meas(X) -> [0, oo]$ is the *risk functional*.
] <def:learn-risk>

The integral is well defined: the map $(x, y) |-> (x, y, f(x))$ from $X times Y$ to $X times Y times RR$
is measurable because each of its three components is measurable (the third is $f compose pi$), so
$(x, y) |-> L(x, y, f(x))$ is a nonnegative measurable function as a composition of measurable maps. Its
integral may be $+oo$. In probabilistic language, $risk(L, P)(f)$ is the expected loss
$EE[L(x, y, f(x))]$ of $f$ on a new pair $(x, y)$ drawn from $P$, independent of the data. By the
disintegration formula (@lem:learn-regular-conditional (iii)),
$ risk(L, P)(f) = integral_X integral_Y L(x, y, f(x)) dif P(y | x) dif P_X (x). $ <eq:learn-risk-iterated>

Two elementary observations will be used throughout the book.

#remark[
  + *The risk only sees $P_X$-equivalence classes.* If $f, g in meas(X)$ agree $P_X$-almost everywhere,
    then $risk(L, P)(f) = risk(L, P)(g)$: the set ${(x, y) : f(x) != g(x)} = pi^(-1)({f != g})$ has
    $P$-measure $P_X ({f != g}) = 0$, so the two integrands agree $P$-almost everywhere. This is why the
    risk can later be studied on spaces of equivalence classes such as $L^p (P_X)$ (@sec:loss).
  + *The risk is in general nonlinear and may be infinite.* Even for the simple least squares loss and a
    distribution with $integral y^2 dif P(x, y) < oo$, we have $risk(L, P)(f) = oo$ for all $f$ with
    $integral f^2 dif P_X = oo$ (@ex:learn-least-squares). The analytic
    properties of $risk(L, P)$ as a functional on function spaces (measurability, convexity, continuity,
    differentiability) are the subject of @sec:loss.
] <rem:learn-risk-basic>

The inner integral in @eq:learn-risk-iterated is the expected loss of the prediction $f(x)$ at the fixed
input $x$. It is convenient to give it a name, because it reduces many questions about the risk to
one-dimensional problems.

#definition(title: [Inner risk])[
  Let $L$ be a loss function, $P$ a probability measure on $X times Y$ and $P(dot | dot)$ a regular
  conditional probability of $P$, fixed once and for all (by @lem:learn-regular-conditional (ii), another
  choice changes the following only for $x$ in a $P_X$-null set). For $x in X$ and $t in RR$, the *inner
  risk* is
  $ cal(C)_(L, P) (x, t) := integral_Y L(x, y, t) dif P(y | x) in [0, oo]. $
] <def:learn-inner-risk>

For a supervised loss the inner risk depends on $x$ only through the conditional distribution: in the
notation of @sec:loss, where $I_(L, Q) (t) := integral_Y L(y, t) dif Q(y)$ for a distribution $Q$ on $Y$,
we have $cal(C)_(L, P) (x, t) = I_(L, P(dot | x)) (t)$.

#lemma(title: [Pointwise minimization])[
  Let $L$ be a loss function and $P$ a probability measure on $X times Y$. For every $f in meas(X)$ the
  function $x |-> cal(C)_(L, P) (x, f(x))$ is measurable and
  $ risk(L, P)(f) = integral_X cal(C)_(L, P) (x, f(x)) dif P_X (x). $
  Consequently, if $f_0 in meas(X)$ satisfies $cal(C)_(L, P) (x, f_0 (x)) = inf_(t in RR) cal(C)_(L, P) (x, t)$
  for $P_X$-almost every $x$, then $risk(L, P)(f_0) <= risk(L, P)(f)$ for every $f in meas(X)$.
] <lem:learn-inner-risk>

#proof[
  The function $g(x, y) := L(x, y, f(x))$ is nonnegative and measurable, and its inner integral in
  @lem:learn-regular-conditional (iii) is $cal(C)_(L, P) (x, f(x))$; so the first statement is that lemma. For the second statement,
  $cal(C)_(L, P) (x, f(x)) >= cal(C)_(L, P) (x, f_0 (x))$ for $P_X$-almost every $x$; integrate.
]

Now we can say what the best possible prediction rule is.

#definition(title: [Bayes risk and Bayes decision function])[
  Let $L$ be a loss function and $P$ a probability measure on $X times Y$. The *Bayes risk* is the smallest
  possible $L$-risk,
  $ bayes(L, P) := inf { risk(L, P)(f) : f in meas(X) } in [0, oo]. $
  A function $f^*_(L, P) in meas(X)$ with $risk(L, P)(f^*_(L, P)) = bayes(L, P)$ is called a *Bayes
  decision function*. For $f in meas(X)$ with $bayes(L, P) < oo$, the difference
  $risk(L, P)(f) - bayes(L, P) >= 0$ is the *excess risk* of $f$.
] <def:learn-bayes>

The Bayes risk is the benchmark: no prediction rule, however clever, can do better, and it is typically
strictly positive because of noise. The following points deserve emphasis.

- *The infimum is over all measurable functions.* No restriction on the "complexity" of $f$ is made; the
  Bayes risk is a property of $L$ and $P$ alone. Since we allow real-valued predictions, the infimum is
  taken over $meas(X)$ and not only over measurable functions with values in $Y$; for some losses (e.g.
  least squares with $Y = {-1, 1}$) this makes a difference.
- *A Bayes decision function need not exist.* See @ex:learn-no-bayes below.
- *A Bayes decision function is at best unique up to $P_X$-null sets*: by @rem:learn-risk-basic (i) it
  can be changed on any $P_X$-null set without changing its risk. It can also be genuinely non-unique: in classification, at inputs where
  both labels are equally likely, both predictions are optimal (@ex:learn-classification).
- *It is unknown*, because $P$ is unknown. The whole point of learning is to approximate it from data.

#example(title: [A Bayes risk that is not attained])[
  Let $Y = {-1, 1}$ and consider the _exponential loss_ $L(y, t) := e^(-y t)$ (used in boosting
  @freund1997). Let $P$
  be any distribution with $P({1} | x) = 1$ for all $x$, i.e. all labels are $1$. Then
  $risk(L, P)(f) = integral_X e^(-f(x)) dif P_X (x) > 0$ for every $f in meas(X)$, while the constant
  functions $f equiv n$ have risk $e^(-n) -> 0$. Hence $bayes(L, P) = 0$, but no Bayes decision function
  exists. The "optimal prediction" would be $+oo$, which is not a real number.
] <ex:learn-no-bayes>

With these notions, the goal of learning can be stated precisely. Since $f_D$ is computed from a random
sample, its risk is a random variable, and we ask that it approaches the Bayes risk in probability.

#definition(title: [Learning method, consistency])[
  A *learning method* assigns to every $N in NN$ and every data set $D in (X times Y)^N$ a function
  $f_D in meas(X)$. Let $L$ be a loss function and $P$ a distribution on $X times Y$ with
  $bayes(L, P) < oo$, and assume that $D |-> risk(L, P)(f_D)$ is measurable on $(X times Y)^N$ for each
  $N$. The learning method is called *($L$-risk) consistent for $P$* if for every $epsilon > 0$
  $ lim_(N -> oo) P^N ({D in (X times Y)^N : risk(L, P)(f_D) > bayes(L, P) + epsilon}) = 0. $
  It is called *universally consistent* if it is consistent for every distribution $P$ on $X times Y$ with
  $bayes(L, P) < oo$.
] <def:learn-consistency>

The two questions at the end of @sec:learn-data thus ask for learning methods with small excess risk
for finite $N$, and for consistent learning methods.

== Three fundamental examples <sec:learn-examples>

In this section we compute the Bayes decision function for three important learning problems. In each case
@lem:learn-inner-risk reduces the problem to minimizing a function of one real variable.

=== Least squares regression

The oldest and most popular loss is the squared error.

#example(title: [Least squares loss])[
  Let $Y subset.eq RR$ be closed and let $L(y, t) := (y - t)^2$ be the *least squares loss*. Let $P$ be a
  distribution on $X times Y$ with finite second moment,
  $ integral_(X times Y) y^2 dif P(x, y) < oo. $
  Define the *regression function* (conditional mean) and the *conditional variance*
  $ f_P (x) := integral_Y y dif P(y | x), quad
    sigma_P^2 (x) := integral_Y (y - f_P (x))^2 dif P(y | x), $
  (modified on a $P_X$-null set as explained in the proof), and the *average noise level*
  $sigma_P^2 := integral_X sigma_P^2 (x) dif P_X (x)$. Then $f_P in L^2 (P_X)$, $sigma_P^2 < oo$, and for every
  $f in meas(X)$
  $ risk(L, P)(f) = norm(f - f_P)_(L^2 (P_X))^2 + sigma_P^2, $ <eq:learn-ls-decomposition>
  where $norm(f - f_P)_(L^2 (P_X))^2 := integral_X (f - f_P)^2 dif P_X in [0, oo]$ also for
  $f in.not L^2 (P_X)$, so both sides may be $+oo$. Consequently $bayes(L, P) = sigma_P^2 = risk(L, P)(f_P)$, and
  $f in meas(X)$ is a Bayes decision function if and only if $f = f_P$ $P_X$-almost everywhere. In
  particular, the excess risk of $f$ is $norm(f - f_P)_(L^2 (P_X))^2$.
] <ex:learn-least-squares>

#proof[
  _Step 1: $f_P$ and $sigma_P^2$ are well defined._ By @lem:learn-regular-conditional (iii) with
  $g(x, y) = y^2$, the function $m(x) := integral_Y y^2 dif P(y | x)$ is measurable and
  $integral_X m dif P_X = integral y^2 dif P < oo$. Hence $N_0 := {x : m(x) = oo} in cal(A)$ is a $P_X$-null
  set. For $x in.not N_0$ the measure $P(dot | x)$ has a finite second moment, hence also a finite first
  moment ($abs(y) <= 1 + y^2$), so $f_P (x)$ is a well-defined real number, and
  $x |-> ind_(X without N_0) (x) f_P (x)$ is measurable as the difference of the measurable functions
  $x |-> integral y^+ dif P(y | x)$ and $x |-> integral y^- dif P(y | x)$ (restricted to $X without N_0$,
  where both are finite). We set $f_P (x) := 0$ and $sigma_P^2 (x) := 0$ for $x in N_0$; this does not
  affect any integral with respect to $P_X$.

  _Step 2: the pointwise identity._ Fix $x in.not N_0$ and $t in RR$. Expanding
  $(y - t)^2 = (y - f_P (x))^2 + 2 (y - f_P (x))(f_P (x) - t) + (f_P (x) - t)^2$ and integrating with
  respect to $P(dot | x)$ (all three terms are integrable since $P(dot | x)$ has a finite second moment)
  gives
  $ cal(C)_(L, P) (x, t) = integral_Y (y - t)^2 dif P(y | x) = sigma_P^2 (x) + (f_P (x) - t)^2, $ <eq:learn-ls-pointwise>
  because the mixed term vanishes: $integral_Y (y - f_P (x)) dif P(y | x) = f_P (x) - f_P (x) = 0$. Taking
  $t = 0$ gives $m(x) = sigma_P^2 (x) + f_P (x)^2$; in particular $sigma_P^2 (x) = m(x) - f_P (x)^2$ is a
  measurable function of $x in X without N_0$. Integrating over $x$ yields
  $sigma_P^2 + norm(f_P)_(L^2 (P_X))^2 = integral y^2 dif P < oo$, so $sigma_P^2 < oo$ and $f_P in L^2 (P_X)$.

  _Step 3: the decomposition._ Let $f in meas(X)$. By @lem:learn-inner-risk and @eq:learn-ls-pointwise with
  $t = f(x)$,
  $ risk(L, P)(f) = integral_(X without N_0) (sigma_P^2 (x) + (f(x) - f_P (x))^2) dif P_X (x) = sigma_P^2 + norm(f - f_P)_(L^2 (P_X))^2, $
  where we used that $N_0$ is a null set and that the integral of a sum of nonnegative functions is the sum
  of the integrals (in $[0, oo]$).

  _Step 4: consequences._ Since $sigma_P^2 < oo$, @eq:learn-ls-decomposition shows
  $risk(L, P)(f) >= sigma_P^2 = risk(L, P)(f_P)$ with equality if and only if
  $norm(f - f_P)_(L^2 (P_X)) = 0$, i.e. $f = f_P$ $P_X$-almost everywhere.
]

The decomposition @eq:learn-ls-decomposition is worth pausing over. The Bayes risk $sigma_P^2$ is the
_irreducible_ error: the average variance of $y$ around its conditional mean, which no prediction rule can
remove; it vanishes exactly in the deterministic case $y = f_P (x)$. The excess risk is a squared
_Hilbert space distance_: for the least squares loss, learning is the same as approximating the unknown
regression function $f_P$ in $L^2 (P_X)$. This Hilbert space structure is one reason why least squares is
so tractable, and it is the model case for much of this book (kernel ridge regression, @ex:reg-krr).

The moment assumption has a simple meaning: $integral y^2 dif P = risk(L, P)(0)$ is the risk of the
trivial predictor $f = 0$. It is equivalent to $risk(L, P)(f) < oo$ for one (equivalently, for all)
$f in L^2 (P_X)$, because $y^2 <= 2 (y - f(x))^2 + 2 f(x)^2$ and, conversely, @eq:learn-ls-decomposition
holds. Without it, a Bayes decision function may still exist, but it need not lie in $L^2 (P_X)$
(@ex:learn-exercise-ls-moment). For $Y = {-1, 1}$ it is
automatically satisfied, and then $f_P (x) = eta(x) - (1 - eta(x)) = 2 eta(x) - 1$ with $eta$ as in
@ex:learn-conditional-examples (iii).

#remark(title: [$L_p$ losses and the median])[
  A natural family of variations are the *$L_p$ losses* $L_p (y, t) := abs(y - t)^p$ for $p in (0, oo)$,
  shown in @fig:learn-lp-losses. They differ in how they weigh small and large residuals $r = y - t$: for
  $p > 1$ small residuals are cheap and large residuals very expensive, so the risk is sensitive to
  outliers; for $p < 1$ it is the other way round, and the loss is no longer convex. For $p = 2$ we recover
  least squares. For $p = 1$ (the *absolute loss*) the role of the conditional mean is taken by the
  conditional *median*: if $integral abs(y) dif P < oo$, then $f in meas(X)$ is a Bayes decision function
  if and only if for $P_X$-almost every $x$ the number $f(x)$ is a median of $P(dot | x)$, i.e.
  $P((-oo, f(x)] | x) >= 1\/2$ and $P([f(x), oo) | x) >= 1\/2$ (@ex:learn-exercise-median). Since medians are much
  less affected by outliers than means, the absolute loss is a standard choice in robust regression. The
  properties of $L_p$ losses (convexity, Lipschitz continuity, growth) are discussed in @sec:loss
  (@ex:loss-catalogue).
] <rem:learn-lp>

#figure(
  cetz.canvas({
    plot.plot(
      size: (6.5, 4),
      axis-style: "scientific",
      x-label: $r = y - t$,
      y-label: $abs(r)^p$,
      x-tick-step: 1,
      y-tick-step: 1,
      y-min: 0,
      y-max: 3,
      x-min: -2,
      x-max: 2,
      legend: "east",
      legend-style: (stroke: none, fill: white, offset: (0.3, 0)),
      {
        plot.add(domain: (-2, 2), samples: 200, x => calc.pow(calc.abs(x), 0.5), style: (stroke: 1.1pt + rgb("#2e5a8a")), label: $p = 1\/2$)
        plot.add(domain: (-2, 2), samples: 3, x => calc.abs(x), style: (stroke: 1.1pt + rgb("#b5452a")), label: $p = 1$)
        plot.add(domain: (-1.74, 1.74), samples: 100, x => x * x, style: (stroke: 1.1pt + rgb("#3d8a4a")), label: $p = 2$)
        plot.add(domain: (-1.44, 1.44), samples: 100, x => calc.pow(calc.abs(x), 3), style: (stroke: 1.1pt + rgb("#c08a1e")), label: $p = 3$)
      },
    )
  }),
  caption: [The $L_p$ losses $L_p (y, t) = abs(y - t)^p$ as functions of the residual $r = y - t$. All
    curves pass through $(plus.minus 1, 1)$; larger $p$ punishes large residuals more and small residuals
    less. For $p < 1$ the loss is not convex.],
) <fig:learn-lp-losses>

=== Binary classification

#example(title: [Classification loss and the Bayes classifier])[
  Let $Y = {-1, 1}$. We use the convention
  $ sign(t) := cases(1 quad & "if" t >= 0, -1 & "if" t < 0) $
  (so that $sign$ takes values in $Y$), and define the *classification loss* (0-1 loss)
  $ L(y, t) := ind_((-oo, 0]) (y sign(t)) = cases(1 quad & "if" sign(t) != y, 0 & "if" sign(t) = y.) $
  Thus a real-valued $f$ predicts the label $sign(f(x))$, and
  $ risk(L, P)(f) = P({(x, y) in X times Y : sign(f(x)) != y}) $
  is the probability that $f$ misclassifies a new example. Let $eta(x) := P({1} | x)$. Then:
  + $risk(L, P)(f) = integral_X (eta(x) ind_((-oo, 0)) (f(x)) + (1 - eta(x)) ind_([0, oo)) (f(x))) dif P_X (x)$
    for all $f in meas(X)$.
  + The *Bayes classifier*
    $ f^*_(L, P) (x) := cases(1 quad & "if" eta(x) >= 1\/2, -1 & "if" eta(x) < 1\/2) $
    is a Bayes decision function, and
    $ bayes(L, P) = integral_X min{eta(x), 1 - eta(x)} dif P_X (x) <= 1/2. $
  + A function $f in meas(X)$ is a Bayes decision function if and only if $sign(f(x)) = f^*_(L, P) (x)$
    for $P_X$-almost every $x$ with $eta(x) != 1\/2$.
] <ex:learn-classification>

#proof[
  The loss is measurable because the set where it equals $1$,
  ${(y, t) : L(y, t) = 1} = ({1} times (-oo, 0)) union ({-1} times [0, oo))$, is a Borel set; $eta$ is
  measurable by (ii) of @def:learn-regular-conditional. Since $P(dot | x)$ lives
  on ${-1, 1}$ and $P({-1} | x) = 1 - eta(x)$, the inner risk is
  $ cal(C)_(L, P) (x, t) = eta(x) L(1, t) + (1 - eta(x)) L(-1, t) = cases(eta(x) quad & "if" t < 0, 1 - eta(x) & "if" t >= 0.) $
  (i) follows from @lem:learn-inner-risk. For (ii), note that
  $cal(C)_(L, P) (x, t) >= min{eta(x), 1 - eta(x)} =: cal(C)^* (x)$ for all $t$, with equality for
  $t = f^*_(L, P) (x)$. The Bayes classifier is measurable as $f^*_(L, P) = 2 ind_({eta >= 1\/2}) - 1$, so
  @lem:learn-inner-risk shows that it is a Bayes decision function, and
  $bayes(L, P) = integral_X cal(C)^* dif P_X$; the bound $1\/2$ holds because $min{s, 1 - s} <= 1\/2$.
  For (iii), all quantities are finite, so
  $risk(L, P)(f) - bayes(L, P) = integral_X (cal(C)_(L, P) (x, f(x)) - cal(C)^* (x)) dif P_X (x)$ with a
  nonnegative integrand. This vanishes if and only if the integrand is zero $P_X$-almost everywhere. If
  $eta(x) = 1\/2$ the integrand is always zero; if $eta(x) > 1\/2$ it is zero if and only if $f(x) >= 0$,
  and if $eta(x) < 1\/2$ if and only if $f(x) < 0$; in both cases this means $sign(f(x)) = f^*_(L, P) (x)$.
]

#figure(
  cetz.canvas({
    let etaf(x) = 0.5 + 0.4 * calc.sin(2 * calc.pi * x)
    plot.plot(
      size: (7.5, 3.8),
      axis-style: "scientific",
      x-label: $x$,
      y-label: none,
      x-tick-step: 0.25,
      y-tick-step: 0.5,
      y-min: 0,
      y-max: 1,
      x-min: 0,
      x-max: 1,
      legend: "east",
      legend-style: (stroke: none, fill: white, offset: (0.3, 0)),
      {
        plot.add-fill-between(domain: (0, 1), samples: 200, x => calc.min(etaf(x), 1 - etaf(x)), x => 0,
          style: (fill: rgb(46, 90, 138, 60), stroke: none), label: $min{eta, 1 - eta}$)
        plot.add(domain: (0, 1), samples: 200, etaf, style: (stroke: 1.2pt + rgb("#2e5a8a")), label: $eta(x)$)
        plot.add-hline(0.5, style: (stroke: (dash: "dashed", paint: gray)))
        plot.add(((0, 0.97), (0.5, 0.97)), style: (stroke: 2pt + rgb("#b5452a")), label: $f^* = 1$)
        plot.add(((0.5, 0.03), (1, 0.03)), style: (stroke: 2pt + rgb("#7a7a7a")), label: $f^* = -1$)
      },
    )
  }),
  caption: [Binary classification with $P_X$ the uniform distribution on $X = [0, 1]$ and
    $eta(x) = 1\/2 + 2\/5 sin(2 pi x)$. The Bayes classifier predicts $1$ where $eta >= 1\/2$ and $-1$
    elsewhere; the Bayes risk is the shaded area under $min{eta, 1 - eta}$.],
) <fig:learn-classification>

The Bayes classifier is a _majority vote_ under the conditional distribution: it predicts the label that is
more likely at $x$. Its risk is zero if and only if $eta in {0, 1}$ $P_X$-almost everywhere (the labels
are a deterministic function of the input), and it equals $1\/2$ if and only if $eta = 1\/2$ almost
everywhere (the input carries no information about the label).

#context-note[
  The classification loss is the "true" loss in classification, but it is neither convex nor continuous in
  $t$, and minimizing its empirical version is computationally intractable already for linear classifiers
  in general (see e.g. @shalev2014). In practice one therefore minimizes a convex _surrogate_ loss such as
  the hinge loss $max{0, 1 - y t}$ (support vector machines, @cortes1995), the logistic loss
  $log(1 + e^(-y t))$, or the least squares loss, and uses $sign(f)$ as the classifier. That this is
  reasonable is suggested by the least squares case: the regression function $f_P = 2 eta - 1$ has exactly
  the sign of the Bayes classifier, and @ex:learn-exercise-comparison shows that a small excess least squares risk
  forces a small excess classification risk. The general theory of such comparison inequalities is
  developed in @bartlett2006 and in Chapter 3 of @steinwart2008. Margin-based losses $L(y, t) = phi(y t)$ are
  studied in @sec:loss (@def:loss-margin).
]

=== Density level detection

Our third example is unsupervised and shows why losses are allowed to depend on $x$.

#example(title: [Density level detection])[
  Let $mu$ be a probability measure on $(X, cal(A))$ and let the data $x_1, ..., x_N$ be drawn from a
  distribution $Q$ with a density $g: X -> [0, oo)$ with respect to $mu$, i.e. $Q(A) = integral_A g dif mu$
  for $A in cal(A)$. For a level $rho > 0$ we want to estimate the *density level set*
  ${g >= rho} = {x in X : g(x) >= rho}$, the region where the data are concentrated. A function
  $f in meas(X)$ describes the estimate ${f >= 0}$. The *density level detection loss* is the unsupervised
  loss
  $ L(x, t) := ind_((-oo, 0]) ((g(x) - rho) sign(t)), quad x in X, t in RR, $
  with the convention $sign(0) = 1$ from @ex:learn-classification. It is measurable, and
  $L(x, t) = 1$ if and only if
  $ t >= 0 "and" g(x) <= rho quad "or" quad t < 0 "and" g(x) >= rho, $
  that is, if $x$ is put into the estimated level set although its density does not exceed $rho$, or left
  out although its density is at least $rho$ (on the boundary ${g = rho}$ every prediction is penalized).
  Errors are measured with respect to the reference measure $mu$:
  $ risk(L, mu)(f) := integral_X L(x, f(x)) dif mu(x), $
  which is the $L$-risk (@def:learn-risk) of any distribution $P$ on $X times Y$ with $P_X = mu$, since
  $L$ does not depend on $y$. If $mu({g = rho}) = 0$, then
  $ risk(L, mu)(f) = mu({f >= 0} triangle.stroked.t {g >= rho}), $
  where $triangle.stroked.t$ denotes the symmetric difference of sets. In particular $bayes(L, mu) = 0$,
  attained by $f = g - rho$, and the Bayes decision functions are exactly the $f in meas(X)$ with
  ${f >= 0} = {g >= rho}$ up to a $mu$-null set.
] <ex:learn-density-level>

#proof[
  $L$ is measurable as the composition of the measurable map $(x, t) |-> (g(x) - rho) sign(t)$ with an
  indicator of a Borel set. The description of ${L = 1}$ is immediate from $sign(t) in {-1, 1}$. Outside
  the null set $E := {g = rho}$, the loss $L(x, f(x))$ equals $1$ exactly if $f(x) >= 0 > g(x) - rho$ or
  $f(x) < 0 < g(x) - rho$, i.e. if $x in {f >= 0} triangle.stroked.t {g >= rho}$. Integrating with respect to
  $mu$ gives the formula for the risk, and the remaining claims follow since the risk is nonnegative and
  $f = g - rho$ gives the empty symmetric difference.
]

A new input $x$ is flagged as an anomaly if $f(x) < 0$. This example has a peculiarity: the loss depends
on the unknown density $g$, so, unlike in the supervised examples, we cannot even evaluate the loss on the
data. It nevertheless fits into our framework, and it can be reduced to a classification problem by
comparing the data with artificially generated samples from $mu$; we do not pursue this here. Density level
detection in the present framework is discussed in @steinwart2008, and a related kernel method for novelty
detection is the one-class SVM @schoelkopf2002.

== Empirical risk and overfitting <sec:learn-overfitting>

The risk $risk(L, P)$ cannot be computed, because $P$ is unknown. What we can compute is the average loss
on the data. It is useful to view it as the risk with respect to a particular distribution built from the
data.

#definition(title: [Empirical risk])[
  Let $D = ((x_1, y_1), ..., (x_N, y_N)) in (X times Y)^N$ be a data set. The *empirical measure* of $D$
  is the probability measure
  $ D := 1/N sum_(i=1)^N delta_((x_i, y_i)) $
  on $X times Y$, denoted by the same letter as the data set. For a loss function $L$ and $f in meas(X)$,
  the *empirical risk* of $f$ is
  $ risk(L, D)(f) := 1/N sum_(i=1)^N L(x_i, y_i, f(x_i)) = integral_(X times Y) L(x, y, f(x)) dif D(x, y). $
] <def:learn-empirical-risk>

The last equality says that the empirical risk is the $L$-risk of @def:learn-risk for the distribution $D$.
This simple observation is very useful: every statement proved for $risk(L, P)$ and _arbitrary_ $P$
(existence and uniqueness of minimizers, representer theorems, stability estimates) automatically applies to
the empirical risk. We will use this systematically in @sec:reg and @sec:stab.

=== The law of large numbers for a fixed function

Why should the empirical risk tell us anything about the risk? For a _fixed_ function $f$, the answer is the
law of large numbers.

#proposition(title: [Law of large numbers for a fixed function])[
  Let $L$ be a loss function, $P$ a probability measure on $X times Y$, and let $(x_1, y_1), (x_2, y_2), ...$
  be independent $X times Y$-valued random variables on a probability space $(Omega, Sigma, Pr)$, each
  with distribution $P$. Let $D_N := ((x_1, y_1), ..., (x_N, y_N))$ and let $f in meas(X)$ be fixed.
  + If $risk(L, P)(f) < oo$, then $risk(L, D_N)(f) -> risk(L, P)(f)$ as $N -> oo$, $Pr$-almost surely.
  + If $risk(L, P)(f) = oo$, then $risk(L, D_N)(f) -> oo$ as $N -> oo$, $Pr$-almost surely.
  + If $integral L(x, y, f(x))^2 dif P(x, y) < oo$, then $risk(L, P)(f) < oo$ and, with the variance
    $sigma_f^2 := integral (L(x, y, f(x)) - risk(L, P)(f))^2 dif P(x, y)$, for all $epsilon > 0$ and
    $N in NN$
    $ Pr(abs(risk(L, D_N)(f) - risk(L, P)(f)) >= epsilon) <= sigma_f^2 / (N epsilon^2). $
] <prop:learn-lln>

#proof[
  Let $xi_i := L(x_i, y_i, f(x_i))$. Since $(x, y) |-> L(x, y, f(x))$ is measurable, the $xi_i$ are
  independent (as measurable functions of independent random variables), identically distributed and
  nonnegative, with $EE xi_i = integral L(x, y, f(x)) dif P(x, y) = risk(L, P)(f)$. Moreover
  $risk(L, D_N)(f) = 1/N sum_(i=1)^N xi_i$.

  (i) is Kolmogorov's strong law of large numbers for i.i.d. integrable random variables
  (see Chapter 8 of @dudley2002 or Chapter 4 of @kallenberg2002).

  (ii) For $k in NN$ the truncated variables $min{xi_i, k}$ are i.i.d. and bounded, so by (i) applied to them,
  $liminf_N risk(L, D_N)(f) >= lim_N 1/N sum_(i=1)^N min{xi_i, k} = EE min{xi_1, k}$ almost surely. Intersecting
  these countably many events of probability one and using $EE min{xi_1, k} arrow.t EE xi_1 = oo$ (monotone
  convergence) gives the claim.

  (iii) Now $EE xi_1^2 < oo$, hence $EE xi_1 < oo$ and $"Var" xi_1 = sigma_f^2$. By independence, the variance
  of $1/N sum_i xi_i$ is $sigma_f^2 \/ N$; apply Chebyshev's inequality.
]

#warning-block[
  @prop:learn-lln holds for each _fixed_ $f$: the exceptional null set, and the sample size needed for a
  given accuracy, depend on $f$. It says nothing about a function $f_D$ that is _chosen after looking at the
  data_, because then $L(x_1, y_1, f_D (x_1)), ..., L(x_N, y_N, f_D (x_N))$ are no longer independent
  samples of a fixed distribution. Since there are uncountably many candidate functions, we also cannot
  simply take a union of the exceptional null sets.
]

=== Minimizing the empirical risk over all functions

The most straightforward learning method is *empirical risk minimization*: choose $f_D$ as a minimizer of
$risk(L, D)$. Let us see what happens if we minimize over _all_ measurable functions.

#proposition(title: [Interpolation learns nothing])[
  Assume that ${x} in cal(A)$ for every $x in X$. Let $L: Y times RR -> [0, oo)$ be a supervised loss with
  $L(y, y) = 0$ for all $y in Y$, and let $P$ be a distribution on $X times Y$ whose marginal has no atoms,
  i.e. $P_X ({x}) = 0$ for all $x in X$. For a data set $D = ((x_1, y_1), ..., (x_N, y_N))$ with pairwise
  distinct inputs $x_1, ..., x_N$ define
  $ hat(f)_D (x) := cases(y_i quad & "if" x = x_i "for some" i in {1, ..., N}, 0 & "if" x in.not {x_1, ..., x_N}.) $
  Then $hat(f)_D in meas(X)$ and
  + $risk(L, D)(hat(f)_D) = 0 = min{risk(L, D)(f) : f in meas(X)}$;
  + $hat(f)_D = 0$ $P_X$-almost everywhere; in particular $risk(L, P)(hat(f)_D) = risk(L, P)(0)$.
] <prop:learn-interpolation>

#proof[
  $hat(f)_D = sum_(i=1)^N y_i ind_({x_i})$ is measurable because the singletons are measurable. (i):
  $L(y_i, hat(f)_D (x_i)) = L(y_i, y_i) = 0$ for every $i$, and the empirical risk of any function is
  nonnegative. (ii): ${hat(f)_D != 0} subset.eq {x_1, ..., x_N}$, which has $P_X$-measure at most
  $sum_i P_X ({x_i}) = 0$. The risks agree by @rem:learn-risk-basic (i).
]

#figure(
  cetz.canvas({
    let fP(x) = 1.1 + 0.7 * calc.sin(2 * calc.pi * x)
    let xs = (0.06, 0.15, 0.27, 0.38, 0.5, 0.61, 0.72, 0.83, 0.94)
    let noise = (0.25, -0.3, 0.2, -0.15, 0.3, -0.25, 0.1, 0.35, -0.2)
    let pts = xs.zip(noise).map(((x, e)) => (x, fP(x) + e))
    plot.plot(
      size: (8, 4),
      axis-style: "school-book",
      x-label: $x$,
      y-label: $y$,
      x-tick-step: none,
      y-tick-step: none,
      y-min: -0.3,
      y-max: 2.3,
      x-min: 0,
      x-max: 1.02,
      legend: "north-east",
      legend-style: (stroke: none, fill: white, offset: (0.2, 0.3)),
      {
        plot.add(domain: (0, 1), samples: 150, fP,
          style: (stroke: (paint: gray, dash: "dashed", thickness: 1pt)), label: $f_P$)
        for (x, y) in pts {
          plot.add(((x, 0), (x, y)), style: (stroke: (paint: rgb("#b5452a"), dash: "dotted", thickness: 0.8pt)))
        }
        plot.add(((0, 0), (1, 0)), style: (stroke: 1.6pt + rgb("#b5452a")), label: $hat(f)_D$)
        plot.add(pts, mark: "o", mark-size: 0.12,
          mark-style: (fill: rgb("#2e5a8a"), stroke: rgb("#2e5a8a")), style: (stroke: none), label: [data])
      },
    )
  }),
  caption: [Overfitting. The data (dots) scatter around the regression function $f_P$ (dashed). The
    interpolant $hat(f)_D$ of @prop:learn-interpolation takes the value $y_i$ at $x_i$ and $0$ everywhere
    else: it has empirical risk zero, but it predicts $0$ at every new input.],
) <fig:learn-overfitting>

The interpolant $hat(f)_D$ reproduces the data perfectly and is useless on new data: for the least squares
loss and a distribution with $integral y^2 dif P < oo$, @eq:learn-ls-decomposition gives
$ risk(L, P)(hat(f)_D) - bayes(L, P) = norm(f_P)_(L^2 (P_X))^2 $
for every data set $D$, no matter how large $N$ is; for classification, $hat(f)_D$ predicts the label $1$
at every new input. The learning method $D |-> hat(f)_D$ is therefore not consistent (unless $0$ happens to
be a Bayes decision function). This phenomenon is called *overfitting*: the method has _memorized_ the data
instead of learning the structure behind them. The assumption that $P_X$ has no atoms is harmless: it holds
whenever $P_X$ has a density with respect to Lebesgue measure on $X = RR^d$, and then the inputs of an
i.i.d. sample are almost surely pairwise distinct (@ex:learn-exercise-distinct).

The deeper problem is that empirical risk minimization over $meas(X)$ is _ill-posed_. The empirical risk
depends on $f$ only through the $N$ numbers $f(x_1), ..., f(x_N)$. Every function that agrees with
$hat(f)_D$ at the data points, e.g. $hat(f)_D + h$ for any measurable $h$ vanishing at $x_1, ..., x_N$, is an
equally good empirical risk minimizer. When $P_X$ has no atoms, their risks range over _all_ values
$risk(L, P)(f)$, $f in meas(X)$, since changing a function at finitely many points does not change its
risk. The data do not
determine the minimizer, and nothing in the method tells us how to choose between these functions.

In terms of the law of large numbers: for every fixed $f$ the empirical risk converges to the risk, but for
every data set $D$ with distinct inputs
$ sup_(f in meas(X)) abs(risk(L, D)(f) - risk(L, P)(f)) >= abs(risk(L, D)(hat(f)_D) - risk(L, P)(hat(f)_D)) = risk(L, P)(0), $
so the convergence is not _uniform_ over $meas(X)$. The class of all measurable functions is too large to
be learned from finitely many examples.

== Remedies: restriction and regularization <sec:learn-remedies>

There are two classical ways out, and they are closely related: restrict the class of candidate functions,
or penalize complicated functions.

=== Hypothesis classes and the error decomposition

Let $cal(F) subset.eq meas(X)$ be a *hypothesis class*, e.g. the linear functions $x |-> ip(w, x) + b$ on
$RR^d$, polynomials of bounded degree, or neural networks of a fixed architecture. Empirical risk
minimization over $cal(F)$ produces $f_D in cal(F)$ with $risk(L, D)(f_D) = inf_(f in cal(F)) risk(L, D)(f)$
(if such a minimizer exists). Writing $cal(R)^*_(L, P, cal(F)) := inf_(f in cal(F)) risk(L, P)(f)$ for the
best risk achievable in $cal(F)$, and assuming $cal(R)^*_(L, P, cal(F)) < oo$ (note that $bayes(L, P) <= cal(R)^*_(L, P, cal(F))$), the excess
risk splits as
$ risk(L, P)(f_D) - bayes(L, P) = underbrace(risk(L, P)(f_D) - cal(R)^*_(L, P, cal(F)), "estimation error") + underbrace(cal(R)^*_(L, P, cal(F)) - bayes(L, P), "approximation error"). $ <eq:learn-error-decomposition>
The *approximation error* is deterministic: it measures how well the class can approximate the Bayes
decision function, and it can only decrease as $cal(F)$ grows. The *estimation error* is random: it measures how much
we lose because we only know $D$ instead of $P$. It typically increases with the size of $cal(F)$, because a
larger class offers more opportunities to fit the noise in the data; for $cal(F) = meas(X)$ it can be as bad as
@prop:learn-interpolation shows. Choosing $cal(F)$ is a trade-off between the two, closely related to the
bias–variance trade-off of statistics @hastie2009.

For a _finite_ class the estimation error can be controlled by the law of large numbers, because a finite
union of "bad events" is still small.

#proposition(title: [Empirical risk minimization over a finite class])[
  Let $L$ be a loss function with $L(x, y, t) <= B$ for all $(x, y, t)$ and some $B > 0$, let $P$ be a
  probability measure on $X times Y$, and let $cal(F) = {f_1, ..., f_M} subset.eq meas(X)$ be finite. For
  $D in (X times Y)^N$ let
  $ S(D) := max_(m = 1, ..., M) abs(risk(L, D)(f_m) - risk(L, P)(f_m)). $
  + For every data set $D$ and every $f_D in cal(F)$ with $risk(L, D)(f_D) = min_(f in cal(F)) risk(L, D)(f)$,
    $ risk(L, P)(f_D) - min_(f in cal(F)) risk(L, P)(f) <= 2 S(D). $
  + For every $epsilon > 0$ and $N in NN$,
    $ P^N ({D in (X times Y)^N : S(D) >= epsilon}) <= (M B^2) / (4 N epsilon^2). $
] <prop:learn-finite-class>

#proof[
  (i) For every $f in cal(F)$,
  $risk(L, P)(f_D) <= risk(L, D)(f_D) + S(D) <= risk(L, D)(f) + S(D) <= risk(L, P)(f) + 2 S(D)$; take the
  minimum over $f$.

  (ii) Under $P^N$ the coordinates $(x_1, y_1), ..., (x_N, y_N)$ are independent with distribution $P$.
  Fix $m$. The random variables $xi_i := L(x_i, y_i, f_m (x_i))$ are i.i.d. with values in $[0, B]$ and mean
  $risk(L, P)(f_m)$, and their variance is at most $B^2 \/ 4$, since
  $"Var" xi_i = EE (xi_i - B\/2)^2 - (EE xi_i - B\/2)^2 <= (B\/2)^2$. Since $risk(L, D)(f_m)$ is the mean
  of $xi_1, ..., xi_N$, Chebyshev's inequality gives, as in the proof of @prop:learn-lln (iii),
  $P^N (abs(risk(L, D)(f_m) - risk(L, P)(f_m)) >= epsilon) <= B^2 \/ (4 N epsilon^2)$. The event
  ${S(D) >= epsilon}$ is the union of these $M$ events; the union bound gives the claim.
]

Hence, with probability at least $1 - M B^2 \/ (4 N epsilon^2)$, _every_ empirical risk minimizer over
$cal(F)$ has a risk within $2 epsilon$ of the best risk in $cal(F)$. Using Hoeffding's inequality instead of
Chebyshev's, the bound improves to $2 M exp(-2 N epsilon^2 \/ B^2)$, so $cal(F)$ may even have
exponentially many elements in $N$ @shalev2014. For infinite classes, the cardinality $M$ is replaced by
measures of complexity such as the Vapnik–Chervonenkis dimension or covering numbers @vapnik1998
@shalev2014. In all cases the message is the same: _the estimation error is controlled by the complexity
of the class_, and $meas(X)$ is infinitely complex.

=== Regularization

Fixing a hypothesis class in advance is a rather rigid way to control complexity: which class should we
take, and how large? A more flexible approach keeps a large space $cal(F)$ but adds a _penalty_ for
complicated functions. Given a functional $Omega: cal(F) -> [0, oo)$ measuring the "complexity" of $f$ and a
*regularization parameter* $lambda > 0$, we minimize
$ risk(L, D)(f) + lambda Omega(f), quad f in cal(F). $ <eq:learn-regularized-general>
This is *Tikhonov regularization*, originally developed for ill-posed inverse problems @tikhonov1977. The
parameter $lambda$ balances fit and simplicity: for $lambda -> 0$ we are back to empirical risk
minimization (and to overfitting), for $lambda -> oo$ the data are ignored. Intuitively, penalizing and
restricting are two sides of the same coin: minimizing @eq:learn-regularized-general implicitly restricts
to a sublevel set ${Omega <= r}$ whose size $r$ is tuned by $lambda$, so the family of sublevel
sets ${Omega <= r}$, $r > 0$, plays the role of a nested family of hypothesis classes. Classical choices
are $Omega(f) = integral f''(x)^2 dif x$ (smoothing splines, @wahba1990) and the squared norm of the
coefficients of a linear model (ridge regression, @hoerl1970).

=== Which penalty? Hilbert spaces with continuous point evaluations

In this book $cal(F)$ is a Hilbert space $H$ of functions on $X$ and $Omega(f) = norm(f)_H^2$. The
Hilbert-space structure is what makes the theory work:

- *Existence*: bounded sequences in a Hilbert space have weakly convergent subsequences
  (@thm:app-weak-compactness). This replaces the compactness of closed balls, which fails in infinite
  dimensions, and yields minimizers of convex lower semicontinuous functionals with a bounded sublevel set
  (@lem:app-existence-minimizer).
- *Uniqueness*: $f |-> norm(f)_H^2$ is strictly convex (by the parallelogram law), so for convex losses the
  regularized problem has at most one minimizer.
- *Representation*: orthogonal projections (@thm:app-projection) will reduce the infinite-dimensional
  problem to a finite-dimensional one, and the Riesz representation theorem (@thm:app-riesz) turns
  derivatives into elements of $H$.

But not every Hilbert space of functions will do. Recall that the empirical risk only depends on the values
$f(x_1), ..., f(x_N)$. For the penalty $norm(f)_H^2$ to have any influence on these values, a function of
small norm must have small values. This is exactly continuity of the point evaluations
$delta_x: f |-> f(x)$. Without it, the penalty is worthless:

#proposition(title: [Discontinuous point evaluations make the penalty useless])[
  Let $cal(F)$ be a linear space of functions $X -> RR$ with a norm $norm(dot)$, and let $x in X$ be such
  that the linear functional $delta_x: cal(F) -> RR$, $delta_x (f) = f(x)$, is not continuous. Then:
  + for every $y in RR$ and $epsilon > 0$ there is $f in cal(F)$ with $f(x) = y$ and $norm(f) < epsilon$;
  + for every loss $L$, every $y in Y$ and every $lambda > 0$, the regularized empirical risk for the data set
    $D = ((x, y))$ with a single point satisfies
    $ inf_(f in cal(F)) (L(x, y, f(x)) + lambda norm(f)^2) = inf_(t in RR) L(x, y, t), $
    i.e. the regularization has no effect at all.
] <prop:learn-discontinuous-evaluation>

#proof[
  (i) A linear functional is continuous if and only if it is bounded on the unit ball. Hence for every
  $n in NN$ there is $g_n in cal(F)$ with $norm(g_n) <= 1$ and $abs(g_n (x)) >= n$. The function
  $f_n := (y \/ g_n (x)) g_n$ satisfies $f_n (x) = y$ and $norm(f_n) <= abs(y) \/ n$, which is smaller than
  $epsilon$ for large $n$ (for $y = 0$ take $f = 0$).
  (ii) "$>=$" holds because $L(x, y, f(x)) >= inf_t L(x, y, t)$ and the penalty is nonnegative. For "$<=$",
  let $t in RR$ and $epsilon > 0$, and choose by (i) a function $f$ with $f(x) = t$ and $norm(f) < epsilon$;
  then the regularized risk of $f$ is at most $L(x, y, t) + lambda epsilon^2$.
]

#example[
  Consider $cal(F) = C[0, 1]$ with the $L^2$ norm $norm(f)_2 = (integral_0^1 f(s)^2 dif s)^(1\/2)$ and fix
  $x in [0, 1]$. The "tent" functions $g_n (s) := max{0, 1 - n abs(s - x)}$ satisfy $g_n (x) = 1$ and
  $norm(g_n)_2^2 <= 2\/n$, so point evaluation is discontinuous. (In $L^2 [0, 1]$ itself, point evaluation is not
  even defined, since elements of $L^2$ are equivalence classes.) By contrast, let $H$ be the space of
  absolutely continuous $f: [0, 1] -> RR$ with $f(0) = 0$ and $f' in L^2 [0, 1]$, normed by
  $norm(f)_H := norm(f')_2$. Then, by the Cauchy–Schwarz inequality,
  $ abs(f(x)) = abs(integral_0^x f'(s) dif s) <= sqrt(x) norm(f')_2 <= norm(f)_H, $
  so all point evaluations are continuous, and a small norm forces small values everywhere. This space is
  the warm-up example of @sec:rkhs (@prop:rkhs-sobolev).
] <ex:learn-evaluation>

We are thus led to the central definition of this book: a *reproducing kernel Hilbert space* (RKHS) is a
Hilbert space $H$ of functions on $X$ in which every point evaluation $f |-> f(x)$ is continuous
(@def:rkhs). By the Riesz representation theorem, each point evaluation is then given by an inner product
with an element $K_x in H$: $f(x) = ip(f, K_x)_H$ for all $f in H$ (@eq:rkhs-reproducing). The function
$K(x, x') := K_(x') (x)$ is the _reproducing kernel_ of $H$, and it satisfies
$abs(f(x)) <= sqrt(K(x, x)) norm(f)_H$, so the penalty $norm(f)_H^2$ does control the values of $f$. We will
see that RKHSs correspond one-to-one to positive definite kernels (@thm:rkhs-moore-aronszajn), that $K$ can
be interpreted as an inner product of "features" (@def:rkhs-feature-map), and that the Gaussian kernel
$K(x, x') = exp(-norm(x - x')^2 \/ sigma^2)$ and many other kernels give RKHSs that are rich enough to
approximate every continuous function on a compact set uniformly (@sec:univ).

The reproducing property also shows why regularized problems in an RKHS reduce to finite dimensions. Let
$H_D := spn{K_(x_1), ..., K_(x_N)}$ and write $f = f_parallel + f_perp$ with $f_parallel in H_D$ and
$f_perp perp H_D$. Then $f_perp (x_i) = ip(f_perp, K_(x_i))_H = 0$ for all $i$, so the empirical risk of
$f$ equals that of $f_parallel$, while $norm(f)_H^2 = norm(f_parallel)_H^2 + norm(f_perp)_H^2$. Hence a
minimizer of $risk(L, D)(f) + lambda norm(f)_H^2$ must have $f_perp = 0$, i.e. it is of the form
$sum_(i=1)^N a_i K(dot, x_i)$. This is the _representer theorem_, proved in @sec:reg
(@thm:reg-representer); it is what makes kernel methods computable.

#context-note[
  Many successful methods of machine learning and statistics are of this form, although they were often
  discovered independently: support vector machines @cortes1995, kernel ridge regression (for the linear
  kernel, ridge regression @hoerl1970), smoothing splines @wahba1990, and the posterior mean of Gaussian
  process regression @rasmussen2006 are all minimizers of a
  regularized empirical risk over an RKHS (or, for splines, of a closely related problem with a
  seminorm penalty) for suitable $L$ and $K$. See @schoelkopf2002 and @steinwart2008 for the
  machine learning perspective and @berlinet2004 for the statistical one.
]

== Roadmap of the book <sec:learn-roadmap>

We can now formulate the problem that this book studies. Let $H$ be an RKHS on $X$, $L$ a loss function, and
$lambda > 0$. For a distribution $P$ and a data set $D$ we consider the *regularized risks*
$ risk(L, P, lambda)(f) := risk(L, P)(f) + lambda norm(f)_H^2, quad
  risk(L, D, lambda)(f) := risk(L, D)(f) + lambda norm(f)_H^2, quad f in H, $
and their minimizers
$ f_(P, lambda) in argmin_(f in H) risk(L, P, lambda)(f), quad
  f_(D, lambda) in argmin_(f in H) risk(L, D, lambda)(f) $
(precise definitions in @def:reg-regularized-risk). The function $f_(D, lambda)$ is what an algorithm
computes from the data; $f_(P, lambda)$ is its "infinite-sample" counterpart, which we can study with the
tools of analysis because it does not depend on random data. Two running examples will accompany us:

- *Support vector machines* (SVMs) @cortes1995 are used for binary classification, $Y = {-1, 1}$, and
  minimize the regularized empirical risk of the hinge loss $L(y, t) = max{0, 1 - y t}$.
- *Kernel ridge regression* uses the least squares loss $L(y, t) = (y - t)^2$. Here $f_(D, lambda)$ can be
  computed in closed form: $f_(D, lambda) = sum_(i=1)^N a_i K(dot, x_i)$, where the coefficient vector
  $a in RR^N$ solves the linear system $(bold(K) + lambda N I) a = (y_1, ..., y_N)^top$ with the Gram
  matrix $bold(K) = (K(x_i, x_j))_(i, j = 1)^N$ (@ex:reg-krr).

=== Guiding questions

The theory is organized around the following eight questions, which will be answered one by one.

#table(
  columns: (auto, 1fr, auto),
  stroke: none,
  inset: (x: 6pt, y: 5pt),
  align: (left, left, left),
  table.hline(stroke: 0.8pt),
  table.header([], [*Question*], [*Answered in*]),
  table.hline(stroke: 0.4pt),
  [*Q1*], [_Existence:_ is there a minimizer $f_(P, lambda)$ of $risk(L, P, lambda)$ over $H$?], [@thm:reg-existence],
  [*Q2*], [_Uniqueness:_ is $f_(P, lambda)$ uniquely determined?], [@prop:reg-uniqueness],
  [*Q3*], [_Representation:_ how can $f_(P, lambda)$ be represented?], [@thm:reg-general-representer],
  [*Q4*], [_Dependence on $lambda$:_ how does $f_(P, lambda)$ depend on $lambda$?], [@thm:stab-lambda],
  [*Q5*], [_Error analysis:_ how large is $risk(L, P)(f_(P, lambda)) - bayes(L, P)$, and what about
    $risk(L, P)(f_(D, lambda)) - bayes(L, P)$?], [@sec:stab-outlook, @thm:univ-bayes],
  [*Q6*], [_Existence_ of a minimizer $f_(D, lambda)$ of the regularized empirical risk?], [@thm:reg-existence, @thm:reg-representer],
  [*Q7*], [_Representation_ of $f_(D, lambda)$?], [@thm:reg-representer],
  [*Q8*], [_Relation_ between $f_(P, lambda)$ and $f_(D, lambda)$?], [@thm:stab-measure],
  table.hline(stroke: 0.8pt),
)

Since the empirical risk is a risk (@def:learn-empirical-risk), the answers to Q1–Q3 largely contain
those to Q6–Q7 as special cases; but for $D$ we get more, notably the finite-dimensional representation
above, and existence without any boundedness assumption on the kernel. The questions fit together through
the following decomposition of the excess risk of $f_(D, lambda)$, the regularized analogue of
@eq:learn-error-decomposition. Let $cal(R)^*_(L, P, H) := inf_(f in H) risk(L, P)(f)$ be the best risk
achievable in $H$ and assume that it is finite. Then
$ risk(L, P)(f_(D, lambda)) - bayes(L, P) =
  underbrace(risk(L, P)(f_(D, lambda)) - risk(L, P)(f_(P, lambda)), "sample error (Q8)")
  + underbrace(risk(L, P)(f_(P, lambda)) - cal(R)^*_(L, P, H), "regularization error (Q4)")
  + underbrace(cal(R)^*_(L, P, H) - bayes(L, P), "richness of" H). $
Compared with @eq:learn-error-decomposition, the estimation error of $f_(D, lambda)$ within $H$ has been
split into two parts: the sample error, which is caused by the finite data, and the regularization error,
which is caused by the penalty and would be present even if $P$ were known. The last term is the
approximation error of the class $H$.
- The *sample error* is random. It is controlled by the stability of $P |-> f_(P, lambda)$ with respect to
  changes of the distribution (Q8), applied with the empirical measure $D$ in place of the second
  distribution. For convex Nemitski losses and bounded kernels, @thm:stab-measure bounds
  $norm(f_(P, lambda) - f_(D, lambda))_H$ by $1\/lambda$ times the distance in $H$ between the means of one
  and the same $H$-valued function with respect to $P$ and with respect to $D$. By a law of large numbers
  in $H$, this distance is typically of order $1\/sqrt(N)$, and for Lipschitz continuous losses a small
  distance in $H$ implies a small difference of risks.
- The *regularization error* is deterministic. Since
  $risk(L, P)(f_(P, lambda)) <= risk(L, P, lambda)(f_(P, lambda))$, it is bounded by the _approximation
  error function_ $A(lambda) := inf_(f in H) risk(L, P, lambda)(f) - cal(R)^*_(L, P, H)$. Its behaviour as $lambda -> 0$ is
  studied in @sec:stab (@def:stab-approx-error, @prop:stab-approx-error); in particular, $A(lambda) -> 0$ as
  $lambda -> 0$ whenever $cal(R)^*_(L, P, H) < oo$.
- The *richness* term is deterministic and does not involve $lambda$. It vanishes if $H$ is rich enough.
  This is where universal kernels enter: for a universal kernel on a compact metric space and a continuous
  $P$-integrable Nemitski loss, $cal(R)^*_(L, P, H) = bayes(L, P)$ (@thm:univ-bayes).

The sample error calls for a small $1\/(lambda sqrt(N))$, the regularization error for a small
$lambda$. Choosing $lambda = lambda_N -> 0$ slowly enough as $N -> oo$ makes both small, and this leads to
consistency (@def:learn-consistency). In @sec:stab-outlook this is carried out for convex, Lipschitz
continuous losses and bounded measurable kernels: if $lambda_N -> 0$ and $lambda_N^2 N -> oo$, then
$risk(L, P)(f_(D, lambda_N)) -> cal(R)^*_(L, P, H)$ in probability, and for universal kernels the limit
is the Bayes risk.

=== Plan of the book

- *@sec:loss: Loss functions and their risks.* Properties of the loss $L$, such as convexity, continuity,
  Lipschitz continuity and differentiability in $t$, are transferred to the risk functional
  $risk(L, P)$ on spaces like $L^p (P_X)$. This is the analytic toolbox for the optimization problems
  above. A catalogue of standard losses for classification and regression is included.
- *@sec:rkhs: Reproducing kernel Hilbert spaces.* The hypothesis spaces: the correspondence between
  kernels and RKHSs (Moore–Aronszajn), feature maps and the kernel trick, constructions of kernels, and
  measurability, boundedness and continuity of the functions in an RKHS.
- *@sec:mercer: Integral operators and Mercer's theorem.* The RKHS $H_K$ as a subspace of $L^2 (mu)$,
  described through the eigenvalues and eigenfunctions of an integral operator. This shows that
  $norm(f)_H$ is a measure of smoothness, and it gives concrete examples on the torus and on the sphere.
- *@sec:univ: Universal kernels.* When is an RKHS dense in the continuous functions? This answers the
  question when the richness term of the error decomposition vanishes.
- *@sec:reg: Regularized risk minimization.* Existence, uniqueness and representation of $f_(P, lambda)$
  and $f_(D, lambda)$ (Q1–Q3, Q6, Q7), kernel ridge regression, subdifferential calculus for
  non-differentiable losses, and support vector machines.
- *@sec:stab: Stability of regularized solutions.* The dependence of $f_(P, lambda)$ on $lambda$ (Q4)
  and on $P$ (Q8), and an outlook on how these results yield consistency (Q5).
- *@sec:app* collects the background from measure theory, functional analysis and convex analysis that
  is used in the text.

@sec:loss and @sec:rkhs are largely independent of each other and may be read in either order.
@sec:mercer and @sec:univ deepen the understanding of RKHSs. The existence and representation theory of
@sec:reg does not depend on them. @sec:univ is needed for the last step of the consistency argument in
@sec:stab, while @sec:mercer provides the spectral picture behind several examples and behind the faster
learning rates mentioned there.

== Summary

- Data are modelled as an i.i.d. sample from an unknown distribution $P$ on $X times Y$, which
  disintegrates into the input distribution $P_X$ and the conditional distributions $P(dot | x)$
  (@lem:learn-regular-conditional). This requires some regularity of $Y$; closed $Y subset.eq RR$ is enough.
- A loss function $L(x, y, t)$ measures the cost of a prediction; the risk $risk(L, P)(f)$ is the expected
  loss of $f$, and the Bayes risk $bayes(L, P)$ is the best possible risk. Bayes decision functions can be
  found by minimizing the inner risk pointwise (@lem:learn-inner-risk).
- For least squares, the Bayes function is the conditional mean $f_P$ and the excess risk is
  $norm(f - f_P)_(L^2 (P_X))^2$ (@ex:learn-least-squares); for classification, it is the majority vote
  $f^*_(L, P) = sign(2 eta - 1)$ with Bayes risk $integral min{eta, 1 - eta} dif P_X$ (@ex:learn-classification).
- The empirical risk is the risk with respect to the empirical measure. It converges to the risk for each
  fixed $f$ (@prop:learn-lln), but minimizing it over all functions leads to overfitting
  (@prop:learn-interpolation).
- Complexity must be controlled, either by restricting the hypothesis class (approximation vs. estimation
  error) or by a penalty $lambda Omega(f)$. The choice $Omega(f) = norm(f)_H^2$ on a Hilbert space with
  continuous point evaluations, an RKHS, combines good geometry with control of function values
  (@prop:learn-discontinuous-evaluation).
- The book studies the minimizers $f_(P, lambda)$ and $f_(D, lambda)$ of the regularized risks along the
  questions Q1–Q8. The excess risk of $f_(D, lambda)$ splits into the sample error, the regularization
  error and the richness of $H$; each of them is controlled by a different part of the theory.

== Notes and further reading

The formulation of learning as the minimization of an expected loss under an unknown distribution, with
the empirical risk as a computable substitute, goes back to the work of Vapnik and Chervonenkis on
statistical learning theory; @vapnik1998 is a comprehensive account, including the uniform laws of large
numbers that are needed to analyse empirical risk minimization over infinite classes. For classification,
@devroye1996 is the standard reference on the Bayes classifier, consistency and universal consistency, and
it also shows that no learning method can achieve a uniform rate of convergence over all distributions;
@shalev2014 presents the related "no free lunch" theorem and the bias–complexity trade-off (Ch. 5) in
textbook form, as well as the analysis of finite classes via Hoeffding's inequality that sharpens
@prop:learn-finite-class. @hastie2009 discusses the bias–variance trade-off and many practical methods.

Our setting and notation follow @steinwart2008 closely; its Chapter 2 treats loss functions and risks,
including density level detection, and its Chapter 3 develops inner risks and the comparison of risks for
surrogate losses systematically; see also @bartlett2006. Regular conditional probabilities and
disintegration are treated in @dudley2002 and @kallenberg2002.

Tikhonov regularization originates in the theory of ill-posed inverse problems @tikhonov1977. Its use with
reproducing kernel Hilbert spaces in statistics goes back to the spline smoothing literature, in particular
the representer theorem of @kimeldorf1971; see @wahba1990. The general theory of reproducing kernels is due
to @aronszajn1950; modern introductions are @berlinet2004 and @paulsen2016. For the machine learning side
of kernel methods, including SVMs, see @schoelkopf2002; the soft-margin SVM was introduced in
@cortes1995. An approximation-theoretic view of learning with kernels, with emphasis on least squares, is
given in @cucker2007.

== Exercises

#exercise(title: [A metric space is not enough])[
  Let $lambda$ denote Lebesgue measure on $[0, 1]$ and let $E subset [0, 1]$ be a set of outer measure
  $1$ and inner measure $0$ (such sets exist by the axiom of choice, e.g. Bernstein sets). Equip $Y := E$
  with the metric of $RR$, so $borel(Y) = {B inter E : B in borel([0, 1])}$.
  + Show that $mu(B inter E) := lambda(B)$ is a well-defined probability measure on $borel(Y)$.
    _Hint:_ a Borel set disjoint from $E$ is a $lambda$-null set.
  + Let $X := [0, 1]$ with $cal(A) = borel([0, 1])$ and let $P$ be the image of $mu$ under the measurable
    map $Y -> X times Y$, $y |-> (y, y)$. Show that $P_X = lambda$ and
    $P(A times (B inter E)) = lambda(A inter B)$ for Borel sets $A, B subset.eq [0, 1]$.
  + Suppose that $P(dot | dot)$ is a regular conditional probability of $P$. Show that there is a Borel set
    $G subset.eq [0, 1]$ with $lambda(G) = 1$ such that for all $x in G$ and all rational $a < b$ one has
    $P((a, b) inter E | x) = ind_((a, b)) (x)$. Deduce that $x in E$ for every $x in G$ (consider
    rational intervals shrinking to $x$) and derive a contradiction.
] <ex:learn-exercise-no-conditional>

#exercise(title: [The median minimizes the absolute loss])[
  Let $Q$ be a probability measure on $RR$ and $h(t) := integral_RR (abs(y - t) - abs(y)) dif Q(y)$.
  + Show that $h$ is finite (without any moment assumption) and convex.
  + Show that $h$ has the right derivative $h'_+ (t) = 2 Q((-oo, t]) - 1$ and the left derivative
    $h'_- (t) = 1 - 2 Q([t, oo))$. _Hint:_ for $t < s$,
    $abs(y - s) - abs(y - t)$ equals $s - t$ for $y <= t$, equals $t - s$ for $y >= s$, and lies in
    $(t - s, s - t)$ for $t < y < s$.
  + Conclude that $t$ minimizes $h$ if and only if $Q((-oo, t]) >= 1\/2$ and $Q([t, oo)) >= 1\/2$, i.e. if
    $t$ is a median of $Q$. The set of medians is a nonempty compact interval.
  + Deduce the claim of @rem:learn-lp about Bayes decision functions for the absolute loss, assuming
    $integral abs(y) dif P < oo$. _Hint:_ the smallest median of $P(dot | x)$,
    $ m(x) := min{t in RR : P((-oo, t] | x) >= 1\/2}, $
    is measurable in $x$, because ${m <= t} = {x : P((-oo, t] | x) >= 1\/2}$; then use
    @lem:learn-inner-risk.
] <ex:learn-exercise-median>

#exercise(title: [Excess classification risk])[
  In the setting of @ex:learn-classification, show that for every $f in meas(X)$
  $ risk(L, P)(f) - bayes(L, P) = integral_({sign f != f^*_(L, P)}) abs(2 eta(x) - 1) dif P_X (x). $
  Interpret: errors at inputs where $eta$ is close to $1\/2$ are cheap.
] <ex:learn-exercise-excess-classification>

#exercise(title: [Least squares controls classification])[
  Let $Y = {-1, 1}$, let $L_"ls"$ be the least squares loss and $L_"class"$ the classification loss. Recall
  that $f_P = 2 eta - 1$. Using @ex:learn-exercise-excess-classification, show that for every $f in meas(X)$
  $ risk(L_"class", P)(f) - bayes(L_"class", P) <= sqrt(risk(L_"ls", P)(f) - bayes(L_"ls", P)). $
  _Hint:_ $f^*_(L_"class", P) = sign f_P$; if $sign f(x) != sign f_P (x)$, then $abs(f_P (x)) <= abs(f(x) - f_P (x))$; then use the
  Cauchy–Schwarz inequality.
] <ex:learn-exercise-comparison>

#exercise(title: [Samples have distinct inputs])[
  Let $X$ be a separable metric space with its Borel $sigma$-algebra and let $P_X$ have no atoms. Show that
  for an i.i.d. sample $x_1, ..., x_N$ from $P_X$ the inputs are pairwise distinct almost surely.
  _Hint:_ the diagonal ${(x, x') : x = x'}$ is closed in $X times X$ and belongs to
  $borel(X) times.o borel(X)$ because $X$ is separable; compute its $P_X times.o P_X$-measure with Fubini's
  theorem.
] <ex:learn-exercise-distinct>

#exercise(title: [Least squares without second moments])[
  Let $X = [0, 1]$ with the uniform distribution, $Y = RR$, and $y = g(x)$ deterministic with
  $g(x) := x^(-1\/2)$ for $x > 0$ and $g(0) := 0$. Show that $integral y^2 dif P = oo$, so
  @ex:learn-least-squares does not apply, but that $bayes(L, P) = 0$ for the least squares loss and $g$ is
  a Bayes decision function. What is $risk(L, P)(f)$ for $f in L^2 (P_X)$?
] <ex:learn-exercise-ls-moment>

#exercise(title: [Continuity of point evaluations])[
  Let $H$ be the space of @ex:learn-evaluation (it is studied in detail in @prop:rkhs-sobolev). Show that
  $norm(dot)_H$ is a norm on $H$ (why is the
  condition $f(0) = 0$ needed?), and that for $x, x' in [0, 1]$ and $f in H$
  $ abs(f(x) - f(x')) <= sqrt(abs(x - x')) norm(f)_H. $
  Conclude that a sequence converging in $H$ converges uniformly on $[0, 1]$.
] <ex:learn-exercise-sobolev>
