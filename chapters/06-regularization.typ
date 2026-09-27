#import "/template.typ": *

= Regularized Risk Minimization <sec:reg>

We have now assembled all the ingredients of the learning method announced in @sec:learn-roadmap. From
@sec:loss we know how analytic properties of a loss $L$ (convexity, continuity, differentiability, growth)
translate into properties of the risk functional $f |-> risk(L, P)(f)$. From @sec:rkhs we have the
hypothesis spaces: reproducing kernel Hilbert spaces $H$, whose norm controls the values of their
functions pointwise. In this chapter we put the two together and study the *regularized risk*
$ risk(L, P, lambda)(f) = risk(L, P)(f) + lambda norm(f)_H^2, quad f in H, $
together with its empirical counterpart $risk(L, D, lambda)$, in which the unknown distribution $P$ is
replaced by the empirical measure of a data set $D$. Minimizers of these functionals, denoted
$f_(P, lambda)$ and $f_(D, lambda)$, are the objects that support vector machines, kernel ridge
regression, kernel logistic regression and many other kernel methods compute.

The chapter answers the first group of guiding questions of @sec:learn-roadmap. First, we show that for
convex losses and under mild integrability assumptions $f_(P, lambda)$ and $f_(D, lambda)$ exist and are
unique (@thm:reg-existence,
@prop:reg-uniqueness). Second, the *representer theorem* (@thm:reg-representer) shows that the
infinite-dimensional problem for $f_(D, lambda)$ is really an $N$-dimensional one:
$f_(D, lambda) = sum_(i=1)^N a_i K(dot, x_i)$. This is the mathematical core of the "kernel trick".
Third, for differentiable losses the minimizer satisfies an integral equation
@eq:reg-integral-equation[], which for the least squares loss becomes the linear system
$(bold(K) + lambda N I) bold(a) = bold(y)$ of kernel ridge regression. Finally, to treat non-differentiable
losses such as the hinge loss of the SVM, we introduce *subdifferentials* of convex functions and prove
the *general representer theorem* (@thm:reg-general-representer):
$f_(P, lambda) = -1/(2 lambda) integral h(x, y) Phi(x) dif P(x, y)$ for a function $h$ with values in the
subdifferential of the loss. For SVMs this explains support vectors and box constraints; in @sec:stab
it will be the key to the stability of $f_(P, lambda)$ with respect to $P$.


== The regularized risk <sec:reg-problem>

Recall the basic problem (@def:learn-risk, @def:learn-bayes): given a loss
$L: X times Y times RR -> [0, oo)$ and a distribution $P$ on $X times Y$, we would like to find a
measurable $f: X -> RR$ whose risk $risk(L, P)(f)$ is close to the Bayes risk
$bayes(L, P) = inf {risk(L, P)(f) : f in meas(X)}$. There are two obstacles.

- *The distribution is unknown.* We only observe a data set $D = ((x_1, y_1), ..., (x_N, y_N))$. The
  natural idea is to minimize the empirical risk $risk(L, D)$ instead (@def:learn-empirical-risk). Over
  the class of *all* measurable functions this is disastrous (@sec:learn-overfitting): a function that
  reproduces the labels at the data points and is zero elsewhere has empirical risk zero but has learned
  nothing.
- *The space $meas(X)$ is too big even when $P$ is known.* It carries no useful norm or topology: there is
  no compactness to guarantee existence of minimizers, no way to express that a function is "simple", and
  point values of a function are not controlled by any norm.

The remedy, prepared in @sec:learn and @sec:rkhs, has two parts. We restrict the search to a Hilbert space $H$ of
functions on $X$ in which point evaluations are continuous, an RKHS; and we *penalize* complexity by adding
a multiple of the squared norm.

#definition(title: [Regularized risk])[
  Let $(X, cal(A))$ be a measurable space, $Y subset.eq RR$ closed, $L: X times Y times RR -> [0, oo)$ a
  loss, and $H$ an RKHS of real-valued functions on $X$ all of whose elements are measurable. For a
  distribution $P$ on $X times Y$ and $lambda > 0$, the *regularized $L$-risk* is
  $ risk(L, P, lambda): H -> [0, oo], quad risk(L, P, lambda)(f) := risk(L, P)(f) + lambda norm(f)_H^2 = integral_(X times Y) L(x, y, f(x)) dif P(x, y) + lambda norm(f)_H^2. $
  For a data set $D = ((x_1, y_1), ..., (x_N, y_N)) in (X times Y)^N$, the *regularized empirical risk* is
  $ risk(L, D, lambda)(f) := risk(L, D)(f) + lambda norm(f)_H^2 = 1/N sum_(i=1)^N L(x_i, y_i, f(x_i)) + lambda norm(f)_H^2, quad f in H. $
  The number $lambda$ is the *regularization parameter*. A minimizer of $risk(L, P, lambda)$ over $H$ is
  denoted $f_(P, lambda)$ (or $f_(L, P, lambda)$ if the loss must be named), a minimizer of
  $risk(L, D, lambda)$ is denoted $f_(D, lambda)$:
  $ risk(L, P, lambda)(f_(P, lambda)) = inf_(f in H) risk(L, P, lambda)(f), quad risk(L, D, lambda)(f_(D, lambda)) = inf_(f in H) risk(L, D, lambda)(f). $
] <def:reg-regularized-risk>

Since the empirical measure $D = 1/N sum_i delta_((x_i, y_i))$ is a distribution on $X times Y$ and
$risk(L, D)$ is its risk, $risk(L, D, lambda)$ is the special case $P = D$ of $risk(L, P, lambda)$. We
keep both notations because they play different roles: $f_(D, lambda)$ is what an algorithm computes,
$f_(P, lambda)$ is the idealized "infinite-sample" version it should approximate.

Before we turn to the mathematics, let us discuss the choice of the penalty $lambda norm(f)_H^2$.

*A trade-off.* The two terms pull in opposite directions. The risk term rewards functions that fit the
data (or the distribution), the penalty rewards functions of small norm. The parameter $lambda$ sets the
exchange rate. For large $lambda$ the penalty dominates, and we will see in @prop:reg-norm-bound that
$norm(f_(P, lambda))_H <= sqrt(risk(L, P)(0) \/ lambda)$, so $f_(P, lambda) -> 0$ as $lambda -> oo$ whenever
$risk(L, P)(0) < oo$. For
small $lambda$ we approach unregularized risk minimization over $H$; in the empirical case this brings back
the danger of overfitting. How $lambda$ should depend on the sample size $N$ is one of the central
questions of @sec:stab.

*What the RKHS norm measures.* By the reproducing property (@eq:rkhs-reproducing) and the
Cauchy–Schwarz inequality, every $f in H$ satisfies
$ abs(f(x)) <= sqrt(K(x, x)) norm(f)_H quad "and" quad abs(f(x) - f(x')) = abs(ip(f, Phi(x) - Phi(x'))_H) <= norm(f)_H norm(Phi(x) - Phi(x'))_H, $
where $Phi(x) = K(dot, x)$ is the canonical feature map. A function of small norm therefore has small
values and varies slowly with respect to the geometry that the kernel induces on $X$. Two examples make this
concrete. For the kernel $K(x, x') = min{x, x'}$ on $[0, 1]$ (@prop:rkhs-sobolev), $norm(f)_H^2 = integral_0^1 f'(x)^2 dif x$
is the "energy" of $f$, so the penalty discourages steep slopes. For a continuous kernel on a compact
metric space $X$ and a finite Borel measure $mu$ with $supp mu = X$, every $f in H$ satisfies
$norm(f)_H^2 = sum_j ip(f, e_j)_(L^2(mu))^2 \/ lambda_j$ with the eigenpairs $(lambda_j, e_j)$ of the
integral operator $T_K$ (@prop:mercer-rkhs-spectral), so components of
$f$ along eigenfunctions with small eigenvalues $lambda_j$ (typically: highly oscillating ones) are
penalized heavily. In both cases, "small norm" means "simple" or "smooth" in a precise sense.

*Why a squared Hilbert norm?* Other penalties are conceivable, e.g. $lambda norm(f)_H$, or the constraint
$norm(f)_H <= r$ instead of a penalty. The squared Hilbert norm is singled out by several convenient
properties that we will use again and again:
- it is *strictly convex*, by the parallelogram law (see @eq:reg-parallelogram below). This yields
  uniqueness of minimizers even for losses that are not strictly convex, such as the hinge loss. The norm
  itself is not strictly convex: it is linear along rays;
- it is *differentiable* everywhere with derivative $g |-> 2 ip(g, f)_H$, so first-order optimality
  conditions become equations in $H$ via the Riesz representation theorem (@thm:app-riesz);
- it is compatible with *orthogonal projections*: if $f = f_1 + f_2$ with $f_1 perp f_2$, then
  $norm(f)_H^2 = norm(f_1)_H^2 + norm(f_2)_H^2$. This is the heart of the representer theorem;
- for the least squares loss it leads to *linear* equations (@ex:reg-krr).

#context-note[
  Adding $lambda norm(f)^2$ to an objective is known as *Tikhonov regularization*, after its use for
  ill-posed inverse problems @tikhonov1977. There one wants to solve $A f = g$ for a compact operator $A$
  between Hilbert spaces; the solution (if it exists) does not depend continuously on the data $g$. The
  regularized problem $min_f norm(A f - g)^2 + lambda norm(f)^2$ has the unique solution
  $(A^* A + lambda)^(-1) A^* g$, which depends continuously on $g$. The regularized least squares problem
  of this chapter is the statistical analogue: $A$ is (roughly) the evaluation of $f$ at the random inputs,
  and $g$ are the noisy outputs. In statistical learning theory, minimizing $risk(L, D, lambda)$ is also
  called *regularized empirical risk minimization*; see @vapnik1998 for the related principle of
  structural risk minimization.
]

The following examples are the running examples of this chapter; all three losses are convex
(@ex:loss-catalogue).

#example(title: [Three regularized kernel methods])[
  + *Support vector machine (SVM).* For binary classification, $Y = {-1, 1}$, and the hinge loss
    $L(y, t) = max{0, 1 - y t}$, the minimizer
    $ f_(D, lambda) = argmin_(f in H) 1/N sum_(i=1)^N max{0, 1 - y_i f(x_i)} + lambda norm(f)_H^2 $
    is the decision function of the (soft-margin) SVM without offset; new inputs are classified by
    $sign f_(D, lambda) (x)$. The hinge loss is convex but not differentiable at $y t = 1$.
  + *Kernel ridge regression.* For $Y = RR$ and the least squares loss $L(y, t) = (y - t)^2$,
    $ f_(D, lambda) = argmin_(f in H) 1/N sum_(i=1)^N (y_i - f(x_i))^2 + lambda norm(f)_H^2. $
    For the linear kernel $K(x, x') = ip(x, x')$ on $RR^d$ this is classical ridge regression
    (@ex:reg-exr-ridge).
  + *Kernel logistic regression.* For $Y = {-1, 1}$ and the logistic loss
    $L(y, t) = log(1 + e^(-y t))$, which is convex and differentiable.
] <ex:reg-running>


== The guiding questions <sec:reg-questions>

In the notation of this chapter, the guiding questions of @sec:learn-roadmap ask for existence (Q1),
uniqueness (Q2) and a representation (Q3) of $f_(P, lambda)$; for its dependence on $lambda$ (Q4); for an
error analysis of $risk(L, P)(f_(P, lambda)) - bayes(L, P)$ and $risk(L, P)(f_(D, lambda)) - bayes(L, P)$
(Q5); for existence (Q6) and a computable representation (Q7) of $f_(D, lambda)$; and for the relation
between $f_(P, lambda)$ and $f_(D, lambda)$ (Q8). This chapter answers Q1, Q2 and Q6
(@thm:reg-existence, @prop:reg-uniqueness, @thm:reg-representer) and Q3 and Q7 (@thm:reg-representer,
@thm:reg-integral-equation, @thm:reg-general-representer and their empirical versions). Questions Q4 and
Q8 are the subject of @sec:stab (@thm:stab-lambda, @thm:stab-measure), which also sketches the answer to
Q5 (@sec:stab-outlook) building on universal kernels (@sec:univ).


== Existence and uniqueness <sec:reg-existence>

Throughout this section and the rest of the chapter we use the following standing assumptions.
$(X, cal(A))$ is a measurable space, $Y subset.eq RR$ is closed, $P$ is a distribution on $X times Y$, and
$L: X times Y times RR -> [0, oo)$ is a loss (@def:learn-loss). $H$ is an RKHS of *real-valued*
functions on $X$ with kernel $K$ and canonical feature map
$ Phi: X -> H, quad Phi(x) := K_x = K(dot, x), $
so that $f(x) = ip(f, Phi(x))_H$ for all $f in H$ and $x in X$, and $K(x, x') = K(x', x)$. As in
@sec:rkhs, $K$ is called *measurable* if it is $cal(A) times.o cal(A)$-measurable. All we actually use is
the weaker property that every section $K(dot, x): X -> RR$ is measurable, which by @prop:rkhs-measurable
holds if and only if every $f in H$ is measurable; then $risk(L, P)(f) in [0, oo]$ is defined for every
$f in H$, and all results below that assume a measurable kernel remain true. Recall that $K$ is *bounded* if $abs(K)_oo = sup_(x in X) sqrt(K(x, x)) < oo$
(@def:rkhs-kernel-norms); then $norm(f)_oo <= abs(K)_oo norm(f)_H$ for all $f in H$ (@prop:rkhs-bounded).

#remark(title: [The empirical case])[
  Everything proved below for a general distribution $P$ applies to $P = D$. Measurability plays no
  role there: $risk(L, D)(f)$ only involves the numbers $f(x_1), ..., f(x_N)$, and it is finite for every
  function $f$. If $X$ carries no natural $sigma$-algebra, we may equip it with the power set $2^X$; then
  every function on $X$ and every kernel is measurable, and $L$ stays measurable because
  $cal(A) times.o borel(Y) times.o borel(RR) subset.eq 2^X times.o borel(Y) times.o borel(RR)$.
] <rem:reg-empirical>

=== An a priori bound

Before asking whether minimizers exist, let us see what any minimizer must satisfy. The trick is to
compare with the simplest candidate, $f = 0$, whose regularized risk is just $risk(L, P)(0)$.

#proposition(title: [A priori bounds])[
  In the setting of this section, let $lambda > 0$ and assume $risk(L, P)(0) < oo$.
  + Every $f in H$ with $risk(L, P, lambda)(f) <= risk(L, P)(0)$ satisfies $norm(f)_H <= sqrt(risk(L, P)(0) \/ lambda)$.
  + If $f_(P, lambda) in H$ is a minimizer of $risk(L, P, lambda)$, then
    $ lambda norm(f_(P, lambda))_H^2 + risk(L, P)(f_(P, lambda)) <= risk(L, P)(0), $
    in particular $norm(f_(P, lambda))_H <= sqrt(risk(L, P)(0) \/ lambda)$ and $risk(L, P)(f_(P, lambda)) <= risk(L, P)(0)$.
  + If moreover $K$ is bounded, then $norm(f_(P, lambda))_oo <= abs(K)_oo sqrt(risk(L, P)(0) \/ lambda)$.
] <prop:reg-norm-bound>

#proof[
  (i) Since $risk(L, P)(f) >= 0$, we have $lambda norm(f)_H^2 <= risk(L, P, lambda)(f) <= risk(L, P)(0)$.
  (ii) By minimality, $risk(L, P, lambda)(f_(P, lambda)) <= risk(L, P, lambda)(0) = risk(L, P)(0)$; now use (i).
  (iii) follows from (ii) and $sup_(x in X) abs(f(x)) <= abs(K)_oo norm(f)_H$ (@prop:rkhs-bounded).
]

For the empirical measure the bound is explicit: $risk(L, D)(0) = 1/N sum_i L(x_i, y_i, 0)$. For the
hinge loss $L(y, 0) = 1$, so $norm(f_(D, lambda))_H <= lambda^(-1\/2)$ *whatever the data*; for the least
squares loss and $abs(y_i) <= M$ we get $norm(f_(D, lambda))_H <= M lambda^(-1\/2)$. Intuitively, the
regularized problem implicitly searches in a ball of radius of order $lambda^(-1\/2)$: the smaller
$lambda$, the larger (and more complex) the effective hypothesis class.

=== Uniqueness

The risk $risk(L, P)$ is rarely strictly convex as a functional on $H$. The hinge loss is piecewise linear,
and even for a strictly convex loss, $risk(L, P)(f)$ only depends on the values of $f$ on a set of full
$P_X$-measure, so strict convexity can at best give uniqueness $P_X$-almost everywhere. The regularizer
repairs this. For $f, g in H$ and $theta in [0, 1]$ we have the identity (for $theta = 1\/2$ the
parallelogram law)
$ norm((1 - theta) f + theta g)_H^2 = (1 - theta) norm(f)_H^2 + theta norm(g)_H^2 - theta (1 - theta) norm(f - g)_H^2, $ <eq:reg-parallelogram>
since both sides equal
$(1 - theta)^2 norm(f)_H^2 + 2 theta (1 - theta) ip(f, g)_H + theta^2 norm(g)_H^2$. In particular,
$norm(dot)_H^2$ is strictly convex, with a quantitative gap $theta (1 - theta) norm(f - g)_H^2$.

#proposition(title: [Uniqueness])[
  In the setting of this section, let $L$ be convex, $lambda > 0$, and assume that there is $f_0 in H$ with
  $risk(L, P)(f_0) < oo$. Then $risk(L, P, lambda)$ has at most one minimizer in $H$.
] <prop:reg-uniqueness>

#proof[
  Let $m := inf_(f in H) risk(L, P, lambda)(f)$; then $m <= risk(L, P, lambda)(f_0) < oo$. Suppose that
  $f_1 != f_2$ are both minimizers, so $risk(L, P, lambda)(f_1) = risk(L, P, lambda)(f_2) = m$, and in
  particular $risk(L, P)(f_1), risk(L, P)(f_2) < oo$. Let $g := 1/2 (f_1 + f_2) in H$. Since
  $L(x, y, dot)$ is convex,
  $ L(x, y, g(x)) <= 1/2 L(x, y, f_1 (x)) + 1/2 L(x, y, f_2 (x)) quad "for all" (x, y) in X times Y, $
  and integrating these nonnegative measurable functions gives (this is @prop:loss-convex-risk)
  $ risk(L, P)(g) <= 1/2 risk(L, P)(f_1) + 1/2 risk(L, P)(f_2). $
  Adding $lambda$ times @eq:reg-parallelogram with $theta = 1\/2$,
  $ risk(L, P, lambda)(g) <= 1/2 risk(L, P, lambda)(f_1) + 1/2 risk(L, P, lambda)(f_2) - lambda/4 norm(f_1 - f_2)_H^2 = m - lambda/4 norm(f_1 - f_2)_H^2 < m, $
  where we used $m < oo$ for the strict inequality. This contradicts the definition of $m$.
]

Three comments are in order. First, the minimizer is unique *as an element of $H$*, hence as a function
defined everywhere on $X$, not only $P_X$-almost everywhere; this is entirely due to the regularizer.
Second, the proof applies verbatim to $P = D$: for convex $L$, $risk(L, D, lambda)$ has at most one
minimizer (note $risk(L, D)(0) < oo$ always). Third, the finiteness assumption cannot be dropped:
if $risk(L, P)(f) = oo$ for all $f in H$, then every $f in H$ is a minimizer of $risk(L, P, lambda) equiv oo$.
This happens, for instance, for the least squares loss, a bounded kernel and a distribution with
$integral y^2 dif P(x, y) = oo$: for $f in H$ with $norm(f)_oo <= B$ we have
$(y - f(x))^2 >= 1/2 y^2 - B^2$ (from $y^2 <= 2 (y - t)^2 + 2 t^2$), hence $risk(L, P)(f) = oo$.

=== Existence

In finite dimensions, existence of minimizers is a compactness argument: a continuous function whose
sublevel sets are bounded attains its minimum, because closed bounded sets are compact. In an
infinite-dimensional Hilbert space closed balls are not compact, and continuity plus boundedness of
sublevel sets is *not* enough (see the remark after @lem:app-existence-minimizer for a continuous
function on $ell^2$ with bounded sublevel sets and no minimizer). The way out is to use the weak topology:
bounded sequences in a Hilbert space have weakly convergent subsequences (@thm:app-weak-compactness), and
convex lower semicontinuous functionals are weakly lower semicontinuous (Mazur's theorem,
@thm:app-mazur).
This is packaged in the following result from Appendix A (@lem:app-existence-minimizer):

#quote(block: true)[
  _Let $E$ be a reflexive Banach space (for instance a Hilbert space) and $phi: E -> RR union {oo}$ convex
  and lower semicontinuous. If some sublevel set ${w in E : phi(w) <= M}$ is nonempty and bounded, then
  $phi$ attains its infimum. If $phi$ is strictly convex, the minimizer is unique._
]

Convexity of the loss is therefore essential for our existence theory, and it is used twice: for weak
lower semicontinuity and for uniqueness.

#theorem(title: [Existence and uniqueness of $f_(P, lambda)$])[
  Let $(X, cal(A))$ be a measurable space, $Y subset.eq RR$ closed, $P$ a distribution on $X times Y$,
  $L: X times Y times RR -> [0, oo)$ a convex loss, $H$ an RKHS over $RR$ with measurable kernel $K$, and
  $lambda > 0$.
  + If there is $f_0 in H$ with $risk(L, P)(f_0) < oo$, then $risk(L, P, lambda)$ has exactly one minimizer
    $f_(P, lambda) in H$.
  + If $L$ is a $P$-integrable Nemitski loss and $K$ is bounded, then $risk(L, P): H -> [0, oo)$ is finite,
    convex and continuous. In particular (i) applies with $f_0 = 0$, so $f_(P, lambda)$ exists and is
    unique for every $lambda > 0$, and it satisfies the bounds of @prop:reg-norm-bound.
] <thm:reg-existence>

#proof[
  (i) We verify the hypotheses of @lem:app-existence-minimizer for $phi := risk(L, P, lambda)$ on $E := H$.

  _Convexity._ $risk(L, P)$ is convex on $H$ by the pointwise argument in the proof of @prop:reg-uniqueness
  (@prop:loss-convex-risk), and $f |-> lambda norm(f)_H^2$ is convex; so $phi$ is convex.

  _Lower semicontinuity._ Let $f_n -> f$ in $H$. Then $f_n (x) -> f(x)$ for every $x in X$
  (@prop:rkhs-norm-convergence). Each $L(x, y, dot)$ is a convex function $RR -> RR$ and hence continuous
  (@lem:app-convex-lipschitz), so $L(x, y, f_n (x)) -> L(x, y, f(x))$ for all $(x, y)$. By Fatou's lemma
  (@thm:app-convergence),
  $ risk(L, P)(f) = integral lim_(n -> oo) L(x, y, f_n (x)) dif P(x, y) <= liminf_(n -> oo) integral L(x, y, f_n (x)) dif P(x, y) = liminf_(n -> oo) risk(L, P)(f_n). $
  So $risk(L, P): H -> [0, oo]$ is lower semicontinuous; adding the continuous function $lambda norm(dot)_H^2$
  preserves this.

  _A nonempty bounded sublevel set._ Let $M := phi(f_0) = risk(L, P)(f_0) + lambda norm(f_0)_H^2 < oo$ and
  $S := {f in H : phi(f) <= M}$. Then $f_0 in S$, and every $f in S$ satisfies $lambda norm(f)_H^2 <= M$, so
  $S$ is bounded.

  Hence $phi$ attains its minimum by @lem:app-existence-minimizer, and the minimizer is unique by
  @prop:reg-uniqueness.

  (ii) By @prop:rkhs-bounded every $f in H$ is bounded with $norm(f)_oo <= abs(K)_oo norm(f)_H$. Let
  $b in cal(L)^1(P)$ and $h: [0, oo) -> [0, oo)$ non-decreasing with $L(x, y, t) <= b(x, y) + h(abs(t))$
  (@def:loss-nemitski). Then $risk(L, P)(f) <= norm(b)_(L^1(P)) + h(abs(K)_oo norm(f)_H) < oo$. For
  continuity, let $f_n -> f$ in $H$. Then $sup_(x in X) abs(f_n (x) - f(x)) <= abs(K)_oo norm(f_n - f)_H -> 0$,
  and $B := sup_n norm(f_n)_oo < oo$ because convergent sequences are bounded. As in (i),
  $L(x, y, f_n (x)) -> L(x, y, f(x))$ pointwise, and $L(x, y, f_n (x)) <= b(x, y) + h(B)$, an integrable
  majorant. By dominated convergence (@thm:app-convergence), $risk(L, P)(f_n) -> risk(L, P)(f)$. (In
  other words, $risk(L, P)$ on $H$ is the composition of the continuous risk on $L^oo (P_X)$ from
  @prop:loss-risk-continuity (ii) with the bounded embedding $H -> L^oo (P_X)$.) Convexity was shown in
  (i), and $risk(L, P)(0) <= norm(b)_(L^1(P)) < oo$, so (i) applies with $f_0 = 0$.
]

#remark(title: [On the hypotheses])[
  + Boundedness of $K$ is *not* needed for existence; it is needed only to make $risk(L, P)$ finite and
    continuous on all of $H$. Part (i) needs just one function of finite risk. In particular, for the
    empirical measure $D$ (@rem:reg-empirical) and any convex loss, $f_(D, lambda)$ exists and is unique
    for *every* kernel, bounded or not. We will reprove this by a finite-dimensional argument in
    @thm:reg-representer.
  + Convexity is essential. Without it, minimizers may fail to exist, as the next example shows. It is
    also essential in a less obvious way: lower semicontinuity with respect to the norm is not enough in
    infinite dimensions; we need *weak* lower semicontinuity, which convexity provides.
]

#example(title: [No minimizer for the 0–1 loss])[
  Let $X = {x_0}$ be a single point and $K(x_0, x_0) = 1$. Then $H$ consists of the constant functions
  $f = c K_(x_0)$, $c in RR$, with $norm(f)_H = abs(c)$; we identify $f$ with $c$. Let $P$ be the point
  mass at $(x_0, -1)$ and let $L$ be the classification loss $L(y, t) = ind_((-oo, 0]) (y sign(t))$ with the
  convention $sign(0) := 1$ (@ex:learn-classification). Then $L(-1, c) = 1$ if $c >= 0$ and $L(-1, c) = 0$ if
  $c < 0$, so
  $ risk(L, P, lambda)(c) = ind_([0, oo)) (c) + lambda c^2. $
  Its infimum is $0$ (let $c -> 0$ from below), but $risk(L, P, lambda)(c) > 0$ for every $c in RR$. No
  minimizer exists. The culprit is that $L(-1, dot)$ is neither convex nor lower semicontinuous at $0$.
] <ex:reg-nonexistence>


== The representer theorem <sec:reg-representer>

For interesting kernels, such as the Gaussian kernel, $H$ is infinite-dimensional, so minimizing
$risk(L, D, lambda)$ over $H$ seems to require an optimization over infinitely many parameters. The key
observation is that the data only "see" $N$ numbers: $risk(L, D)(f)$ depends on $f$ only through
$f(x_i) = ip(f, Phi(x_i))_H$, $i = 1, ..., N$. Any component of $f$ orthogonal to all $Phi(x_i)$ is
invisible to the data, but costs norm. An optimal $f$ should therefore have no such component, i.e. lie in
the finite-dimensional space
$ H_D := spn{Phi(x_1), ..., Phi(x_N)} = spn{K(dot, x_1), ..., K(dot, x_N)} subset.eq H. $

To compute with elements of $H_D$ we use the *Gram matrix* $bold(K) := (K(x_i, x_j))_(i,j=1)^N in RR^(N times N)$,
which is symmetric and positive semidefinite (@def:rkhs-pd, @prop:rkhs-kernel-properties). For
$bold(a) = (a_1, ..., a_N)^top in RR^N$ put
$ f_(bold(a)) := sum_(j=1)^N a_j K(dot, x_j) in H_D. $
By the reproducing property,
$ f_(bold(a)) (x_i) = sum_(j=1)^N a_j K(x_i, x_j) = (bold(K) bold(a))_i, quad norm(f_(bold(a)))_H^2 = sum_(i,j=1)^N a_i a_j ip(K_(x_j), K_(x_i))_H = bold(a)^top bold(K) bold(a). $ <eq:reg-gram>

#theorem(title: [Representer theorem])[
  Let $X$ be a nonempty set, $Y subset.eq RR$, $H$ an RKHS over $RR$ on $X$ with kernel $K$,
  $D = ((x_1, y_1), ..., (x_N, y_N)) in (X times Y)^N$, $lambda > 0$, and $L: X times Y times RR -> [0, oo)$.
  Let $Pi$ denote the orthogonal projection of $H$ onto $H_D$.
  + For every $f in H$, $risk(L, D, lambda)(Pi f) <= risk(L, D, lambda)(f)$, with equality only if $f = Pi f$.
    Consequently, every minimizer of $risk(L, D, lambda)$ lies in $H_D$.
  + If $L(x_i, y_i, dot)$ is continuous for every $i$, then $risk(L, D, lambda)$ has a minimizer. If
    $L(x_i, y_i, dot)$ is convex for every $i$ (e.g. if $L$ is a convex loss), the minimizer $f_(D, lambda)$
    is unique, and there is $bold(a) in RR^N$ with
    $ f_(D, lambda) = sum_(i=1)^N a_i K(dot, x_i), quad "i.e." quad f_(D, lambda) (x) = sum_(i=1)^N a_i K(x, x_i) quad (x in X). $
  + Let $L(x_i, y_i, dot)$ be convex for every $i$ and define
    $ G_D: RR^N -> [0, oo), quad G_D (bold(a)) := risk(L, D, lambda)(f_(bold(a))) = 1/N sum_(i=1)^N L(x_i, y_i, (bold(K) bold(a))_i) + lambda bold(a)^top bold(K) bold(a). $
    Then $f_(bold(a)) = f_(D, lambda)$ if and only if $bold(a)$ minimizes $G_D$. If $bold(a)^*$ is one such
    vector, the set of all of them is $bold(a)^* + Ker bold(K)$. In particular, the coefficients are unique
    if and only if $bold(K)$ is invertible; this is the case, for instance, if $K$ is strictly positive
    definite and $x_1, ..., x_N$ are pairwise distinct.
] <thm:reg-representer>

#proof[
  (i) $H_D$ is finite-dimensional and therefore closed, so by the projection theorem (@thm:app-projection)
  every $f in H$ decomposes as $f = Pi f + f^perp$ with $f^perp perp H_D$. By the reproducing property,
  $f^perp (x_i) = ip(f^perp, Phi(x_i))_H = 0$, hence $f(x_i) = (Pi f)(x_i)$ for all $i$ and
  $risk(L, D)(f) = risk(L, D)(Pi f)$. By Pythagoras, $norm(f)_H^2 = norm(Pi f)_H^2 + norm(f^perp)_H^2$.
  Since $risk(L, D)(f) < oo$, we obtain
  $ risk(L, D, lambda)(f) = risk(L, D, lambda)(Pi f) + lambda norm(f^perp)_H^2, $
  which proves the inequality, with equality if and only if $f^perp = 0$. If $f$ is a minimizer, then
  $risk(L, D, lambda)(f) <= risk(L, D, lambda)(Pi f)$, hence $f^perp = 0$ and $f in H_D$.

  (ii) _Existence._ On the finite-dimensional space $H_D$ the functional $risk(L, D, lambda)$ is continuous:
  the maps $f |-> f(x_i) = ip(f, Phi(x_i))_H$ are continuous and linear, $L(x_i, y_i, dot)$ is continuous
  by assumption, and the norm is continuous. The set
  $S := {f in H_D : risk(L, D, lambda)(f) <= risk(L, D)(0)}$ contains $0$, is closed, and is bounded, since
  $lambda norm(f)_H^2 <= risk(L, D)(0)$ on $S$. As $dim H_D < oo$, $S$ is compact (Heine–Borel), and the
  continuous function $risk(L, D, lambda)$ attains its minimum over $S$ at some $f^* in S$. Then $f^*$
  minimizes $risk(L, D, lambda)$ over all of $H$: for $f in H$ we have $Pi f in H_D$, and either
  $Pi f in S$, so that $risk(L, D, lambda)(f) >= risk(L, D, lambda)(Pi f) >= risk(L, D, lambda)(f^*)$ by (i),
  or $Pi f in.not S$, so that
  $risk(L, D, lambda)(f) >= risk(L, D, lambda)(Pi f) > risk(L, D)(0) >= risk(L, D, lambda)(f^*)$.

  _Uniqueness and representation._ A convex $L(x_i, y_i, dot): RR -> RR$ is continuous, so a minimizer
  exists. It is unique by @prop:reg-uniqueness applied to $P = D$ (its proof only uses convexity of
  $L(x_i, y_i, dot)$ and @eq:reg-parallelogram, see @rem:reg-empirical). By (i), $f_(D, lambda) in H_D$,
  i.e. $f_(D, lambda) = f_(bold(a))$ for some $bold(a) in RR^N$.

  (iii) The map $A: RR^N -> H_D$, $bold(a) |-> f_(bold(a))$, is linear and surjective, and
  $G_D = risk(L, D, lambda) compose A$ by @eq:reg-gram. Since $f_(D, lambda) in H_D = Ran A$ is the unique
  minimizer of $risk(L, D, lambda)$ over $H$, we have $min G_D = risk(L, D, lambda)(f_(D, lambda))$, and
  $G_D (bold(a)) = min G_D$ holds if and only if $A bold(a) = f_(D, lambda)$. The solution set of
  $A bold(a) = f_(D, lambda)$ is $bold(a)^* + Ker A$, and $Ker A = Ker bold(K)$: by @eq:reg-gram,
  $f_(bold(a)) = 0$ if and only if $bold(a)^top bold(K) bold(a) = 0$, and for a symmetric positive
  semidefinite matrix $bold(a)^top bold(K) bold(a) = norm(bold(K)^(1\/2) bold(a))^2 = 0$ holds if and only if
  $bold(K)^(1\/2) bold(a) = 0$, i.e. if and only if $bold(K) bold(a) = 0$. Finally, if $K$ is strictly positive definite and the
  $x_i$ are pairwise distinct, $bold(K)$ is positive definite (@def:rkhs-pd) and hence invertible.
]

#example(title: [Non-unique coefficients])[
  The representer theorem says that $f_(D, lambda)$ *can* be written as $sum_i a_i K(dot, x_i)$; the
  coefficients need not be unique. If two inputs coincide, $x_1 = x_2$, then $K(dot, x_1) = K(dot, x_2)$
  and only $a_1 + a_2$ is determined. If $K(x, x') = x x'$ is the linear kernel on $RR$, then
  $bold(K) = bold(x) bold(x)^top$ with $bold(x) = (x_1, ..., x_N)^top$ has rank at most one, and for $N >= 2$ there
  are infinitely many coefficient vectors, although $f_(D, lambda)$ itself is unique. The function is
  canonical, the coefficients are not.
] <ex:reg-coefficients>

*The kernel trick at work.* Part (iii) turns the infinite-dimensional problem into the minimization of a
convex function of $N$ real variables, and everything in it is expressed through the Gram matrix: neither
the space $H$ nor a feature map ever has to be written down. Predictions are evaluated as
$f_(D, lambda) (x) = sum_i a_i K(x, x_i)$. This is what makes kernel methods practical for infinite-dimensional
$H$ (e.g. Gaussian kernels), at a price: the Gram matrix has $N^2$ entries, and solving the resulting
problem typically costs of the order of $N^3$ operations, which becomes prohibitive for very large
data sets.

The proof of (i) did not need convexity, continuity or even measurability of $L$; it only used that the
penalty cannot increase under the projection $Pi$ and strictly decreases unless $f in H_D$. The same
argument works for every penalty of the form $g(norm(f)_H)$ with $g$ strictly increasing
(@ex:reg-exr-generalized-representer).

#context-note[
  The representer theorem goes back to Kimeldorf and Wahba @kimeldorf1971, who proved it for spline
  smoothing with the squared loss; the RKHS approach to splines is developed in @wahba1990. The version for
  arbitrary losses and penalties $g(norm(f)_H)$ with strictly increasing $g$ is due to Schölkopf, Herbrich
  and Smola @schoelkopf2001representer; see also @schoelkopf2002. The theorem is the mathematical
  justification of the "kernel trick": algorithms formulated in terms of inner products $ip(Phi(x_i), Phi(x_j))$
  only ever need the kernel values $K(x_i, x_j)$.
]

The representer theorem tells us nothing about the coefficients. In the following sections we derive
equations for them: linear equations for the least squares loss (@ex:reg-krr), nonlinear ones for
general differentiable losses (@cor:reg-empirical-equation), and inclusions for non-differentiable losses
(@cor:reg-empirical-representer).

=== When is the solution nontrivial?

The representer theorem does not exclude the useless answer $f_(D, lambda) = 0$. The following
proposition characterizes exactly when this happens, for general $P$ (and hence also for $P = D$).

#proposition(title: [Nontrivial minimizers])[
  In the setting of @sec:reg-existence, let $L$ be convex, $risk(L, P)(0) < oo$ and $lambda > 0$, so that
  $f_(P, lambda)$ exists and is unique by @thm:reg-existence (i). Then
  $ f_(P, lambda) != 0 quad <==> quad inf_(f in H) risk(L, P)(f) < risk(L, P)(0). $
  In particular, either $f_(P, lambda) = 0$ for all $lambda > 0$, or $f_(P, lambda) != 0$ for all $lambda > 0$.
] <prop:reg-nonzero>

#proof[
  "$arrow.l.double$": Choose $tilde(f) in H$ with $risk(L, P)(tilde(f)) < risk(L, P)(0)$ and put
  $delta := risk(L, P)(0) - risk(L, P)(tilde(f)) > 0$; in particular $tilde(f) != 0$. For $alpha in [0, 1]$,
  convexity of the risk (@prop:loss-convex-risk) gives
  $ risk(L, P)(alpha tilde(f)) = risk(L, P)(alpha tilde(f) + (1 - alpha) 0) <= alpha risk(L, P)(tilde(f)) + (1 - alpha) risk(L, P)(0) = risk(L, P)(0) - alpha delta, $
  hence
  $ risk(L, P, lambda)(alpha tilde(f)) <= q(alpha) := risk(L, P)(0) - alpha delta + lambda alpha^2 norm(tilde(f))_H^2. $
  The quadratic $q$ satisfies $q(0) = risk(L, P)(0)$ and $q'(0) = -delta < 0$, so it drops below $q(0)$ for
  small $alpha > 0$. Explicitly, for $alpha := min{1, delta \/ (2 lambda norm(tilde(f))_H^2)}$ we have
  $lambda alpha norm(tilde(f))_H^2 <= delta \/ 2$ and therefore $q(alpha) <= risk(L, P)(0) - alpha delta \/ 2$. Thus
  $ risk(L, P, lambda)(f_(P, lambda)) <= risk(L, P, lambda)(alpha tilde(f)) <= risk(L, P)(0) - (alpha delta)/2 < risk(L, P)(0) = risk(L, P, lambda)(0), $
  and $f_(P, lambda) != 0$.

  "$==>$": If $inf_(f in H) risk(L, P)(f) = risk(L, P)(0)$, then every $f in H without {0}$ satisfies
  $ risk(L, P, lambda)(f) >= risk(L, P)(0) + lambda norm(f)_H^2 > risk(L, P, lambda)(0), $
  so $0$ is the minimizer.
]

The condition $inf_H risk(L, P) < risk(L, P)(0)$ says that $H$ contains *some* function that beats the
trivial predictor. It is not implied by the other assumptions: even if $0$ is far from optimal among all
measurable functions (or among all bounded ones), $H$ may be too poor to do better.

#example(title: [A kernel that cannot see the signal])[
  Let $X = [-1, 1]$ with $P_X$ the uniform distribution, $y = x^2$ deterministically (i.e.
  $P(dot | x) = delta_(x^2)$), $L$ the least squares loss, and $K(x, x') = x x'$ the linear kernel, whose
  RKHS consists of the functions $x |-> w x$ with norm $abs(w)$. Since $integral x^3 dif P_X = 0$,
  $ risk(L, P)(w x) = integral_(-1)^1 (x^2 - w x)^2 dif x / 2 = 1/5 + w^2/3 >= 1/5 = risk(L, P)(0). $
  By @prop:reg-nonzero, $f_(P, lambda) = 0$ for every $lambda > 0$, although the Bayes function $x |-> x^2$
  has risk $0$. In contrast, for a universal kernel on a compact metric space and a continuous
  $P$-integrable Nemitski loss, $inf_H risk(L, P)$ equals the Bayes risk (@thm:univ-bayes), and then
  $f_(P, lambda) != 0$ as soon as $risk(L, P)(0) > bayes(L, P)$, i.e. as soon as $0$ is not itself a Bayes
  decision function.
] <ex:reg-trivial>


== Differentiable losses: an integral equation <sec:reg-differentiable>

The representer theorem describes the *form* of $f_(D, lambda)$ but gives no equations for the
coefficients, and it says nothing about $f_(P, lambda)$. For differentiable losses we can use calculus: at
a minimizer the derivative of $risk(L, P, lambda)$ vanishes. The derivative is a continuous linear
functional on $H$, which by the Riesz representation theorem is an element of $H$: a gradient. Formally,
by the reproducing property,
$ integral L'(x, y, f(x)) g(x) dif P(x, y) & = integral L'(x, y, f(x)) ip(g, Phi(x))_H dif P(x, y) \
  & eq.quest ip(g, integral L'(x, y, f(x)) Phi(x) dif P(x, y))_H, $
so the gradient should be an $H$-valued integral of the feature map. We first make sense of such
integrals.

=== $H$-valued integrals of the feature map

#definition(title: [Integrals of the feature map])[
  Let $Q$ be a distribution on $X times Y$ and let $h: X times Y -> RR$ be measurable. We define an element
  $ EE_Q [h Phi] = integral_(X times Y) h(x, y) Phi(x) dif Q(x, y) in H $
  in the following two situations.
  + If $K$ is bounded and measurable and $h in cal(L)^1 (Q)$: $EE_Q [h Phi]$ is the unique element of $H$
    with
    $ ip(g, EE_Q [h Phi])_H = integral_(X times Y) h(x, y) g(x) dif Q(x, y) quad "for all" g in H. $ <eq:reg-kernel-mean>
  + If $Q = D$ is the empirical measure of a data set (and $K$ is arbitrary):
    $ EE_D [h Phi] := 1/N sum_(i=1)^N h(x_i, y_i) Phi(x_i) = 1/N sum_(i=1)^N h(x_i, y_i) K(dot, x_i). $
] <def:reg-kernel-mean>

#lemma[
  In the situations of @def:reg-kernel-mean, $EE_Q [h Phi]$ is well defined, it satisfies
  @eq:reg-kernel-mean, and:
  + $h |-> EE_Q [h Phi]$ is linear, and in situation (i), $norm(EE_Q [h Phi])_H <= abs(K)_oo norm(h)_(L^1(Q))$;
  + $EE_Q [h Phi]$ is the function $x' |-> integral_(X times Y) h(x, y) K(x', x) dif Q(x, y)$;
  + if $K$ is bounded and measurable and $H$ is separable (e.g. by @prop:rkhs-separable), then
    $(x, y) |-> h(x, y) Phi(x)$ is Bochner integrable (@def:app-bochner) for $h in cal(L)^1 (Q)$, and its
    Bochner integral equals $EE_Q [h Phi]$.
] <lem:reg-kernel-mean>

#proof[
  In situation (i), for $g in H$ the function $(x, y) |-> h(x, y) g(x)$ is measurable and
  $abs(h(x, y) g(x)) <= abs(h(x, y)) abs(K)_oo norm(g)_H$. Hence $ell(g) := integral h(x, y) g(x) dif Q(x, y)$
  defines a linear functional on $H$ with $abs(ell(g)) <= abs(K)_oo norm(h)_(L^1(Q)) norm(g)_H$. By the
  Riesz representation theorem (@thm:app-riesz) there is a unique $w in H$ with $ell(g) = ip(g, w)_H$ for
  all $g$, and $norm(w)_H = norm(ell) <= abs(K)_oo norm(h)_(L^1(Q))$. In situation (ii), the defining
  formula is a finite sum, and $ip(g, EE_D [h Phi])_H = 1/N sum_i h(x_i, y_i) g(x_i) = integral h g dif D$,
  which is @eq:reg-kernel-mean. Linearity in $h$ is clear from @eq:reg-kernel-mean and uniqueness.

  For (ii), apply @eq:reg-kernel-mean to $g = Phi(x') = K(dot, x')$: since
  $Phi(x')(x) = K(x, x') = K(x', x)$, we get
  $EE_Q [h Phi](x') = ip(EE_Q [h Phi], Phi(x'))_H = integral h(x, y) K(x', x) dif Q(x, y)$.

  For (iii), the map $(x, y) |-> Phi(x)$ is weakly measurable: for each $g in H$,
  $(x, y) |-> ip(Phi(x), g)_H = g(x)$ is measurable. As $H$ is separable, Pettis' theorem
  (@thm:app-bochner-properties (ii)) shows that it is strongly measurable, hence so is
  $(x, y) |-> h(x, y) Phi(x)$ (@thm:app-bochner-properties (iii)), and
  $integral norm(h(x, y) Phi(x))_H dif Q = integral abs(h(x, y)) sqrt(K(x, x)) dif Q(x, y) <= abs(K)_oo norm(h)_(L^1(Q)) < oo$.
  So the Bochner integral $w'$ exists (@thm:app-bochner-properties (i)), and since bounded linear
  functionals commute with Bochner integrals (@thm:app-bochner-properties (iv)),
  $ip(g, w')_H = integral h(x, y) ip(g, Phi(x))_H dif Q = integral h g dif Q$ for all $g in H$. By uniqueness
  in @eq:reg-kernel-mean, $w' = EE_Q [h Phi]$. (For $h$ depending on $x$ only, this is
  @prop:app-bochner-feature-map.)
]

Defining $EE_Q [h Phi]$ "weakly" through @eq:reg-kernel-mean has the advantage that no separability of $H$
is needed; part (iii) shows that nothing changes when the Bochner integral is available. For $h equiv 1$,
$EE_Q [Phi] = integral Phi(x) dif Q_X (x)$ is known as the *kernel mean embedding* of the marginal $Q_X$.

=== The integral equation

#theorem(title: [Minimizers for differentiable losses])[
  Let $(X, cal(A))$ be a measurable space, $Y subset.eq RR$ closed, $P$ a distribution on $X times Y$, and
  $L: X times Y times RR -> [0, oo)$ a convex loss such that $L(x, y, dot)$ is differentiable for all
  $(x, y)$ and both $L$ and $abs(L')$ are $P$-integrable Nemitski losses, where
  $L'(x, y, t) = partial_t L(x, y, t)$. Let $H$ be an RKHS over $RR$ with bounded measurable kernel $K$ and
  let $lambda > 0$. Then $f in H$ equals $f_(P, lambda)$ if and only if
  $ f = -1/(2 lambda) integral_(X times Y) L'(x, y, f(x)) Phi(x) dif P(x, y). $
  In particular, $f_(P, lambda)$ satisfies the integral equation
  $ f_(P, lambda) (x') = -1/(2 lambda) integral_(X times Y) L'(x, y, f_(P, lambda) (x)) K(x', x) dif P(x, y), quad x' in X. $ <eq:reg-integral-equation>
] <thm:reg-integral-equation>

#proof[
  By @thm:reg-existence (ii), $f_(P, lambda)$ exists and is unique. For $f in H$ put
  $h_f (x, y) := L'(x, y, f(x))$. This function is measurable ($L'$ is measurable by @prop:loss-frechet (i))
  and integrable: if $abs(L'(x, y, t)) <= b'(x, y) + h'(abs(t))$ with $b' in cal(L)^1(P)$ and $h'$ non-decreasing,
  then $abs(h_f) <= b' + h'(norm(f)_oo)$. So $EE_P [h_f Phi]$ is defined (@def:reg-kernel-mean).

  _Step 1: the derivative of the risk on $H$._ Let $iota: H -> L^oo (P_X)$ map $f$ to its equivalence
  class; $iota$ is linear with $norm(iota f)_(L^oo (P_X)) <= abs(K)_oo norm(f)_H$ (@prop:rkhs-bounded), and
  $risk(L, P)(f) = R^oo (iota f)$, where $R^oo: L^oo (P_X) -> [0, oo)$ denotes the risk on $L^oo (P_X)$.
  By the chain rule @prop:loss-frechet (iv), $risk(L, P) = R^oo compose iota$ is Fréchet differentiable on
  $H$ (@def:loss-frechet) with derivative
  $ g |-> integral g(x) L'(x, y, f(x)) dif P(x, y) = ip(g, EE_P [h_f Phi])_H, $
  where the last identity is @eq:reg-kernel-mean.

  _Step 2: the derivative of the penalty._ For $Omega(f) := norm(f)_H^2$,
  $ Omega(f + g) - Omega(f) - 2 ip(g, f)_H = norm(g)_H^2 = o(norm(g)_H) quad (g -> 0), $
  so $Omega$ is Fréchet differentiable with $Omega'(f) g = 2 ip(g, f)_H$. Together,
  $ risk(L, P, lambda)'(f) g = ip(g, EE_P [h_f Phi] + 2 lambda f)_H quad (f, g in H). $

  _Step 3: necessity._ Let $f = f_(P, lambda)$ and $g in H$. The real function
  $s |-> risk(L, P, lambda)(f + s g)$ has a minimum at $s = 0$ and is differentiable there with derivative
  $risk(L, P, lambda)'(f) g$, which must therefore vanish. Choosing $g := EE_P [h_f Phi] + 2 lambda f$ gives
  $norm(g)_H^2 = 0$, i.e. $f = -1/(2 lambda) EE_P [h_f Phi]$.

  _Step 4: sufficiency._ Suppose $f = -1/(2 lambda) EE_P [h_f Phi]$, i.e. $risk(L, P, lambda)'(f) = 0$. For
  $g in H$ and $s in (0, 1]$, convexity of $risk(L, P, lambda)$ gives
  $ (risk(L, P, lambda)(f + s (g - f)) - risk(L, P, lambda)(f))/s <= risk(L, P, lambda)(g) - risk(L, P, lambda)(f). $
  Letting $s -> 0^+$, the left-hand side tends to $risk(L, P, lambda)'(f)(g - f) = 0$. Hence
  $risk(L, P, lambda)(g) >= risk(L, P, lambda)(f)$ for all $g$, and $f = f_(P, lambda)$ by uniqueness.
  Finally, the integral equation @eq:reg-integral-equation[] is the pointwise form given by @lem:reg-kernel-mean (ii).
]

The integral equation @eq:reg-integral-equation[] is a nonlinear fixed-point equation: $f_(P, lambda)$ appears on both sides. It
says that $f_(P, lambda)$ is a superposition of kernel sections $K(dot, x)$, weighted by
$-L'(x, y, f_(P, lambda) (x)) \/ (2 lambda)$, the (negative, rescaled) slope of the loss at the current
prediction. Points at which the prediction is already good (small slope) contribute little; this is the
"continuous" counterpart of the representer theorem.

For the empirical measure, the same argument works without any assumption on the kernel, because only
finitely many points are involved.

#corollary(title: [Coefficient equations])[
  Let $X$ be a nonempty set, $H$ an RKHS over $RR$ on $X$ with kernel $K$, $D in (X times Y)^N$, $lambda > 0$,
  and let $L: X times Y times RR -> [0, oo)$ be such that $L(x_i, y_i, dot)$ is convex and differentiable for
  $i = 1, ..., N$. Then $f in H$ equals $f_(D, lambda)$ if and only if
  $ f = -1/(2 lambda N) sum_(i=1)^N L'(x_i, y_i, f(x_i)) K(dot, x_i). $
  Consequently, $f_(D, lambda) = f_(bold(a))$ with $a_i := -L'(x_i, y_i, f_(D, lambda) (x_i)) \/ (2 lambda N)$,
  and this vector $bold(a)$ is the unique solution of the $N$ equations
  $ a_i = -1/(2 lambda N) L'(x_i, y_i, (bold(K) bold(a))_i), quad i = 1, ..., N. $ <eq:reg-coefficient-equations>
] <cor:reg-empirical-equation>

#proof[
  The regularized empirical risk has a unique minimizer by @thm:reg-representer. For $f, g in H$, the function
  $ s |-> risk(L, D, lambda)(f + s g) = 1/N sum_(i=1)^N L(x_i, y_i, f(x_i) + s g(x_i)) + lambda norm(f + s g)_H^2 $
  is differentiable, and with $h_f (x_i, y_i) := L'(x_i, y_i, f(x_i))$ its derivative at $s = 0$ is
  $ 1/N sum_(i=1)^N L'(x_i, y_i, f(x_i)) g(x_i) + 2 lambda ip(g, f)_H = ip(g, EE_D [h_f Phi] + 2 lambda f)_H. $ Steps 3 and 4 of the proof of @thm:reg-integral-equation only
  used these directional derivatives and convexity, so they apply verbatim and prove the first claim.

  If $f_(D, lambda) = f_(bold(a))$ with the stated $a_i$, then $(bold(K) bold(a))_i = f_(D, lambda) (x_i)$ by
  @eq:reg-gram, so $bold(a)$ solves @eq:reg-coefficient-equations[]. Conversely, if $bold(a)$ solves
  @eq:reg-coefficient-equations[], then $f := f_(bold(a))$ satisfies $f(x_i) = (bold(K) bold(a))_i$, hence
  $f = sum_i a_i K(dot, x_i) = -1/(2 lambda N) sum_i L'(x_i, y_i, f(x_i)) K(dot, x_i)$, so $f = f_(D, lambda)$ by
  the first part. Then $a_i = -L'(x_i, y_i, f_(D, lambda) (x_i)) \/ (2 lambda N)$ is determined by
  $f_(D, lambda)$, which proves uniqueness of the solution.
]

Among the many coefficient vectors that may represent $f_(D, lambda)$ (@ex:reg-coefficients), the
equations @eq:reg-coefficient-equations[] single out a canonical one, determined by the slopes of the loss
at the data points. We now work this out for the most important differentiable loss.

#example(title: [Kernel ridge regression])[
  Let $L(y, t) = (y - t)^2$, so $L'(y, t) = -2 (y - t)$.

  *The linear system.* The coefficient equations @eq:reg-coefficient-equations[] read
  $a_i = 1/(lambda N) (y_i - (bold(K) bold(a))_i)$, i.e. $lambda N bold(a) = bold(y) - bold(K) bold(a)$ with
  $bold(y) = (y_1, ..., y_N)^top$:
  $ (bold(K) + lambda N I) bold(a) = bold(y). $ <eq:reg-krr-system>
  Since $bold(K)$ is symmetric positive semidefinite, its eigenvalues $mu_1, ..., mu_N$ are $>= 0$, so the
  eigenvalues of $bold(K) + lambda N I$ are $>= lambda N > 0$ and the matrix is invertible. By
  @cor:reg-empirical-equation, $bold(a) = (bold(K) + lambda N I)^(-1) bold(y)$ gives the minimizer:
  $ f_(D, lambda) (x) = sum_(i=1)^N a_i K(x, x_i) = bold(k)(x)^top (bold(K) + lambda N I)^(-1) bold(y), quad bold(k)(x) := (K(x, x_1), ..., K(x, x_N))^top. $
  (One can also see this directly: $G_D (bold(a)) = 1/N norm(bold(y) - bold(K) bold(a))^2 + lambda bold(a)^top bold(K) bold(a)$ has gradient
  $2/N bold(K) ((bold(K) + lambda N I) bold(a) - bold(y))$, which vanishes at $bold(a) = (bold(K) + lambda N I)^(-1) bold(y)$.)

  *Spectral interpretation.* Let $bold(K) = sum_j mu_j bold(u)_j bold(u)_j^top$ with an orthonormal basis of
  eigenvectors $bold(u)_j$. The vector of fitted values is
  $ (f_(D, lambda) (x_i))_(i=1)^N = bold(K) bold(a) = bold(K) (bold(K) + lambda N I)^(-1) bold(y) = sum_(j=1)^N mu_j/(mu_j + lambda N) (bold(u)_j^top bold(y)) bold(u)_j. $
  The data are expanded in the eigenbasis of the Gram matrix, and each component is shrunk by the factor
  $mu_j \/ (mu_j + lambda N) in [0, 1)$: components with large eigenvalue ("smooth directions") are kept,
  components with small eigenvalue are damped. As $lambda -> 0$ with $bold(K)$ invertible,
  $bold(a) -> bold(K)^(-1) bold(y)$ and the fitted values tend to $bold(y)$: the solution interpolates the
  data (@ex:reg-exr-min-norm). As $lambda -> oo$, $lambda N bold(a) -> bold(y)$ and $f_(D, lambda) -> 0$.

  *A worked example.* Take the kernel $K(x, x') = min{x, x'}$ on $X = [0, 1]$, whose RKHS consists of the
  absolutely continuous $f$ with $f(0) = 0$ and $f' in L^2 [0, 1]$, with $norm(f)_H = norm(f')_(L^2)$
  (@sec:rkhs). With the data $(x_1, y_1) = (1\/2, 1)$ and $(x_2, y_2) = (1, 1)$ we minimize
  $ 1/2 ((1 - f(1\/2))^2 + (1 - f(1))^2) + lambda integral_0^1 f'(x)^2 dif x. $
  Here $bold(K) = mat(1\/2, 1\/2; 1\/2, 1)$ and $N = 2$; solving the linear system @eq:reg-krr-system[] gives
  $ bold(a) = 1/(16 lambda^2 + 12 lambda + 1) vec(2 + 8 lambda, 8 lambda), quad f_(D, lambda) (x) = ((2 + 8 lambda) min{x, 1\/2} + 8 lambda x)/(16 lambda^2 + 12 lambda + 1). $
  For instance, $lambda = 1\/4$ gives $bold(a) = (4\/5, 2\/5)^top$; indeed
  $(bold(K) + 1/2 I) bold(a) = (4/5 + 1/5, 2/5 + 3/5)^top = (1, 1)^top$. The solutions are piecewise linear with
  kinks only at the data points: *linear splines*, the simplest instance of the connection between
  regularization in RKHSs and spline smoothing. As $lambda -> 0$ they converge to the interpolant
  $2 min{x, 1\/2}$, the interpolating function of smallest energy $integral_0^1 f'^2$
  (@fig:reg-krr).

  *The population version.* If $integral y^2 dif P(x, y) < oo$, the least squares loss is a $P$-integrable
  Nemitski loss (since $(y - t)^2 <= 2 y^2 + 2 t^2$), and so is $abs(L'(y, t)) = 2 abs(y - t) <= 2 abs(y) + 2 abs(t)$.
  For a bounded measurable kernel, @thm:reg-integral-equation gives
  $f_(P, lambda) = 1/lambda EE_P [(y - f_(P, lambda) (x)) Phi(x)]$, i.e.
  $ (C_P + lambda) f_(P, lambda) = EE_P [y Phi(x)], quad "where" quad C_P g := EE_P [g(x) Phi(x)] = integral_X g(x) Phi(x) dif P_X (x). $
  Here $EE_P [y Phi(x)]$ is $EE_P [h Phi]$ for $h(x, y) = y$, which is $P$-integrable. By
  @eq:reg-kernel-mean, $ip(C_P g, g')_H = integral g g' dif P_X$, so the *covariance operator* $C_P$ is
  bounded, self-adjoint and positive. Hence $ip((C_P + lambda) g, g)_H >= lambda norm(g)_H^2$, so the operator
  $C_P + lambda$ is injective with closed range; its range is also dense, because the orthogonal
  complement of the range is $Ker (C_P + lambda)^* = Ker (C_P + lambda) = {0}$. So $C_P + lambda$ is invertible and
  $ f_(P, lambda) = (C_P + lambda)^(-1) EE_P [y Phi(x)], $
  the exact analogue of $bold(a) = (bold(K) + lambda N I)^(-1) bold(y)$.
] <ex:reg-krr>

#figure(
  cetz.canvas({
    plot.plot(
      size: (8, 4.5),
      x-tick-step: 0.25,
      y-tick-step: 0.25,
      x-min: 0, x-max: 1.02,
      y-min: 0, y-max: 1.15,
      x-label: $x$,
      y-label: none,
      legend: "inner-south-east",
      {
        plot.add(((0, 0), (0.5, 1), (1, 1)), style: (stroke: black + 1pt), label: [$lambda -> 0$])
        plot.add(((0, 0), (0.5, 0.6), (1, 0.8)), style: (stroke: (paint: rgb("#2e5a8a"), thickness: 1pt, dash: "dashed")), label: [$lambda = 1\/4$])
        plot.add(((0, 0), (0.5, 9 / 29), (1, 13 / 29)), style: (stroke: (paint: rgb("#a0522d"), thickness: 1pt, dash: "dotted")), label: [$lambda = 1$])
        plot.add(((0.5, 1), (1, 1)), mark: "o", mark-size: 0.15, style: (stroke: none), mark-style: (fill: black, stroke: black))
      },
    )
  }),
  caption: [Kernel ridge regression with the kernel $min{x, x'}$ on $[0, 1]$ and two data points (dots). The
    solutions are linear splines with kinks at the data points; larger $lambda$ shrinks them towards $0$.],
) <fig:reg-krr>

#context-note[
  Kernel ridge regression is one of the most widely used kernel methods, and it appears under several
  names. For the linear kernel it is *ridge regression* of Hoerl and Kennard @hoerl1970
  (@ex:reg-exr-ridge; see also @hastie2009). If $H$ is a
  Sobolev-type space, the solutions are *smoothing splines* (the example above shows linear splines;
  penalizing $integral f''^2$ instead gives the classical cubic smoothing splines), see @wahba1990 and
  @kimeldorf1971. And the formula $bold(k)(x)^top (bold(K) + sigma^2 I)^(-1) bold(y)$ is the *posterior
  mean of Gaussian process regression* with covariance function $K$ and Gaussian observation noise of
  variance $sigma^2$ @rasmussen2006; so the two coincide when $sigma^2 = lambda N$ (see also
  @berlinet2004 for the correspondence between RKHSs and Gaussian processes). The regularization
  parameter thus has the Bayesian interpretation of a noise-to-signal ratio.

  In the population version, the spectral picture of @sec:mercer becomes visible. If $H$ is separable and
  $S_K$, $T_K = S_K^* S_K$ are the operators of @thm:mercer-integral-operator for $mu = P_X$, then
  $C_P = S_K S_K^*$ and $EE_P [y Phi(x)] = S_K f_P$ with the regression function
  $f_P (x) = integral y dif P(y | x)$ (@ex:learn-least-squares). From
  $S_K (T_K + lambda) = (C_P + lambda) S_K$ we get $f_(P, lambda) = S_K (T_K + lambda)^(-1) f_P$, and in
  $L^2 (P_X)$ with the eigenpairs $(lambda_j, e_j)$ of $T_K$,
  $ f_(P, lambda) = sum_j lambda_j/(lambda_j + lambda) ip(f_P, e_j)_(L^2 (P_X)) e_j. $
  Regularization acts as a *spectral filter*: the component of the regression function along $e_j$ is
  kept if $lambda_j >> lambda$ and suppressed if $lambda_j << lambda$. This is Tikhonov regularization in
  the sense of the context note in @sec:reg-problem.
]

The linear system @eq:reg-krr-system[] can also be derived in "Fourier coordinates", which illuminates
how the penalty acts on the expansion coefficients of $f$. This computation also yields a second proof of the
representer theorem for the least squares loss.

#example(title: [Kernel ridge regression for series kernels])[
  Let $(phi_k)_(k in NN)$ be functions $X -> RR$ and $w_k > 0$ with $sum_k w_k phi_k (x)^2 < oo$ for every
  $x in X$, and let
  $ K(x, x') := sum_(k=1)^oo w_k phi_k (x) phi_k (x'). $
  With $Psi: X -> ell^2$, $Psi(x) := (sqrt(w_k) phi_k (x))_(k in NN)$, we have
  $K(x, x') = ip(Psi(x'), Psi(x))_(ell^2)$, so $Psi$ is a feature map of $K$ (@def:rkhs-feature-map), and by
  @prop:rkhs-feature-representation
  $ H = {f_v := ip(v, Psi(dot))_(ell^2) : v in ell^2}, quad norm(f)_H = min {norm(v)_(ell^2) : f_v = f}. $
  In the coordinates $c_k := sqrt(w_k) v_k$ we have $f_v = sum_k c_k phi_k$ (pointwise) and
  $norm(v)_(ell^2)^2 = sum_k c_k^2 \/ w_k$; this is also @prop:rkhs-series applied to the functions
  $sqrt(w_k) phi_k$. If $(phi_k)$ is an orthonormal system in some $L^2 (mu)$ and $sup_k w_k < oo$, then
  $sum_k c_k^2 <= (sup_k w_k) norm(v)_(ell^2)^2 < oo$, so the series $sum_k c_k phi_k$ also converges in
  $L^2 (mu)$, necessarily to (the class of) $f$, and the $c_k$ are the Fourier coefficients of $f$. The
  penalty $sum_k c_k^2 \/ w_k$ then damps the coefficients with small weights $w_k$; cf.
  @prop:mercer-rkhs-spectral.

  For the least squares loss, consider
  $ Gamma: ell^2 -> [0, oo), quad Gamma(v) := 1/N sum_(i=1)^N (y_i - ip(v, Psi(x_i))_(ell^2))^2 + lambda norm(v)_(ell^2)^2. $
  Since $norm(f_v)_H <= norm(v)_(ell^2)$ with equality for a suitable $v$ representing any given $f$, we have
  $Gamma(v) >= risk(L, D, lambda)(f_v)$ with equality for suitable $v$, so $inf Gamma = min risk(L, D, lambda)$,
  and $v^*$ minimizes $Gamma$ if and only if $f_(v^*) = f_(D, lambda)$ and $norm(v^*)_(ell^2) = norm(f_(D, lambda))_H$.
  Such a $v^*$ exists: take the $v$ with $f_v = f_(D, lambda)$ and $norm(v)_(ell^2) = norm(f_(D, lambda))_H$.
  The function $Gamma$ is Fréchet differentiable on $ell^2$ with gradient
  $ nabla Gamma(v) = -2/N sum_(i=1)^N (y_i - ip(v, Psi(x_i))_(ell^2)) Psi(x_i) + 2 lambda v, $
  and $nabla Gamma(v^*) = 0$ means, coordinate by coordinate,
  $ v_k^* = 1/(lambda N) sum_(i=1)^N (y_i - f(x_i)) sqrt(w_k) phi_k (x_i), quad f := f_(D, lambda). $
  With $a_i := (y_i - f(x_i)) \/ (lambda N)$ this says $c_k = w_k sum_i a_i phi_k (x_i)$, and therefore
  $ f(x) = sum_(k=1)^oo c_k phi_k (x) = sum_(i=1)^N a_i sum_(k=1)^oo w_k phi_k (x_i) phi_k (x) = sum_(i=1)^N a_i K(x, x_i), $
  where exchanging the finite sum and the series is allowed because each series converges absolutely (by
  the Cauchy–Schwarz inequality and $sum_k w_k phi_k (x)^2 < oo$). This is the representer theorem again.
  Evaluating at $x_j$ gives $f(x_j) = (bold(K) bold(a))_j$, and the definition of $a_i$ becomes
  $lambda N bold(a) = bold(y) - bold(K) bold(a)$, which is the linear system @eq:reg-krr-system[]. As a consistency check,
  $ norm(f)_H^2 = sum_k c_k^2/w_k = sum_k w_k (sum_i a_i phi_k (x_i))^2 = sum_(i,j=1)^N a_i a_j K(x_i, x_j) = bold(a)^top bold(K) bold(a), $
  in accordance with @eq:reg-gram. Note that the coefficient $c_k$ of the solution carries the factor
  $w_k$: directions with small weights are strongly damped.
] <ex:reg-series>


== Subdifferentials <sec:reg-subdifferentials>

Many important losses are convex but not differentiable: the hinge loss has a kink at $y t = 1$, the
absolute loss $abs(y - t)$ at $t = y$, the $epsilon$-insensitive loss $max{0, abs(y - t) - epsilon}$ at
$abs(y - t) = epsilon$, the pinball loss of quantile regression at $t = y$. The integral equation of
@thm:reg-integral-equation does not make sense for them. Convexity offers a substitute for the derivative.
A differentiable convex function lies above each of its tangent lines. At a kink there is no tangent,
but there are *many* lines that stay below the graph and touch it at the point: supporting lines. Their
slopes form an interval, and this interval replaces the derivative. Fermat's rule survives: a convex
function has a minimum at a point if and only if one of these supporting lines is horizontal.

Throughout this section, $E$ and $F$ are real Banach spaces with topological duals $E'$ and $F'$ (the
spaces of *continuous* linear functionals, as opposed to the algebraic duals of all linear functionals). For
$w' in E'$ and $v in E$ we write $w'(v)$ for the value of the functional (not to be confused with an
inner product). Functions may take the value $+oo$; for $f: E -> RR union {oo}$ we write
$dom f := {w in E : f(w) < oo}$, and $f$ is convex if $f((1 - theta) v + theta w) <= (1 - theta) f(v) + theta f(w)$
for all $v, w in E$ and $theta in [0, 1]$ (with the conventions $a + oo = oo$ for $a in RR union {oo}$ and $theta dot oo = oo$ for $theta > 0$, $0 dot oo = 0$).

#definition(title: [Subdifferential])[
  Let $f: E -> RR union {oo}$ be convex and $w in dom f$. The *subdifferential* of $f$ at $w$ is
  $ partial f(w) := {w' in E' : w'(v - w) <= f(v) - f(w) "for all" v in E}. $
  Its elements are called *subgradients* of $f$ at $w$. For $w in.not dom f$ we put $partial f(w) := emptyset$.
  For a convex loss $L$ we write $partial L(x, y, t) := partial (L(x, y, dot))(t) subset.eq RR$, identifying
  $RR' = RR$ via $c |-> (s |-> c s)$.
] <def:reg-subdifferential>

Geometrically, $w' in partial f(w)$ means that the affine function $v |-> f(w) + w'(v - w)$ lies below $f$
and touches it at $w$ (@fig:reg-subdifferential). If $E = H$ is a Hilbert space, we identify $H'$ with $H$
via the Riesz isomorphism (@thm:app-riesz): then $g in H$ is a subgradient of $f$ at $w$ if and only if
$ip(v - w, g)_H <= f(v) - f(w)$ for all $v in H$.

#figure(
  grid(
    columns: 2,
    gutter: 1.5em,
    cetz.canvas({
      plot.plot(
        size: (5.2, 4),
        axis-style: "school-book",
        x-tick-step: none,
        y-tick-step: none,
        x-min: -1.5, x-max: 3,
        y-min: -0.3, y-max: 3,
        x-label: $t$,
        y-label: none,
        {
          for c in (0.25, 0.4375, 0.625, 0.8125, 1.0) {
            plot.add(domain: (-1.5, 3), t => 1.2 + c * (t - 1), style: (stroke: (paint: gray, thickness: 0.6pt, dash: "dashed")))
          }
          plot.add(domain: (-1.5, 1), t => 1.2 + 0.25 * (t - 1) + 0.12 * calc.pow(t - 1, 2), style: (stroke: black + 1.2pt))
          plot.add(domain: (1, 2.3), t => 1.2 + (t - 1) + 0.35 * calc.pow(t - 1, 2), style: (stroke: black + 1.2pt))
          plot.add(((1, 1.2),), mark: "o", mark-size: 0.13, style: (stroke: none), mark-style: (fill: black, stroke: black))
        },
      )
    }),
    cetz.canvas({
      plot.plot(
        size: (5.2, 4),
        axis-style: "left",
        x-tick-step: 1,
        y-tick-step: 1,
        x-min: -1.5, x-max: 3,
        y-min: -1.5, y-max: 2.6,
        x-label: $s$,
        y-label: none,
        {
          plot.add(domain: (-1.5, 3), s => calc.max(0, 1 - s), style: (stroke: (paint: gray, thickness: 0.8pt)), label: [$phi$])
          plot.add(((-1.5, -1), (1, -1), (1, 0), (3, 0)), style: (stroke: black + 1.4pt), label: [$partial phi$])
        },
      )
    }),
  ),
  caption: [Left: a convex function with a kink; every dashed line through the marked point with slope
    between the left and the right derivative supports the graph, and the set of these slopes is the
    subdifferential. Right: the hinge function $phi(s) = max{0, 1 - s}$ (gray) and the graph of its
    subdifferential $partial phi$ (black), which is $-1$ for $s < 1$, the whole interval $[-1, 0]$ at $s = 1$,
    and $0$ for $s > 1$.],
) <fig:reg-subdifferential>

#example(title: [Subdifferentials])[
  + *Absolute value.* For $f(t) = abs(t)$ on $RR$: $partial f(t) = {sign(t)}$ for $t != 0$, and
    $partial f(0) = [-1, 1]$, since $c s <= abs(s)$ for all $s$ if and only if $abs(c) <= 1$.
  + *Hinge function and hinge loss.* For $phi(s) = max{0, 1 - s}$: $partial phi(s) = {-1}$ for $s < 1$,
    $partial phi(1) = [-1, 0]$, $partial phi(s) = {0}$ for $s > 1$ (by @lem:reg-subdifferential-real below).
    For the hinge loss $L(y, t) = phi(y t)$ with $y in {-1, 1}$: substituting $s' = y t'$ and using
    $y^2 = 1$, $c (t' - t) <= phi(y t') - phi(y t)$ for all $t'$ is equivalent to
    $c y (s' - y t) <= phi(s') - phi(y t)$ for all $s'$, i.e. $c y in partial phi(y t)$. Hence
    $ partial L(y, t) = y partial phi(y t) = cases({-y} & "if" y t < 1, {-s y : s in [0, 1]} & "if" y t = 1, {0} & "if" y t > 1.) $
  + *Norms.* For the norm of $E$ at $0$: $w' in partial norm(dot)(0)$ if and only if $w'(v) <= norm(v)$ for
    all $v$, i.e. $norm(w') <= 1$. So $partial norm(dot)(0)$ is the closed unit ball of $E'$, a large set
    reflecting the kink of the norm at the origin.
  + *The squared norm of a Hilbert space.* Identifying $H' = H$, the function $Omega(f) = norm(f)_H^2$
    has $partial Omega(f) = {2 f}$. Indeed, $2 f in partial Omega(f)$ because
    $ norm(g)_H^2 - norm(f)_H^2 - ip(g - f, 2 f)_H = norm(g - f)_H^2 >= 0 quad "for all" g in H. $
    Conversely, if
    $u in partial Omega(f)$, then for $v in H$ and $s > 0$,
    $s ip(v, u)_H <= norm(f + s v)_H^2 - norm(f)_H^2 = 2 s ip(v, f)_H + s^2 norm(v)_H^2$; dividing by $s$ and
    letting $s -> 0$ gives $ip(v, u - 2 f)_H <= 0$ for all $v$, so $u = 2 f$.
] <ex:reg-subdifferentials>

On the real line, the subdifferential is completely described by one-sided derivatives.

#lemma(title: [Convex functions on $RR$])[
  Let $phi: RR -> RR$ be convex and $t in RR$.
  + The one-sided derivatives $phi'_(-) (t) := lim_(s -> 0^-) (phi(t + s) - phi(t))/s$ and
    $phi'_(+) (t) := lim_(s -> 0^+) (phi(t + s) - phi(t))/s$ exist in $RR$, and $phi'_(-) (t) <= phi'_(+) (t)$.
  + $partial phi(t) = [phi'_(-) (t), phi'_(+) (t)]$. In particular, $partial phi(t)$ is a nonempty compact
    interval, and it is a singleton if and only if $phi$ is differentiable at $t$; then
    $partial phi(t) = {phi'(t)}$.
  + If $r >= 0$, $delta > 0$ and $abs(t) <= r$, then $abs(c) <= abs(phi|_([-r - delta, r + delta]))_1$ for every
    $c in partial phi(t)$, where $abs(dot)_1$ denotes the Lipschitz constant (finite by @lem:app-convex-lipschitz).
  + If $L$ is a convex loss, then $(x, y, t) |-> L'_(plus.minus) (x, y, t)$, the one-sided derivatives of
    $L(x, y, dot)$, are measurable. Consequently, for every measurable $f: X -> RR$ the function
    $(x, y) |-> L'_(+) (x, y, f(x))$ is measurable and satisfies $L'_(+) (x, y, f(x)) in partial L(x, y, f(x))$
    for all $(x, y) in X times Y$.
] <lem:reg-subdifferential-real>

#proof[
  (i) Let $q(s) := (phi(t + s) - phi(t)) \/ s$ for $s != 0$ be the slope of the chord between $t$ and $t + s$.
  We claim that $q$ is nondecreasing on $RR without {0}$. This follows from the *three-chord inequality*:
  for $a < b < c$,
  $ (phi(b) - phi(a))/(b - a) <= (phi(c) - phi(a))/(c - a) <= (phi(c) - phi(b))/(c - b), $
  which follows by writing $b$ as a convex combination of $a$ and $c$ and rearranging the convexity
  inequality; it is the three-slope inequality of @sec:app that underlies @lem:app-convex-lipschitz. Now let $s_1 < s_2$ be nonzero. If
  $0 < s_1 < s_2$, apply the left inequality to $a = t < b = t + s_1 < c = t + s_2$; if $s_1 < s_2 < 0$,
  apply the right inequality to $a = t + s_1 < b = t + s_2 < c = t$; if $s_1 < 0 < s_2$, apply the outer
  inequality to $a = t + s_1 < b = t < c = t + s_2$. In each case $q(s_1) <= q(s_2)$. Hence
  $phi'_(+) (t) = inf_(s > 0) q(s)$ exists and is $>= q(-1) > -oo$, $phi'_(-) (t) = sup_(s < 0) q(s)$ exists and
  is $<= q(1) < oo$, and $phi'_(-) (t) <= phi'_(+) (t)$.

  (ii) $c in partial phi(t)$ means $c s <= phi(t + s) - phi(t)$ for all $s in RR$, i.e. $c <= q(s)$ for all
  $s > 0$ and $c >= q(s)$ for all $s < 0$. By monotonicity of $q$ this is equivalent to
  $phi'_(-) (t) <= c <= phi'_(+) (t)$. The interval is a singleton if and only if the one-sided derivatives
  agree, i.e. if and only if $phi$ is differentiable at $t$.

  (iii) Since $-r - delta < t < r + delta$, this is @lem:app-convex-lipschitz (iii) with $[a, b] = [-r - delta, r + delta]$.
  Directly: for $0 < s <= delta$, both $t$ and $t plus.minus s$ lie in $[-r - delta, r + delta]$, so by (ii)
  $-ell <= q(-s) <= c <= q(s) <= ell$ with $ell := abs(phi|_([-r - delta, r + delta]))_1$.

  (iv) By (i), $L'_(+) (x, y, t) = lim_(n -> oo) n (L(x, y, t + 1\/n) - L(x, y, t))$ is a pointwise limit of
  measurable functions of $(x, y, t)$, hence measurable; similarly for $L'_(-)$. Composing with the
  measurable map $(x, y) |-> (x, y, f(x))$ gives measurability of $(x, y) |-> L'_(+) (x, y, f(x))$, and
  $L'_(+) (x, y, f(x)) in partial L(x, y, f(x))$ by (ii).
]

To formulate the relation with derivatives on Banach spaces, recall that $f: E -> RR union {oo}$ is
*Gâteaux differentiable* at $w in dom f$ if there is $f'(w) in E'$ with
$lim_(s -> 0) (f(w + s u) - f(w)) \/ s = f'(w) u$ for every $u in E$ (as in @def:loss-frechet). Every Fréchet differentiable function (@def:loss-frechet) is Gâteaux
differentiable with the same derivative.

#proposition(title: [Basic properties])[
  Let $f: E -> RR union {oo}$ be convex and $w in dom f$.
  + $partial f(w)$ is convex and weak\*-closed.
  + If there are $delta > 0$ and $c >= 0$ with $f(v) - f(w) <= c norm(v - w)$ for all $v$ with
    $norm(v - w) < delta$, then $norm(w') <= c$ for every $w' in partial f(w)$.
  + If $f$ is continuous at $w$, then $partial f(w)$ is nonempty, bounded and weak\*-compact.
] <prop:reg-subdifferential-basic>

#proof[
  (i) $partial f(w) = inter.big_(v in E) {w' in E' : w'(v - w) <= f(v) - f(w)}$. Each set in the intersection
  is either $E'$ (if $f(v) = oo$) or a closed half-space for the weak\* topology, because
  $w' |-> w'(v - w)$ is weak\*-continuous and linear. An intersection of convex weak\*-closed sets is convex and
  weak\*-closed.

  (ii) Let $w' in partial f(w)$. For every unit vector $u in E$ and every $s in (0, delta)$,
  $s w'(u) = w'((w + s u) - w) <= f(w + s u) - f(w) <= c s$, so $w'(u) <= c$. Applying this to $-u$ gives
  $abs(w'(u)) <= c$, hence $norm(w') <= c$.

  (iii) By continuity there is $delta > 0$ with $f(v) <= f(w) + 1$ whenever $norm(v - w) <= delta$. As in (ii),
  for $w' in partial f(w)$ and $norm(u) = 1$ we get $delta w'(u) <= f(w + delta u) - f(w) <= 1$, so
  $norm(w') <= 1 \/ delta$. Thus $partial f(w)$ is bounded and weak\*-closed, hence weak\*-compact by the
  Banach–Alaoglu theorem. That $partial f(w)$ is nonempty follows from the Hahn–Banach separation theorem,
  applied to the point $(w, f(w))$ and the interior of the epigraph of $f$, which is nonempty by
  continuity; see @ekeland1976[Ch. I, §5] or @phelps1993[Ch. 1]. (For $E = RR$, nonemptiness is part of
  @lem:reg-subdifferential-real.)
]

The following rules make subdifferentials computable. Recall that the (Banach space) adjoint of a bounded
linear operator $A: E -> F$ is $A': F' -> E'$, $A' y' := y' compose A$.

#proposition(title: [Subdifferential calculus])[
  Let $f, g: F -> RR union {oo}$ be convex and $A: E -> F$ bounded and linear.
  + (Positive multiples.) For $alpha > 0$ and $w in dom f$: $partial (alpha f)(w) = alpha partial f(w)$.
  + (Sum rule.) For $w in dom f inter dom g$: $partial f(w) + partial g(w) subset.eq partial (f + g)(w)$.
    If $f$ is continuous at some point $w_0 in dom f inter dom g$, then
    $partial (f + g)(w) = partial f(w) + partial g(w)$ for all $w in dom f inter dom g$.
  + (Chain rule.) For $v in E$ with $A v in dom f$: $A' partial f(A v) subset.eq partial (f compose A)(v)$. If
    $f$ is continuous at $A v_0$ for some $v_0 in E$ with $A v_0 in dom f$, then
    $partial (f compose A)(v) = A' partial f(A v)$ for all $v in E$ with $A v in dom f$.
  + (Fermat's rule.) For $w in dom f$: $f(w) = min_(v in E) f(v)$ if and only if $0 in partial f(w)$.
  + (Differentiability.) If $f$ is Gâteaux differentiable at $w in dom f$, then $partial f(w) = {f'(w)}$.
    Conversely, if $f$ is continuous at $w$ and $partial f(w)$ is a singleton, then $f$ is Gâteaux
    differentiable at $w$.
  + (Monotonicity.) For $v, w in dom f$, $v' in partial f(v)$ and $w' in partial f(w)$:
    $(v' - w')(v - w) >= 0$.
] <prop:reg-subdifferential-calculus>

#proof[
  (i) $w'(v - w) <= alpha (f(v) - f(w))$ for all $v$ if and only if $alpha^(-1) w' in partial f(w)$.

  (ii) If $w' in partial f(w)$ and $z' in partial g(w)$, adding the two subgradient inequalities gives
  $(w' + z')(v - w) <= (f + g)(v) - (f + g)(w)$. The reverse inclusion under the continuity assumption is the
  Moreau–Rockafellar theorem; its proof is a Hahn–Banach separation argument in $F times RR$, see
  @ekeland1976[Ch. I, §5] or @phelps1993.

  (iii) If $y' in partial f(A v)$ and $u in E$, then
  $(A' y')(u - v) = y'(A u - A v) <= f(A u) - f(A v)$, so $A' y' in partial (f compose A)(v)$. The reverse
  inclusion under the continuity assumption is again a separation argument, see @ekeland1976[Ch. I, §5].

  (iv) $0 in partial f(w)$ means $0 <= f(v) - f(w)$ for all $v$.

  (v) Let $f$ be Gâteaux differentiable at $w$. For $v in dom f$ and $s in (0, 1]$, convexity gives
  $f(w + s (v - w)) <= (1 - s) f(w) + s f(v)$, i.e. $(f(w + s (v - w)) - f(w)) \/ s <= f(v) - f(w)$; letting
  $s -> 0^+$ yields $f'(w)(v - w) <= f(v) - f(w)$, which trivially also holds for $v in.not dom f$. So
  $f'(w) in partial f(w)$. Conversely, if $w' in partial f(w)$, then for $u in E$ and $s > 0$,
  $w'(u) <= (f(w + s u) - f(w)) \/ s -> f'(w) u$, so $w'(u) <= f'(w) u$ for all $u$; replacing $u$ by $-u$
  gives equality, so $w' = f'(w)$. For the converse we use the "max formula": if $f$ is continuous at $w$,
  the one-sided directional derivatives $d^+ f(w; u) := lim_(s -> 0^+) (f(w + s u) - f(w)) \/ s$ exist and
  $d^+ f(w; u) = max {w'(u) : w' in partial f(w)}$ for all $u in E$, see @phelps1993[Ch. 1] or
  @ekeland1976[Ch. I, §5]. If $partial f(w) = {w'}$, this gives $d^+ f(w; u) = w'(u)$ and
  $d^+ f(w; -u) = -w'(u)$, so the two-sided limit exists and equals $w'(u)$, i.e. $f$ is Gâteaux
  differentiable at $w$ with $f'(w) = w'$.

  (vi) Adding $v'(w - v) <= f(w) - f(v)$ and $w'(v - w) <= f(v) - f(w)$ gives $v'(w - v) + w'(v - w) <= 0$,
  i.e. $(v' - w')(v - w) >= 0$.
]

The continuity assumptions in (ii) and (iii) cannot simply be dropped. For example, in $RR^2$ let $f$ be the
indicator function of the closed unit disk centered at $(0, 1)$ (zero on the disk, $+oo$ outside) and $g$
the indicator function of the line $RR times {0}$. Then $dom f inter dom g = {(0, 0)}$, $f + g$ is the
indicator of ${(0, 0)}$, and $partial (f + g)(0) = RR^2$, whereas $partial f(0) + partial g(0) = {0} times RR$.
Neither function is continuous at the only common point of their domains. In our applications one of the
functions will always be finite and continuous everywhere, so this subtlety does not arise.

Finally we compute the subdifferential of the risk viewed as an integral functional on an $L^p$ space.
It is convenient to allow functions of $(x, y)$ here, i.e. to consider
$ J: L^p (P) -> [0, oo], quad J(u) := integral_(X times Y) L(x, y, u(x, y)) dif P(x, y), $
where $L^p (P) = L^p (X times Y, P)$; $J(u)$ depends only on the equivalence class of $u$. For $p in [1, oo)$
and $1/p + 1/p' = 1$ we identify $(L^p (P))'$ with $L^(p') (P)$ via $h |-> (u |-> integral h u dif P)$
(@sec:app-lp).

#proposition(title: [Subdifferential of the risk on $L^p$])[
  Let $P$ be a distribution on $X times Y$, $p in [1, oo)$, $p'$ the conjugate exponent, and $L$ a convex loss
  such that $J(u) < oo$ for all $u in L^p (P)$ (for instance, a $P$-integrable Nemitski loss of order $p$).
  Then for every $u in L^p (P)$,
  $ partial J(u) = {h in L^(p') (P) : h(x, y) in partial L(x, y, u(x, y)) "for" P"-almost all" (x, y) in X times Y}. $
] <prop:reg-subdifferential-integral>

#proof[
  Fix real-valued measurable representatives of $u$ and of the elements of $L^(p') (P)$ below.

  "$supset.eq$": Let $h in L^(p') (P)$ with $h(x, y) in partial L(x, y, u(x, y))$ almost surely, and let
  $v in L^p (P)$. Then almost surely
  $ h(x, y) (v(x, y) - u(x, y)) <= L(x, y, v(x, y)) - L(x, y, u(x, y)). $
  All terms are integrable: $h (v - u) in L^1 (P)$ by Hölder's inequality, and $L(dot, dot, v)$,
  $L(dot, dot, u)$ are integrable because $J(v), J(u) < oo$. Integrating gives
  $integral h (v - u) dif P <= J(v) - J(u)$, i.e. $h in partial J(u)$.

  "$subset.eq$": Let $u' in partial J(u) subset.eq (L^p (P))'$. Since $p < oo$, there is $h in L^(p') (P)$ with
  $u'(v) = integral h v dif P$ for all $v in L^p (P)$ (@sec:app-lp). Fix $t in QQ$ and set
  $ psi_t (x, y) := L(x, y, t) - L(x, y, u(x, y)) - h(x, y) (t - u(x, y)). $
  This function is integrable: $J(t) < oo$ (constants belong to $L^p (P)$ because $P$ is finite),
  $J(u) < oo$, and $h (t - u) in L^1 (P)$ by Hölder. Let $A := {psi_t < 0}$, a measurable set, and
  $v := t ind_A + u ind_(A^c) in L^p (P)$. The subgradient inequality $integral h (v - u) dif P <= J(v) - J(u)$
  reads, since $v = u$ outside $A$,
  $ integral_A h (t - u) dif P <= integral_A (L(x, y, t) - L(x, y, u(x, y))) dif P(x, y), quad "i.e." quad integral_A psi_t dif P >= 0. $
  As $psi_t < 0$ on $A$, this forces $P(A) = 0$, i.e. $psi_t >= 0$ outside the null set $Z_t := A$. Let $Z := union.big_(t in QQ) Z_t$, again a null set. For $(x, y) in.not Z$ we have
  $h(x, y)(t - u(x, y)) <= L(x, y, t) - L(x, y, u(x, y))$ for all $t in QQ$, and since both sides are continuous
  in $t$ (a convex function on $RR$ is continuous), for all $t in RR$. That is,
  $h(x, y) in partial L(x, y, u(x, y))$ for all $(x, y) in.not Z$.
]

#remark(title: [Why $p < oo$?])[
  The only place where $p < oo$ was used is the representation of $u' in (L^p (P))'$ by a function
  $h in L^(p') (P)$. For $p = oo$ this fails: $(L^oo (P))'$ is in general much larger than $L^1 (P)$ (it
  contains functionals given by finitely additive set functions), and subgradients of $J$ on $L^oo (P)$
  need not be representable by functions. This is why the general representer theorem below is formulated
  for Nemitski losses of order $p < oo$.
]


== The general representer theorem <sec:reg-general-representer>

We can now describe $f_(P, lambda)$ for convex losses that are not differentiable. The idea is the same as
in @thm:reg-integral-equation: Fermat's rule $0 in partial risk(L, P, lambda)(f_(P, lambda))$, computed with the
calculus of the previous section. The derivative $L'$ is replaced by a function $h$ with values in the
subdifferential of the loss.

#theorem(title: [General representer theorem])[
  Let $(X, cal(A))$ be a measurable space, $Y subset.eq RR$ closed, $P$ a distribution on $X times Y$,
  $p in [1, oo)$ and $p' in (1, oo]$ with $1/p + 1/p' = 1$. Let $L: X times Y times RR -> [0, oo)$ be a convex,
  $P$-integrable Nemitski loss of order $p$, $H$ an RKHS over $RR$ with bounded measurable kernel $K$ and
  canonical feature map $Phi$, and $lambda > 0$. Then:
  + There is a measurable $h: X times Y -> RR$ with $h in cal(L)^(p') (P)$ such that
    $ h(x, y) in partial L(x, y, f_(P, lambda) (x)) quad "for all" (x, y) in X times Y $
    and
    $ f_(P, lambda) = -1/(2 lambda) EE_P [h Phi] = -1/(2 lambda) integral_(X times Y) h(x, y) Phi(x) dif P(x, y). $ <eq:reg-general-representer>
    In particular, $f_(P, lambda) (x') = -1/(2 lambda) integral h(x, y) K(x', x) dif P(x, y)$ for all $x' in X$.
  + Conversely, if $f in H$ and $h in cal(L)^1 (P)$ satisfy $h(x, y) in partial L(x, y, f(x))$ for $P$-almost
    all $(x, y)$ and $f = -1/(2 lambda) EE_P [h Phi]$, then $f = f_(P, lambda)$.
  + For all $g in H$,
    $ risk(L, P, lambda)(g) - risk(L, P, lambda)(f_(P, lambda)) >= lambda norm(g - f_(P, lambda))_H^2. $ <eq:reg-strong-convexity>
] <thm:reg-general-representer>

#proof[
  By @thm:reg-existence (ii), $f_(P, lambda)$ exists and is unique; note that $L(x, y, t) <= b(x, y) + c abs(t)^p$
  with $b in cal(L)^1 (P)$ and $c >= 0$. Throughout, $Omega(f) := norm(f)_H^2$.

  _Step 1: the risk on $L^p (P)$._ Let $J: L^p (P) -> [0, oo)$, $J(u) := integral L(x, y, u(x, y)) dif P(x, y)$.
  It is finite, since $L(x, y, u(x, y)) <= b(x, y) + c abs(u(x, y))^p$, and convex, since $L$ is. It is
  continuous on $L^p (P)$ by @prop:loss-risk-continuity (iii) and (iv) (a convex loss is continuous).

  _Step 2: the embedding._ Define $E: H -> L^p (P)$ by $(E f)(x, y) := f(x)$. Since $f$ is measurable and
  $abs(f(x)) <= abs(K)_oo norm(f)_H$ (@prop:rkhs-bounded), $E$ is well defined, linear and bounded with
  $norm(E f)_(L^p (P)) <= abs(K)_oo norm(f)_H$. By construction, $risk(L, P) = J compose E$ on $H$, and so
  $risk(L, P, lambda) = J compose E + lambda Omega$.

  _Step 3: the adjoint._ Let $h in L^(p') (P) = (L^p (P))'$; note that $L^(p') (P) subset.eq L^1 (P)$ because
  $P$ is finite. By @eq:reg-kernel-mean, $E' h in H'$ is the functional
  $ g |-> integral h(x, y) (E g)(x, y) dif P(x, y) = integral h(x, y) g(x) dif P(x, y) = ip(g, EE_P [h Phi])_H. $
  Under the Riesz identification $H' = H$, therefore, $E' h = EE_P [h Phi]$.

  _Step 4: Fermat's rule and calculus._ Since $f_(P, lambda)$ minimizes $risk(L, P, lambda)$,
  $0 in partial risk(L, P, lambda)(f_(P, lambda))$ by @prop:reg-subdifferential-calculus (iv). The function
  $lambda Omega$ is finite and continuous on all of $H$, so the sum rule (ii) applies:
  $partial risk(L, P, lambda)(f) = partial (J compose E)(f) + partial (lambda Omega)(f)$. Since $J$ is finite everywhere
  and continuous at $E 0 = 0$, the chain rule (iii) gives $partial (J compose E)(f) = E' partial J(E f)$. By (i) and
  @ex:reg-subdifferentials (iv), $partial (lambda Omega)(f) = {2 lambda f}$. Finally,
  @prop:reg-subdifferential-integral describes $partial J(E f)$. Altogether, for $f := f_(P, lambda)$ there is
  $tilde(h) in L^(p') (P)$ with $tilde(h)(x, y) in partial L(x, y, f(x))$ for $P$-almost all $(x, y)$ and
  $0 = EE_P [tilde(h) Phi] + 2 lambda f$, i.e. $f = -1/(2 lambda) EE_P [tilde(h) Phi]$.

  _Step 5: an everywhere-defined selection._ Let $h_0$ be a real-valued measurable representative of
  $tilde(h)$ and
  $ Z_0 := {(x, y) : h_0 (x, y) in.not partial L(x, y, f(x))} = {h_0 < L'_(-) (dot, dot, f)} union {h_0 > L'_(+) (dot, dot, f)}, $
  where we used @lem:reg-subdifferential-real (ii) and wrote $L'_(plus.minus) (dot, dot, f)$ for
  $(x, y) |-> L'_(plus.minus) (x, y, f(x))$. By @lem:reg-subdifferential-real (iv), $Z_0$ is measurable,
  and $P(Z_0) = 0$ by Step 4. Define $h := h_0$ on $(X times Y) without Z_0$ and
  $h(x, y) := L'_(+) (x, y, f(x))$ on $Z_0$. Then $h$ is measurable, $h = h_0$ $P$-almost surely (so
  $h in cal(L)^(p') (P)$ and $EE_P [h Phi] = EE_P [tilde(h) Phi]$), and $h(x, y) in partial L(x, y, f(x))$ for
  *all* $(x, y)$ by @lem:reg-subdifferential-real (iv). This proves (i); the pointwise formula is
  @lem:reg-kernel-mean (ii).

  _Step 6: the converse and the quadratic growth._ Let $f$ and $h$ be as in (ii) and let $g in H$. Almost
  surely, $h(x, y)(g(x) - f(x)) <= L(x, y, g(x)) - L(x, y, f(x))$. All terms are integrable ($g - f$ is
  bounded, $h in cal(L)^1 (P)$, and the risks of $f$ and $g$ are finite by @thm:reg-existence (ii)), so
  integration and @eq:reg-kernel-mean give
  $ risk(L, P)(g) - risk(L, P)(f) >= integral h(x, y)(g(x) - f(x)) dif P(x, y) = ip(g - f, EE_P [h Phi])_H = -2 lambda ip(g - f, f)_H. $
  Using $norm(g)_H^2 - norm(f)_H^2 = 2 ip(g - f, f)_H + norm(g - f)_H^2$ we obtain
  $ risk(L, P, lambda)(g) - risk(L, P, lambda)(f) >= -2 lambda ip(g - f, f)_H + lambda (norm(g)_H^2 - norm(f)_H^2) = lambda norm(g - f)_H^2 >= 0. $
  Hence $f$ minimizes $risk(L, P, lambda)$, so $f = f_(P, lambda)$, proving (ii). Applying this computation to
  $f = f_(P, lambda)$ and the function $h$ from (i) proves (iii).
]

Let us interpret the theorem.

- *Weights from the loss.* $f_(P, lambda)$ is a superposition of kernel sections $Phi(x) = K(dot, x)$
  with weights $-h(x, y) \/ (2 lambda)$, where $h(x, y)$ is a "generalized slope" of the loss at the
  prediction $f_(P, lambda) (x)$. Wherever $L(x, y, dot)$ is flat near $f_(P, lambda) (x)$ (for the hinge
  loss: $y f_(P, lambda) (x) > 1$), the weight is zero.
- *Differentiable losses.* If $L$ is differentiable, then $partial L(x, y, t) = {L'(x, y, t)}$, so
  $h(x, y) = L'(x, y, f_(P, lambda) (x))$, and we recover the integral equation @eq:reg-integral-equation[] (for losses of order $p$).
- *Non-uniqueness of $h$.* The function $f_(P, lambda)$ is unique, but $h$ need not be (@ex:reg-svm).
- *Quadratic growth.* Part (iii) says that $risk(L, P, lambda)$ grows at least quadratically away from its
  minimizer; this is the "strong convexity" contributed by the regularizer
  (compare @ex:reg-exr-strong-convexity for a proof that avoids subdifferentials).
- *Size of $h$.* Put $B_lambda := abs(K)_oo sqrt(risk(L, P)(0) \/ lambda)$, so that
  $norm(f_(P, lambda))_oo <= B_lambda$ by @prop:reg-norm-bound. Since $h(x, y) in partial L(x, y, f_(P, lambda) (x))$ for *every* $(x, y)$,
  @lem:reg-subdifferential-real (iii) with $r = B_lambda$ and $delta = 1$ gives
  $ abs(h(x, y)) <= abs(L(x, y, dot)|_([-B_lambda - 1, B_lambda + 1]))_1 quad "for all" (x, y) in X times Y, $
  and $abs(h) <= abs(L)_1$ for Lipschitz losses (@def:loss-lipschitz). That the inclusion holds everywhere, not
  only $P$-almost everywhere, is what allows us in @thm:stab-measure to integrate $h$ against a
  *different* distribution $overline(P)$, and thereby to compare $f_(P, lambda)$ with $f_(overline(P), lambda)$.

For the empirical measure we again get a version without any assumption on the kernel.

#corollary(title: [Representer theorem with subgradients])[
  Let $X$ be a nonempty set, $H$ an RKHS over $RR$ on $X$ with kernel $K$, $D in (X times Y)^N$, $lambda > 0$, and
  let $L: X times Y times RR -> [0, oo)$ be such that $L(x_i, y_i, dot)$ is convex for $i = 1, ..., N$. Then
  $f in H$ equals $f_(D, lambda)$ if and only if there are $h_1, ..., h_N in RR$ with
  $ h_i in partial L(x_i, y_i, f(x_i)) quad (i = 1, ..., N) quad "and" quad f = -1/(2 lambda N) sum_(i=1)^N h_i K(dot, x_i). $
  Consequently, for $f = f_(D, lambda)$ and such $h_i$,
  $ f_(D, lambda) = sum_(i=1)^N a_i K(dot, x_i) quad "with" quad a_i = -h_i/(2 lambda N), quad -2 lambda N a_i in partial L(x_i, y_i, f_(D, lambda) (x_i)). $
] <cor:reg-empirical-representer>

#proof[
  "$arrow.l.double$": For $g in H$, $h_i (g(x_i) - f(x_i)) <= L(x_i, y_i, g(x_i)) - L(x_i, y_i, f(x_i))$ for each $i$.
  Averaging and using $1/N sum_i h_i (g - f)(x_i) = ip(g - f, -2 lambda f)_H$ (reproducing property), the
  computation of Step 6 above gives
  $risk(L, D, lambda)(g) - risk(L, D, lambda)(f) >= lambda norm(g - f)_H^2 >= 0$. So $f$ is a minimizer, and
  $f = f_(D, lambda)$ by the uniqueness part of @thm:reg-representer.

  "$==>$": Consider the bounded linear map $A: H -> RR^N$, $A f := (f(x_1), ..., f(x_N))$, and
  $ F_D: RR^N -> [0, oo), quad F_D (bold(t)) := 1/N sum_(i=1)^N L(x_i, y_i, t_i), $
  which is convex and continuous (each $L(x_i, y_i, dot)$ is convex, hence continuous). Then
  $risk(L, D, lambda) = F_D compose A + lambda Omega$ with $Omega = norm(dot)_H^2$. We identify $(RR^N)' = RR^N$
  via the Euclidean inner product and claim that
  $ partial F_D (bold(t)) = {bold(c) in RR^N : N c_i in partial L(x_i, y_i, t_i) "for all" i}. $
  If $N c_i in partial L(x_i, y_i, t_i)$
  for all $i$, summing the subgradient inequalities shows $bold(c) in partial F_D (bold(t))$. Conversely, if
  $bold(c) in partial F_D (bold(t))$, testing the subgradient inequality with $bold(t) + s bold(e)_i$ ($s in RR$)
  gives $c_i s <= 1/N (L(x_i, y_i, t_i + s) - L(x_i, y_i, t_i))$, i.e. $N c_i in partial L(x_i, y_i, t_i)$. The
  adjoint of $A$ maps $bold(c)$ to the functional $g |-> sum_i c_i g(x_i) = ip(g, sum_i c_i K(dot, x_i))_H$. By
  Fermat's rule, the sum rule (with $lambda Omega$ continuous) and the chain rule (with $F_D$ continuous),
  $0 in partial risk(L, D, lambda)(f_(D, lambda))$ yields $bold(c) in partial F_D (A f_(D, lambda))$ with
  $sum_i c_i K(dot, x_i) + 2 lambda f_(D, lambda) = 0$. Put $h_i := N c_i$.
]

#example(title: [Support vector machines: support vectors and box constraints])[
  Let $Y = {-1, 1}$ and $L(y, t) = max{0, 1 - y t}$ be the hinge loss. By @ex:reg-subdifferentials (ii),
  $h_i in partial L(y_i, f(x_i))$ means $h_i = -s_i y_i$ with
  $ s_i = 1 "if" y_i f(x_i) < 1, quad s_i in [0, 1] "if" y_i f(x_i) = 1, quad s_i = 0 "if" y_i f(x_i) > 1. $
  By @cor:reg-empirical-representer, the SVM solution is
  $ f_(D, lambda) = sum_(i=1)^N a_i K(dot, x_i), quad a_i = (s_i y_i)/(2 lambda N), $
  with $s_i$ as above for $f = f_(D, lambda)$. Three facts can be read off:
  + *Box constraints:* $0 <= y_i a_i <= 1\/(2 lambda N)$; every coefficient has the sign of its label (or
    vanishes) and is bounded by $1\/(2 lambda N)$. In particular, a single point, however badly
    misclassified, has only a bounded influence on the solution, in contrast to least squares.
  + *Sparsity:* $a_i = 0$ whenever $y_i f_(D, lambda) (x_i) > 1$, i.e. for points that are classified
    correctly *with margin*. Only points with $y_i f_(D, lambda) (x_i) <= 1$ can enter the expansion; the
    points $x_i$ with $a_i != 0$ are called *support vectors*. In practice their number is often much smaller than $N$, which makes evaluating
    $f_(D, lambda)$ cheap.
  + *Margin violators:* $a_i = y_i \/ (2 lambda N)$ whenever $y_i f_(D, lambda) (x_i) < 1$; the coefficient
    sits at the boundary of the box.

  *A small example.* Let $X = RR$ with the linear kernel $K(x, x') = x x'$, so $H = {x |-> w x : w in RR}$
  with $norm(w x)_H = abs(w)$, and let $D$ consist of $(x_1, y_1) = (1, 1)$, $(x_2, y_2) = (-1, -1)$ and
  $(x_3, y_3) = (3, 1)$, so $N = 3$. For $f(x) = w x$ the margins are $y_i f(x_i) = w, w, 3 w$, and
  $ risk(L, D, lambda)(w x) = 1/3 (2 max{0, 1 - w} + max{0, 1 - 3 w}) + lambda w^2. $
  We claim that $f_(D, lambda) (x) = x$ for $0 < lambda <= 1\/3$. The margins of $f(x) = x$ are $1, 1, 3$, so
  $s_3 = 0$ and $s_1, s_2 in [0, 1]$ are free, and the condition of @cor:reg-empirical-representer reads
  $ x = 1/(6 lambda) (s_1 dot 1 dot K(x, 1) + s_2 dot (-1) dot K(x, -1)) = (s_1 + s_2)/(6 lambda) x, $
  which is solvable with $s_1, s_2 in [0, 1]$ if and only if $6 lambda <= 2$. So $f_(D, lambda) (x) = x$, and the
  point $x_3 = 3$ is not a support vector. Note that $h$ is *not* unique: every pair $(s_1, s_2) in [0, 1]^2$
  with $s_1 + s_2 = 6 lambda$ works. (For $1/3 < lambda < 1$ one finds similarly $f_(D, lambda) (x) = x \/ (3 lambda)$ with
  $s_1 = s_2 = 1$, $s_3 = 0$; see @ex:reg-exr-svm-path for the full solution path.)
] <ex:reg-svm>

#context-note[
  Dividing $risk(L, D, lambda)$ by $2 lambda$ shows that $f_(D, lambda)$ minimizes
  $1/2 norm(f)_H^2 + C sum_i max{0, 1 - y_i f(x_i)}$ with $C = 1\/(2 lambda N)$. Introducing slack variables
  $xi_i >= max{0, 1 - y_i f(x_i)}$ gives the familiar soft-margin SVM of Cortes and Vapnik @cortes1995
  (here without the offset term $b$), and the coefficients $alpha_i := y_i a_i in [0, C]$ are exactly the
  variables of its dual quadratic program; the box constraints above are its constraints $0 <= alpha_i <= C$.
  See @vapnik1998, @schoelkopf2002 and @steinwart2008 for the algorithmic side and the extensive theory.

  Sparsity is a consequence of the flat part of the hinge loss. The logistic loss is strictly decreasing
  in $y t$, so all coefficients are nonzero (@ex:reg-exr-logistic): kernel logistic regression is not sparse.
  For regression, the $epsilon$-insensitive loss $max{0, abs(y - t) - epsilon}$ yields *support vector
  regression*: points strictly inside the "$epsilon$-tube" $abs(y_i - f(x_i)) < epsilon$ get coefficient $0$,
  and $abs(a_i) <= 1\/(2 lambda N)$ (@ex:reg-exr-svr). More generally, @lem:reg-subdifferential-real (iii)
  gives the box constraint $abs(a_i) <= abs(L)_1 \/ (2 lambda N)$ for every Lipschitz continuous loss.
]


== Summary

- The regularized risk $risk(L, P, lambda)(f) = risk(L, P)(f) + lambda norm(f)_H^2$ balances fit against
  complexity; small RKHS norm means small and smooth in the geometry of the kernel. Any minimizer satisfies
  $norm(f_(P, lambda))_H <= sqrt(risk(L, P)(0) \/ lambda)$.
- For convex losses the minimizer is unique as soon as one $f in H$ has finite risk (strict convexity of
  $norm(dot)_H^2$), and it exists by weak compactness (@thm:reg-existence); for $P$-integrable Nemitski losses
  and bounded kernels this holds for every $lambda > 0$. Without convexity minimizers may fail to exist.
- Representer theorem: $f_(D, lambda) in spn{K(dot, x_1), ..., K(dot, x_N)}$. Computing $f_(D, lambda)$ is an
  $N$-dimensional convex problem involving only the Gram matrix; the coefficients are unique if and only
  if the Gram matrix is invertible.
- For differentiable losses, $f_(P, lambda) = -1/(2 lambda) EE_P [L'(x, y, f_(P, lambda) (x)) Phi(x)]$. For the least
  squares loss this gives kernel ridge regression, $(bold(K) + lambda N I) bold(a) = bold(y)$, a spectral
  filter on the data.
- Subdifferentials replace derivatives for convex functions; they obey a calculus (sum rule, chain rule,
  Fermat's rule), and the subdifferential of an integral functional on $L^p$, $p < oo$, is computed
  pointwise.
- General representer theorem: $f_(P, lambda) = -1/(2 lambda) EE_P [h Phi]$ with
  $h(x, y) in partial L(x, y, f_(P, lambda) (x))$ everywhere and $h in cal(L)^(p') (P)$. For SVMs this yields
  box constraints and sparsity (support vectors).
- *Next:* @sec:stab studies how $f_(P, lambda)$ depends on $lambda$ (Q4) and on $P$ (Q8). The general
  representer theorem, in particular the everywhere-defined $h$ and the quadratic growth
  @eq:reg-strong-convexity[], is the main tool there.


== Notes and further reading

The presentation in this chapter follows Chapter 5 of Steinwart and Christmann @steinwart2008, where
the "infinite-sample SVM" $f_(P, lambda)$, its existence and uniqueness, and the general representer theorem
are treated in more generality (e.g. for losses that are not Nemitski of any finite order, and with
explicit treatment of measurability issues). Regularization of ill-posed problems goes back to Tikhonov;
see @tikhonov1977. In statistics, penalized least squares appears as ridge regression and as spline
smoothing (ridge regression goes back to @hoerl1970); Wahba's monograph @wahba1990 develops spline
smoothing systematically in the language of RKHSs, @berlinet2004 describes the interplay between RKHSs,
splines and Gaussian processes, and @rasmussen2006 is the standard reference on Gaussian process
regression. The
representer theorem is due to Kimeldorf and Wahba @kimeldorf1971; its modern general form is from
@schoelkopf2001representer.

Support vector machines were introduced by Cortes and Vapnik @cortes1995; @vapnik1998 describes the
learning-theoretic background, @schoelkopf2002 is a comprehensive treatment of kernel methods including
algorithms, and @shalev2014 gives a gentle introduction to SVMs and kernel methods. The approximation-theoretic
point of view on regularized least squares, including the spectral filter interpretation, is emphasized in
@cucker2007. Why convex surrogates such as the hinge and logistic losses are appropriate for
classification is analysed in @bartlett2006.

Subdifferentials are the central object of convex analysis. @ekeland1976 contains the subdifferential
calculus used here (sum and chain rules via Hahn–Banach separation) together with its use in variational
problems; @phelps1993 treats subdifferentials, monotone operators and differentiability of convex
functions on Banach spaces in depth. The subdifferential of integral functionals
(@prop:reg-subdifferential-integral) is a special case of general results on "normal integrands"; the
simple proof given here exploits that the integrand depends on a single real variable.


== Exercises

#exercise(title: [Strong convexity without subdifferentials])[
  Let $L$ be convex and assume that $f_(P, lambda)$ exists with $risk(L, P, lambda)(f_(P, lambda)) < oo$. Show
  directly from @eq:reg-parallelogram that
  $risk(L, P, lambda)(g) - risk(L, P, lambda)(f_(P, lambda)) >= lambda (1 - theta) norm(g - f_(P, lambda))_H^2$ for all
  $g in H$ and $theta in (0, 1)$, and deduce @eq:reg-strong-convexity. _Hint:_ compare $f_(P, lambda)$ with
  $(1 - theta) f_(P, lambda) + theta g$.
] <ex:reg-exr-strong-convexity>

#exercise(title: [Generalized representer theorem])[
  Let $L$ be an arbitrary loss and $g: [0, oo) -> RR$ strictly increasing. Show that every minimizer of
  $f |-> risk(L, D)(f) + g(norm(f)_H)$ over $H$ lies in $H_D = spn{K(dot, x_1), ..., K(dot, x_N)}$. What remains
  true if $g$ is only nondecreasing?
] <ex:reg-exr-generalized-representer>

#exercise(title: [Minimal-norm interpolation])[
  Assume that the Gram matrix $bold(K)$ is invertible, and let $bold(a)_lambda := (bold(K) + lambda N I)^(-1) bold(y)$ be the
  kernel ridge regression coefficients. Show that $bold(a)_lambda -> bold(K)^(-1) bold(y)$ as $lambda -> 0$, that
  $f_0 := sum_i (bold(K)^(-1) bold(y))_i K(dot, x_i)$ interpolates the data, and that $f_0$ is the unique
  element of minimal norm among all $f in H$ with $f(x_i) = y_i$ for all $i$. _Hint:_ use the projection
  argument of @thm:reg-representer.
] <ex:reg-exr-min-norm>

#exercise(title: [Ridge regression])[
  Let $K(x, x') = ip(x, x')$ on $X = RR^d$ and let $bold(X) in RR^(N times d)$ have rows $x_i^top$. Show that
  $f_(D, lambda) (x) = ip(w, x)$ for the least squares loss, with
  $ w = bold(X)^top (bold(X) bold(X)^top + lambda N I_N)^(-1) bold(y) = (bold(X)^top bold(X) + lambda N I_d)^(-1) bold(X)^top bold(y). $
  _Hint:_ $bold(X)^top (bold(X) bold(X)^top + c I_N) = (bold(X)^top bold(X) + c I_d) bold(X)^top$. Which of the two formulas
  is cheaper to evaluate when $N >> d$, and which when $d >> N$?
] <ex:reg-exr-ridge>

#exercise(title: [Kernel logistic regression])[
  Let $L(y, t) = log(1 + e^(-y t))$ with $y in {-1, 1}$. Compute $L'$, write down the
  coefficient equations @eq:reg-coefficient-equations[], and show that $0 < y_i a_i < 1\/(2 lambda N)$ for all $i$. Conclude that
  every data point is a "support vector".
] <ex:reg-exr-logistic>

#exercise(title: [Support vector regression])[
  Let $L(y, t) = psi(y - t)$ with $psi(r) = max{0, abs(r) - epsilon}$, $epsilon > 0$. Compute $partial L(y, t)$ and
  show that the coefficients $a_i = -h_i \/ (2 lambda N)$ of @cor:reg-empirical-representer satisfy
  $abs(a_i) <= 1\/(2 lambda N)$, $a_i = 0$ if $abs(y_i - f_(D, lambda) (x_i)) < epsilon$, and
  $a_i = sign(y_i - f_(D, lambda) (x_i)) \/ (2 lambda N)$ if $abs(y_i - f_(D, lambda) (x_i)) > epsilon$.
] <ex:reg-exr-svr>

#exercise(title: [The SVM solution path])[
  In the three-point example of @ex:reg-svm, show that $f_(D, lambda) (x) = w(lambda) x$ with
  $ w(lambda) = cases(1 & "for" 0 < lambda <= 1\/3, 1\/(3 lambda) & "for" 1\/3 <= lambda <= 1, 1\/3 & "for" 1 <= lambda <= 5\/2, 5\/(6 lambda) & "for" lambda >= 5\/2,) $
  and determine the support vectors in each regime. _Hint:_ in general $w = (s_1 + s_2 + 3 s_3) \/ (6 lambda)$.
] <ex:reg-exr-svm-path>
