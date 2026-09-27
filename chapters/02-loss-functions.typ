#import "/template.typ": *

= Loss Functions and Their Risks <sec:loss>

In @sec:learn we formalized the learning problem. An unknown distribution $P$ on $X times Y$ generates
the data, a loss function $L$ measures how bad a prediction $t = f(x)$ is when the true output is $y$,
and the quality of a decision function $f$ is its risk
$ risk(L, P)(f) = integral_(X times Y) L(x, y, f(x)) dif P(x, y). $
We also saw in @sec:learn-overfitting that minimizing the empirical risk over all measurable functions
fails. The remedy we pursue in this book is to minimize a *regularized* risk
$risk(L, P)(f) + lambda norm(f)_H^2$ over a reproducing kernel Hilbert space $H$ (@sec:learn-roadmap).
To show that minimizers exist, are unique, can be characterized by equations and depend continuously on the
data, we need to know what kind of functional $f |-> risk(L, P)(f)$ is. Is it measurable, convex,
continuous, Lipschitz continuous, differentiable?

This chapter answers these questions. The guiding principle is simple: *properties of $t |-> L(x, y, t)$
are inherited by $f |-> risk(L, P)(f)$*, because the risk is an average of the values
$L(x, y, f(x))$. Convexity is inherited without any further assumption. Continuity, however, is not: the
integral of a limit need not be the limit of the integrals. The inheritance of continuity and
differentiability therefore requires growth conditions on $L$ that provide integrable majorants. These are
the *Nemitski conditions* of @sec:loss-nemitski. With them, the risk becomes a continuous functional on
$L^oo (P_X)$ or $L^p (P_X)$ (@prop:loss-risk-continuity), a Lipschitz continuous one for Lipschitz losses
(@prop:loss-lipschitz-risk), and a Fréchet differentiable one for differentiable losses
(@prop:loss-frechet). In the second half of the chapter we study the two structural classes of losses that
cover almost all losses used in practice, distance-based losses for regression and margin-based losses for
classification, and we end with a catalogue of the standard losses and their properties
(@ex:loss-catalogue, @tab:loss-properties).

The results of this chapter are the analytic input for @sec:reg. There, the existence of regularized
minimizers (@thm:reg-existence) combines continuity and convexity of the risk, the integral equation
@eq:reg-integral-equation[] for the minimizer comes from the Fréchet derivative, and the general
representer theorem (@thm:reg-general-representer) relies on continuity of the risk on $L^p$.

*Standing assumptions.* Throughout this chapter, $(X, cal(A))$ is a measurable space, $Y subset.eq RR$ is
closed and equipped with its Borel σ-algebra $borel(Y)$, $P$ is a distribution (probability measure) on
$X times Y$ with respect to $cal(A) times.o borel(Y)$, and $P_X$ denotes its marginal on $X$. A *loss* is a
measurable function $L: X times Y times RR -> [0, oo)$ (@def:learn-loss), where $X times Y times RR$
carries the σ-algebra $cal(A) times.o borel(Y) times.o borel(RR)$. A supervised loss $L: Y times RR -> [0, oo)$
is regarded as a loss via $L(x, y, t) := L(y, t)$, and an unsupervised loss $L: X times RR -> [0, oo)$ via
$L(x, y, t) := L(x, t)$. For $p in (0, oo]$ we write $norm(f)_(L^p (P_X))$ for the $L^p$-(quasi)norm with
respect to $P_X$; in particular $norm(f)_(L^oo (P_X))$ is the essential supremum of $abs(f)$, whereas
$norm(f)_oo = sup_(x in X) abs(f(x))$ is the supremum norm. All results apply in particular to the empirical
measure $D$ of a data set (@def:learn-empirical-risk).

== The risk as a functional <sec:loss-functional>

Recall from @def:learn-risk that for a measurable $f: X -> RR$ the function $(x, y) |-> L(x, y, f(x))$ is
measurable, being the composition of $L$ with the measurable map $(x, y) |-> (x, y, f(x))$. Since it is
nonnegative, its integral
$ risk(L, P)(f) = integral_(X times Y) L(x, y, f(x)) dif P(x, y) in [0, oo] $
always exists, but it may be $+oo$. So $risk(L, P)$ is a map $meas(X) -> [0, oo]$, and it is in general
*nonlinear*: for the least squares loss, for instance, $risk(L, P)(2 f)$ is not $2 risk(L, P)(f)$. Our first observation is that
the risk does not see modifications of $f$ on $P_X$-null sets.

#lemma[
  Let $f, g in meas(X)$ with $f = g$ $P_X$-almost surely. Then $L(x, y, f(x)) = L(x, y, g(x))$ for
  $P$-almost all $(x, y) in X times Y$, and in particular $risk(L, P)(f) = risk(L, P)(g)$.
] <lem:loss-classes>

#proof[
  Let $N := {x in X : f(x) != g(x)} in cal(A)$. Then
  ${(x, y) : L(x, y, f(x)) != L(x, y, g(x))} subset.eq N times Y$, and
  $P(N times Y) = P_X (N) = 0$ by the definition of the marginal distribution.
]

Consequently, $risk(L, P)$ is well defined on the space $L^0 (P_X)$ of equivalence classes of measurable
functions modulo $P_X$-null functions, and on its subspaces $L^p (P_X)$. This is the setting in which
continuity will be studied in @sec:loss-nemitski.

=== Measurability of the risk

Why should we care whether $f |-> risk(L, P)(f)$ is measurable? A learning algorithm produces a decision
function $f_D$ that depends on the random data set $D$. To make statements such as "with probability at
least $1 - delta$ the excess risk $risk(L, P)(f_D) - bayes(L, P)$ is at most $epsilon$", the quantity
$risk(L, P)(f_D)$ must be a random variable. It is natural to split $D |-> risk(L, P)(f_D)$ into the map
$D |-> f_D$ into a space $cal(F)$ of functions and the map $risk(L, P): cal(F) -> [0, oo]$, and to ask for
measurability of both. For the second map we need a σ-algebra on $cal(F)$; if $cal(F)$ carries a metric, the
natural choice is the Borel σ-algebra $borel(cal(F))$. The metric must be linked to the values $f(x)$,
since these are what the loss sees.

#definition[
  Let $cal(F) subset.eq meas(X)$ and let $d$ be a metric on $cal(F)$. We say that $d$ *dominates pointwise
  convergence* if for all $f in cal(F)$ and all sequences $(f_n)_(n in NN) subset.eq cal(F)$,
  $ lim_(n -> oo) d(f_n, f) = 0 quad ==> quad lim_(n -> oo) f_n (x) = f(x) quad "for all" x in X. $
] <def:loss-dominates-pointwise>

Equivalently, every point evaluation $cal(F) -> RR$, $f |-> f(x)$, is continuous with respect to $d$ (in
metric spaces, continuity and sequential continuity coincide).

#example[
  + *Continuous functions.* Let $(X, d_X)$ be a compact metric space with $cal(A) = borel(X)$ and
    $cal(F) = C(X)$ with $d(f, g) = norm(f - g)_oo$. Uniform convergence implies pointwise convergence, so $d$
    dominates pointwise convergence. $(C(X), norm(dot)_oo)$ is complete, since uniform limits of continuous
    functions are continuous. It is also separable: $X$ is compact, hence separable, so let
    $\{x_k : k in NN\}$ be dense in $X$ and $g_k := d_X (dot, x_k) in C(X)$. The subalgebra $cal(G)$ of $C(X)$
    generated by the constant function $1$ and the $g_k$ separates points: if $x != x'$, put
    $delta := d_X (x, x') > 0$ and choose $k$ with $d_X (x, x_k) < delta\/2$; then
    $g_k (x) < delta \/ 2 < d_X (x, x') - d_X (x, x_k) <= g_k (x')$. By the Stone–Weierstrass theorem
    (@thm:app-stone-weierstrass), $cal(G)$ is dense in $C(X)$. The countable set of polynomials with *rational*
    coefficients in finitely many $g_k$ is dense in $cal(G)$ (perturbing the finitely many coefficients of a
    polynomial in bounded functions changes it only slightly in the supremum norm), hence dense in $C(X)$.
  + *Reproducing kernel Hilbert spaces.* Let $H$ be a real RKHS on $X$ with kernel $K$ (@def:rkhs,
    @def:rkhs-kernel). Norm convergence in $H$ implies pointwise convergence, since
    $abs(f_n (x) - f(x)) <= sqrt(K(x, x)) norm(f_n - f)_H$ (@prop:rkhs-norm-convergence). If all functions of
    $H$ are measurable (by @prop:rkhs-measurable this holds if and only if every $K(dot, x)$ is measurable)
    and $H$ is separable (for instance if $X$ is a separable topological space and $K$ is continuous,
    @prop:rkhs-separable), then $H$ with its norm metric satisfies all assumptions of
    @prop:loss-measurability below. This is the case relevant for the rest of the book.
  + *A non-example.* $L^p (P_X)$ does not fit into this framework: its elements are equivalence classes, so
    $f(x)$ is not defined, and $L^p$-convergence does not even imply almost sure convergence (the
    "typewriter sequence" of indicator functions of dyadic intervals sweeping over $[0, 1]$ converges to
    $0$ in $L^p [0,1]$ for every $p < oo$, but at no point). For such spaces we obtain measurability of the risk from its
    continuity instead (@rem:loss-measurability-lp).
] <ex:loss-dominating-spaces>

#proposition[
  Let $cal(F) subset.eq meas(X)$ be equipped with a metric $d$ such that $(cal(F), d)$ is complete and
  separable and $d$ dominates pointwise convergence. Equip $cal(F)$ with its Borel σ-algebra
  $borel(cal(F))$. Then:
  + The evaluation map $cal(F) times X -> RR$, $(f, x) |-> f(x)$, is $borel(cal(F)) times.o cal(A)$-measurable.
  + For every loss $L$, the map $X times Y times cal(F) -> [0, oo)$, $(x, y, f) |-> L(x, y, f(x))$, is
    $cal(A) times.o borel(Y) times.o borel(cal(F))$-measurable.
  + For every loss $L$ and every distribution $P$ on $X times Y$, the risk
    $risk(L, P): cal(F) -> [0, oo]$ is $borel(cal(F))$-measurable.
] <prop:loss-measurability>

#proof[
  (i) For fixed $f in cal(F)$ the map $x |-> f(x)$ is measurable because $cal(F) subset.eq meas(X)$, and for
  fixed $x in X$ the map $f |-> f(x)$ is continuous because $d$ dominates pointwise convergence. Hence the
  evaluation map is a Carathéodory function on $X times cal(F)$ with $cal(F)$ a separable metric space, and
  therefore jointly measurable (@thm:app-caratheodory).

  (ii) Consider $T: X times Y times cal(F) -> X times Y times RR$, $T(x, y, f) := (x, y, f(x))$. Its first two
  components are coordinate projections, and its third component is the composition of the projection
  $(x, y, f) |-> (f, x)$ with the evaluation map, which is measurable by (i). A map into a product
  σ-algebra is measurable if and only if all its components are, so $T$ is measurable, and so is
  $L compose T$.

  (iii) By (ii), $g(f, (x, y)) := L(x, y, f(x))$ is a nonnegative
  $borel(cal(F)) times.o (cal(A) times.o borel(Y))$-measurable function on $cal(F) times (X times Y)$. By
  Tonelli's theorem in the form of @thm:app-fubini (i), which needs no measure on the first factor
  $cal(F)$, the map $f |-> integral_(X times Y) g(f, (x, y)) dif P(x, y) = risk(L, P)(f)$ is
  $borel(cal(F))$-measurable.
]

#remark[
  The proof uses only the *separability* of $(cal(F), d)$; completeness is not needed (@thm:app-caratheodory
  holds for separable metrizable parameter spaces), but all spaces we use are complete anyway.
  Separability cannot simply be dropped: joint measurability of Carathéodory functions may fail for
  non-separable parameter spaces. For $L^p (P_X)$, which does not dominate pointwise convergence, we
  get measurability differently: whenever $risk(L, P)$ is *continuous* on $L^p (P_X)$
  (@prop:loss-risk-continuity), it is Borel measurable, as every continuous map between metric spaces is.
] <rem:loss-measurability-lp>

== Convexity and semicontinuity <sec:loss-convexity>

Most properties of a loss that matter for us are properties of the functions $t |-> L(x, y, t)$ for fixed
$(x, y)$.

#definition[
  A loss $L: X times Y times RR -> [0, oo)$ is called *convex*, *strictly convex*, or *continuous* if for
  every $(x, y) in X times Y$ the function $L(x, y, dot): RR -> [0, oo)$ is convex, strictly convex, or
  continuous, respectively.
] <def:loss-convex-continuous>

A real-valued convex function on $RR$ is automatically continuous, even locally Lipschitz continuous
(@lem:app-convex-lipschitz). Hence *every convex loss is continuous*, a fact we shall use repeatedly: the
continuity results below apply to all convex losses.

Convexity is the property that makes minimization tractable: local minima are global, and first-order
conditions are sufficient. It passes to the risk without any integrability assumption, provided we handle
the value $+oo$ correctly. For functions with values in $[0, oo]$ we use the conventions $a dot oo = oo$
for $a > 0$ and $0 dot oo = 0$.

#proposition[
  Let $L$ be a convex loss and $P$ a distribution on $X times Y$.
  + For all $f, g in meas(X)$ and $alpha in [0, 1]$,
    $ risk(L, P)(alpha f + (1 - alpha) g) <= alpha risk(L, P)(f) + (1 - alpha) risk(L, P)(g). $
    In particular, the risk $risk(L, P): meas(X) -> [0, oo]$ is a convex functional, and the set of
    functions with finite risk, ${f in meas(X) : risk(L, P)(f) < oo}$, is convex.
  + If $L$ is strictly convex, then for all $f, g in meas(X)$ with $risk(L, P)(f) < oo$,
    $risk(L, P)(g) < oo$ and $P_X ({x in X : f(x) != g(x)}) > 0$, and for all $alpha in (0, 1)$,
    $ risk(L, P)(alpha f + (1 - alpha) g) < alpha risk(L, P)(f) + (1 - alpha) risk(L, P)(g). $
  + If $L$ is strictly convex, then $risk(L, P)$ has, up to $P_X$-null sets, at most one minimizer on
    ${f in meas(X) : risk(L, P)(f) < oo}$. More generally, if $cal(F) subset.eq meas(X)$ is convex and
    $f, g in cal(F)$ both minimize $risk(L, P)$ over $cal(F)$ with finite minimal value, then $f = g$
    $P_X$-almost surely.
] <prop:loss-convex-risk>

#proof[
  (i) Convexity of $L(x, y, dot)$ gives, for every $(x, y) in X times Y$,
  $ L(x, y, alpha f(x) + (1 - alpha) g(x)) <= alpha L(x, y, f(x)) + (1 - alpha) L(x, y, g(x)). $
  Integrating this inequality between nonnegative measurable functions with respect to $P$, and using
  linearity of the integral for nonnegative functions (which is valid in $[0, oo]$ with the conventions
  above), gives the claim.

  (ii) Let $alpha in (0, 1)$ and define $h: X times Y -> [0, oo)$ by
  $ h(x, y) := alpha L(x, y, f(x)) + (1 - alpha) L(x, y, g(x)) - L(x, y, alpha f(x) + (1 - alpha) g(x)). $
  This is a well-defined (all three terms are finite), measurable and nonnegative function, and by strict
  convexity $h(x, y) > 0$ whenever $f(x) != g(x)$. Hence $h > 0$ on $N times Y$ with
  $N := {f != g}$, and $P(N times Y) = P_X (N) > 0$. A nonnegative function that is strictly positive on a
  set of positive measure has a strictly positive integral, so $integral h dif P > 0$. Since
  $risk(L, P)(f)$ and $risk(L, P)(g)$ are finite, so is $risk(L, P)(alpha f + (1 - alpha) g)$ by (i), and by
  linearity
  $ 0 < integral h dif P = alpha risk(L, P)(f) + (1 - alpha) risk(L, P)(g) - risk(L, P)(alpha f + (1 - alpha) g). $

  (iii) Let $m < oo$ be the minimal value and suppose $P_X (f != g) > 0$. Then $(f + g)\/2 in cal(F)$ and,
  by (ii), $risk(L, P)((f + g)\/2) < (m + m)\/2 = m$, a contradiction.
]

Both hypotheses in (ii) are needed. If $f = g$ almost surely, the two sides coincide by
@lem:loss-classes. If $risk(L, P)(f) = oo$, both sides are $+oo$. Part (iii) applied to $cal(F) = meas(X)$
shows that for a strictly convex loss with finite Bayes risk the Bayes decision function (@def:learn-bayes)
is unique up to $P_X$-null sets, if it exists. Uniqueness of regularized minimizers in @prop:reg-uniqueness
is based on the same argument.

#context-note[
  In binary classification the loss we actually care about, the classification loss
  $L(y, t) = ind_((-oo, 0]) (y sign(t))$ of @ex:learn-classification, is not convex. Minimizing its empirical
  risk over a class of functions is a non-convex, combinatorial problem. This is the main reason why
  learning algorithms such as support vector machines, logistic regression and boosting minimize a convex
  *surrogate* loss instead (hinge, logistic, exponential; see @sec:loss-catalogue). Whether minimizing the
  surrogate risk also drives the classification risk to its minimum is the question of *classification
  calibration*, answered for margin-based losses by @bartlett2006; see also @steinwart2008[Chapter 3].
]

=== Continuity: a warning

Suppose that $L$ is continuous and that $f_n (x) -> f(x)$ for every $x in X$. Then we have
$L(x, y, f_n (x)) -> L(x, y, f(x))$ for every $(x, y)$. Does it follow that the risks converge,
$risk(L, P)(f_n) -> risk(L, P)(f)$? The following example shows that it does not, even for the most
harmless loss one can imagine.

#example[
  Let $X = [0, 1]$ with the Borel σ-algebra, $Y = RR$, and let $P$ be the distribution of $(x, 0)$ with $x$
  uniformly distributed on $[0, 1]$, that is, $P_X$ is the Lebesgue measure on $[0, 1]$ and $y = 0$
  almost surely. Let $L(y, t) = (y - t)^2$ be the least squares loss, which is continuous, strictly convex and
  smooth. Then $risk(L, P)(f) = integral_0^1 f(x)^2 dif x$. For
  $ f_n := sqrt(n) thin ind_((0, 1\/n]), quad n in NN, $
  we have $f_n (x) -> 0$ for every $x in [0, 1]$ (for $x > 0$ as soon as $n > 1\/x$, and $f_n (0) = 0$), but
  $ risk(L, P)(f_n) = n dot 1/n = 1 quad "for all" n, quad "while" quad risk(L, P)(0) = 0. $
  With $g_n := n ind_((0, 1\/n])$ we even get $risk(L, P)(g_n) = n -> oo$ although $g_n -> 0$ pointwise.
  Note also that $norm(f_n)_(L^1 (P_X)) = n^(-1\/2) -> 0$, so the least squares risk is not continuous
  on $L^1 (P_X)$ either.
] <ex:loss-spike>

#intuition[
  The functions $f_n$ are tall, thin spikes. Pointwise convergence cannot see them, because each point
  is eventually outside the spike, but the risk averages the *squared height* over the spike, and this
  average does not vanish. To obtain continuity of the risk we must prevent mass from escaping into
  such spikes, either by bounding the functions uniformly or by controlling the growth of $L(x, y, t)$ in
  $t$ so that the norm in which $f_n -> f$ controls the size of $L(x, y, f_n (x))$. This is exactly what the
  Nemitski conditions of @sec:loss-nemitski do.
]

In the example, the risk of the limit ($0$) is smaller than the limit of the risks ($1$); it is never larger.
This is a general phenomenon, and it holds under a convergence notion much weaker than pointwise convergence. Recall
that $f_n$ *converges to $f$ in probability* (with respect to $P_X$) if
$ lim_(n -> oo) P_X ({x in X : abs(f_n (x) - f(x)) >= epsilon}) = 0 quad "for every" epsilon > 0. $
Almost sure convergence implies convergence in probability, since $P_X$ is finite. So does convergence in
$L^p (P_X)$: for $p < oo$ by Markov's inequality,
$ P_X ({abs(f_n - f) >= epsilon}) <= epsilon^(-p) norm(f_n - f)_(L^p (P_X))^p, $
and trivially for $p = oo$. Conversely, every sequence converging in probability has a subsequence
converging almost surely (@thm:app-convergence).

#proposition[
  Let $L$ be a continuous loss, $P$ a distribution on $X times Y$, and let $f, f_1, f_2, ... in meas(X)$ with
  $f_n -> f$ in probability with respect to $P_X$. Then
  $ risk(L, P)(f) <= liminf_(n -> oo) risk(L, P)(f_n). $
  In particular, $risk(L, P)$ is lower semicontinuous on $L^p (P_X)$ for every $p in (0, oo]$ and with
  respect to $P_X$-almost sure convergence.
] <prop:loss-lsc>

#proof[
  Let $ell := liminf_(n -> oo) risk(L, P)(f_n) in [0, oo]$. *Step 1.* Choose a subsequence
  $(f_(n_k))_k$ with $risk(L, P)(f_(n_k)) -> ell$. *Step 2.* The subsequence still converges to $f$ in
  probability, so it has a further subsequence $(f_(m_j))_j$, $m_j = n_(k_j)$, with $f_(m_j) (x) -> f(x)$ for
  all $x$ outside a $P_X$-null set $N$ (@thm:app-convergence). As a subsequence of a convergent sequence,
  $risk(L, P)(f_(m_j)) -> ell$. (The two steps cannot be merged: an arbitrary almost surely convergent
  subsequence need not realize the $liminf$.) For $(x, y) in.not N times Y$, continuity of $L(x, y, dot)$
  gives $L(x, y, f_(m_j) (x)) -> L(x, y, f(x))$, and $P(N times Y) = P_X (N) = 0$. By Fatou's lemma
  (@thm:app-convergence), applied to nonnegative functions converging $P$-almost surely,
  $ risk(L, P)(f) = integral lim_(j -> oo) L(x, y, f_(m_j) (x)) dif P(x, y)
    <= liminf_(j -> oo) integral L(x, y, f_(m_j) (x)) dif P(x, y) = ell. $
  The last statement follows because the listed modes of convergence imply convergence in probability, and
  lower semicontinuity on a metric space is equivalent to sequential lower semicontinuity.
]

The continuity of $L$ cannot be dropped, not even for uniformly convergent sequences.

#example[
  Let $L(y, t) = ind_((-oo, 0]) (y sign(t))$ be the classification loss on $Y = {-1, 1}$, with the
  convention $sign(0) = 1$ (@ex:learn-classification), and let $P$ be any distribution with $y = -1$
  almost surely. For the constant functions $f_n := -1\/n$ we have $f_n -> 0$ uniformly, but
  $L(-1, -1\/n) = ind_((-oo, 0]) (1) = 0$ while $L(-1, 0) = ind_((-oo, 0]) (-1) = 1$. Hence
  $risk(L, P)(f_n) = 0$ for all $n$, but $risk(L, P)(0) = 1$.
] <ex:loss-01-not-lsc>

Lower semicontinuity plus convexity is what the "direct method" of the calculus of variations needs to
produce minimizers (@lem:app-existence-minimizer). For the existence result in @sec:reg, however, we will
use the stronger property of continuity, which we establish next.

== Nemitski losses and continuity of the risk <sec:loss-nemitski>

By the dominated convergence theorem, the risks $risk(L, P)(f_n)$ converge to $risk(L, P)(f)$ whenever
$L(x, y, f_n (x)) -> L(x, y, f(x))$ almost surely *and* there is a $P$-integrable majorant of the functions
$(x, y) |-> L(x, y, f_n (x))$. The following growth condition produces such majorants from bounds on the
$f_n$. It splits the size of the loss into a part $b(x, y)$ that may depend on the data point but not on the
prediction, and a part $h(abs(t))$ that depends only on the size of the prediction.

#definition(title: [Nemitski losses])[
  A loss $L: X times Y times RR -> [0, oo)$ is called a *Nemitski loss* if there exist a measurable function
  $b: X times Y -> [0, oo)$ and a non-decreasing function $h: [0, oo) -> [0, oo)$ such that
  $ L(x, y, t) <= b(x, y) + h(abs(t)) quad "for all" (x, y, t) in X times Y times RR. $ <eq:loss-nemitski>
  It is called a *Nemitski loss of order $p in (0, oo)$* if @eq:loss-nemitski holds with $h(s) = c s^p$ for
  some constant $c >= 0$, that is,
  $ L(x, y, t) <= b(x, y) + c abs(t)^p quad "for all" (x, y, t) in X times Y times RR. $
  If $P$ is a distribution on $X times Y$ and $b$ can be chosen with $integral b dif P < oo$, then $L$ is a
  *$P$-integrable Nemitski loss* (of order $p$, respectively).
] <def:loss-nemitski>

#remark[
  + If $L$ is a $P$-integrable Nemitski loss and $f in meas(X)$ satisfies $abs(f) <= B$ $P_X$-almost surely,
    then $L(x, y, f(x)) <= b(x, y) + h(B)$ for $P$-almost all $(x, y)$ (as $h$ is non-decreasing), so
    $ risk(L, P)(f) <= norm(b)_(L^1 (P)) + h(B) < oo. $
    In particular $risk(L, P)(0) < oo$, and hence the Bayes risk $bayes(L, P) <= risk(L, P)(0)$ is finite.
  + If $L$ is a $P$-integrable Nemitski loss of order $p$, then
    $risk(L, P)(f) <= norm(b)_(L^1 (P)) + c norm(f)_(L^p (P_X))^p$ for every $f in meas(X)$, so the risk is
    finite on $L^p (P_X)$.
  + A Nemitski loss of order $p$ is a Nemitski loss, and it is also of every order $q >= p$, because
    $s^p <= 1 + s^q$ for $s >= 0$ (replace $b$ by $b + c$).
  + For the empirical measure $D$ of a data set, *every* Nemitski loss is $D$-integrable, because
    $integral b dif D = 1/N sum_(i=1)^N b(x_i, y_i) < oo$. Integrability of $b$ is a genuine restriction only
    for the unknown distribution $P$.
  + The name refers to the *Nemytskii operators* (or superposition operators) $f |-> L(dot, dot, f(dot))$ of
    nonlinear analysis, whose mapping properties between function spaces are governed by growth conditions of
    exactly this type. We use the spelling of @steinwart2008.
] <rem:loss-nemitski-basic>

#example[
  + The least squares loss satisfies $(y - t)^2 <= 2 y^2 + 2 t^2$, so it is a Nemitski loss of order $2$
    with $b(x, y) = 2 y^2$. It is $P$-integrable if $integral y^2 dif P(x, y) < oo$, the moment condition
    of @ex:learn-least-squares.
  + The hinge loss $L(y, t) = max{0, 1 - y t}$ on $Y = {-1, 1}$ satisfies $L(y, t) <= 1 + abs(t)$, so it is a
    $P$-integrable Nemitski loss of order $1$ for *every* $P$ (with $b equiv 1$).
  + The classification loss is bounded by $1$, so it is a $P$-integrable Nemitski loss for every $P$ (with
    $b equiv 1$ and $h equiv 0$).
] <ex:loss-nemitski-examples>

Now we can prove that the risk is continuous. In (i) we allow any sequence that converges almost surely and
is uniformly bounded; (ii) and (iii) are the resulting continuity statements on $L^oo$ and $L^p$. Part (iv)
records that nothing changes if the functions are allowed to depend on $y$ as well, which is needed in
@thm:reg-general-representer.

#proposition(title: [Continuity of the risk])[
  Let $P$ be a distribution on $X times Y$ and let $L$ be a continuous, $P$-integrable Nemitski loss.
  + Let $B >= 0$ and let $f, f_1, f_2, ... in meas(X)$ with $abs(f_n (x)) <= B$ for all $n in NN$ and
    $P_X$-almost all $x in X$, and $f_n -> f$ $P_X$-almost surely. Then all risks
    $risk(L, P)(f_n), risk(L, P)(f)$ are finite and $lim_(n -> oo) risk(L, P)(f_n) = risk(L, P)(f)$.
  + The map $risk(L, P): L^oo (P_X) -> [0, oo)$ is well defined and continuous.
  + If $L$ is a $P$-integrable Nemitski loss of order $p in [1, oo)$, then $risk(L, P): L^p (P_X) -> [0, oo)$
    is well defined and continuous.
  + Statements (i)–(iii) remain true for functions of both variables: if $meas(X)$, $P_X$, $L^oo (P_X)$ and
    $L^p (P_X)$ are replaced by the measurable functions $F: X times Y -> RR$, $P$, $L^oo (P)$ and $L^p (P)$,
    and $risk(L, P)$ by $F |-> integral_(X times Y) L(x, y, F(x, y)) dif P(x, y)$.
] <prop:loss-risk-continuity>

#proof[
  Let $b$ and $h$ be as in @def:loss-nemitski with $integral b dif P < oo$.

  (i) Let $N subset.eq X$ be a $P_X$-null set outside of which $abs(f_n (x)) <= B$ for all $n$ and
  $f_n (x) -> f(x)$; it exists because a countable union of null sets is null. For $x in.not N$ also
  $abs(f(x)) <= B$. For $(x, y) in.not N times Y$ we have
  $ L(x, y, f_n (x)) <= b(x, y) + h(abs(f_n (x))) <= b(x, y) + h(B), $
  and $b + h(B)$ is $P$-integrable because $P$ is a probability measure. The same bound holds for
  $L(x, y, f(x))$, so all risks are finite. Continuity of $L(x, y, dot)$ gives
  $L(x, y, f_n (x)) -> L(x, y, f(x))$ for $(x, y) in.not N times Y$, that is, $P$-almost surely. By the
  dominated convergence theorem (@thm:app-convergence), $risk(L, P)(f_n) -> risk(L, P)(f)$.

  (ii) By @lem:loss-classes, $risk(L, P)(f)$ does not depend on the representative of $f in L^oo (P_X)$, and
  it is finite by @rem:loss-nemitski-basic (i). Since $L^oo (P_X)$ is a metric space, it suffices to prove
  sequential continuity. Let $norm(f_n - f)_(L^oo (P_X)) -> 0$ and fix representatives. There is $n_0$ with
  $norm(f_n - f)_(L^oo (P_X)) <= 1$ for $n >= n_0$, so $abs(f_n) <= B := norm(f)_(L^oo (P_X)) + 1$
  $P_X$-almost surely for $n >= n_0$. Moreover, for each $n$ we have
  $abs(f_n (x) - f(x)) <= norm(f_n - f)_(L^oo (P_X))$ outside a null set $N_n$, so $f_n -> f$ outside the null
  set $union.big_n N_n$. Part (i), applied to $(f_n)_(n >= n_0)$, gives $risk(L, P)(f_n) -> risk(L, P)(f)$.

  (iii) Let $L(x, y, t) <= b(x, y) + c abs(t)^p$ with $integral b dif P < oo$. By @lem:loss-classes and
  @rem:loss-nemitski-basic (ii), $risk(L, P)$ is well defined and finite on $L^p (P_X)$. Let
  $norm(f_n - f)_(L^p (P_X)) -> 0$ and suppose, for a contradiction, that $risk(L, P)(f_n) arrow.r.not risk(L, P)(f)$.
  Then there are $epsilon > 0$ and a subsequence $(f_(n_k))_k$ with
  $ abs(risk(L, P)(f_(n_k)) - risk(L, P)(f)) >= epsilon quad "for all" k in NN. $ <eq:loss-contradiction>
  Since $f_(n_k) -> f$ in $L^p (P_X)$ as well, @thm:app-convergence (vi) provides a further subsequence
  $g_j := f_(n_(k_j))$ and a function $G in cal(L)^p (P_X)$ such that $g_j -> f$ outside a $P_X$-null set $N$ and
  $abs(g_j) <= G$ on $X without N$ for all $j$. (Concretely, if $norm(g_j - f)_(L^p (P_X)) <= 2^(-j)$, one can take
  $G := abs(f) + sum_j abs(g_j - f)$; by Minkowski's inequality, $norm(G)_(L^p (P_X)) <= norm(f)_(L^p (P_X)) + 1$.) Thus, for $(x, y) in.not N times Y$,
  $ L(x, y, g_j (x)) <= b(x, y) + c G(x)^p quad "and" quad L(x, y, g_j (x)) -> L(x, y, f(x)), $
  the latter by continuity of $L$. The majorant is $P$-integrable, since
  $ integral (b(x, y) + c G(x)^p) dif P(x, y) = integral b dif P + c norm(G)_(L^p (P_X))^p < oo. $
  By dominated convergence, $risk(L, P)(g_j) -> risk(L, P)(f)$, which contradicts @eq:loss-contradiction.

  (iv) The proofs of (i)–(iii) use no property of $f(x)$ other than being a measurable function on the space
  carrying the distribution: replace $f(x)$ by $F(x, y)$, the null sets $N times Y$ by $P$-null sets
  $N subset.eq X times Y$, and $P_X$ by $P$. The statement of @lem:loss-classes holds for $F$ with the same
  (even simpler) proof.
]

#remark[
  + Part (iii) also holds for $p in (0, 1)$. Then $L^p (P_X)$ is a complete metric vector space with the
    metric $d_p (f, g) = integral abs(f - g)^p dif P_X$, but not a normed one if $P_X$ has no atoms
    (@sec:app-lp, @fig:loss-lp). The proof above works verbatim, because @thm:app-convergence (vi) holds
    for all $p in (0, oo)$; in the concrete construction of $G$, the subadditivity $(a + b)^p <= a^p + b^p$
    replaces Minkowski's inequality (@ex:loss-exercise-p-small).
  + The subsequence argument in (iii) is necessary because $L^p$-convergence does not imply almost sure
    convergence (@ex:loss-dominating-spaces (iii)). What we actually showed is that every subsequence has a
    further subsequence along which the risks converge to $risk(L, P)(f)$, which forces convergence of the
    whole sequence.
  + Being continuous, the risk is Borel measurable on $L^oo (P_X)$ and on $L^p (P_X)$
    (@rem:loss-measurability-lp).
] <rem:loss-continuity-remarks>

None of the hypotheses of @prop:loss-risk-continuity can be dropped.
- *Continuity of $L$:* the classification loss is a $P$-integrable Nemitski loss, but its risk is not
  continuous on $L^oo (P_X)$ (@ex:loss-01-not-lsc).
- *Integrability of $b$:* let $L$ be the least squares loss and $integral y^2 dif P = oo$. Since
  $(y - t)^2 >= y^2 \/ 2 - t^2$, we get $risk(L, P)(f) >= integral (y^2 \/ 2 - f(x)^2) dif P(x, y) = oo$ for
  every bounded $f$, so the risk is identically $+oo$ on $L^oo (P_X)$.
- *The order $p$ in (iii):* the least squares loss is of order $2$, and by @ex:loss-spike its risk is not
  continuous on $L^1 (P_X)$. The exponential loss is Nemitski but not of any order $p$, and its risk is
  not even finite on $L^p (P_X)$ (@ex:loss-exercise-exp).

In @sec:reg, the RKHS $H$ of a bounded measurable kernel embeds continuously into $L^oo (P_X)$
(@prop:rkhs-bounded), so part (ii) makes $f |-> risk(L, P)(f)$ continuous on $H$. This is one of the two
ingredients, besides convexity, of the existence theorem (@thm:reg-existence).

== Lipschitz continuous losses <sec:loss-lipschitz>

Continuity of the risk is qualitative. For error estimates we need quantitative statements: how much can the
risk change if $f$ changes by a small amount? The natural assumption is a Lipschitz condition on $L$ that is
*uniform* in $(x, y)$.

#definition(title: [Lipschitz losses])[
  A loss $L: X times Y times RR -> [0, oo)$ is called *locally Lipschitz continuous* if for every $r >= 0$
  $ abs(L)_(r, 1) := sup_((x, y) in X times Y) sup_(t, t' in [-r, r], t != t') abs(L(x, y, t) - L(x, y, t')) / abs(t - t') < oo $
  (with $abs(L)_(0, 1) := 0$, the supremum over the empty set).
  Then $abs(L)_(r, 1)$ is the smallest constant $C >= 0$ with
  $abs(L(x, y, t) - L(x, y, t')) <= C abs(t - t')$ for all $(x, y) in X times Y$ and $t, t' in [-r, r]$; it is
  called the *local Lipschitz constant* of $L$ on $[-r, r]$. The loss $L$ is called *Lipschitz continuous*
  if
  $ abs(L)_1 := sup_(r >= 0) abs(L)_(r, 1) < oo, $
  that is, if $abs(L(x, y, t) - L(x, y, t')) <= abs(L)_1 abs(t - t')$ for all $(x, y) in X times Y$ and
  $t, t' in RR$. In this case $abs(L)_1$ is the *Lipschitz constant* of $L$.
] <def:loss-lipschitz>

The function $r |-> abs(L)_(r,1)$ is non-decreasing (the supremum is taken over larger sets), so
$abs(L)_1 = lim_(r -> oo) abs(L)_(r, 1)$. For a function $g: I -> RR$ on an interval we similarly write
$abs(g)_1$ for its Lipschitz constant, and $abs(g|_([a, b]))_1$ for that of its restriction to $[a, b]$.
If $g$ is differentiable on $[a, b]$, then $abs(g|_([a,b]))_1 = sup_(s in [a, b]) abs(g'(s))$: the
inequality "$<=$" is the mean value theorem, and "$>=$" holds because each $g'(s)$ is a limit of difference
quotients of points in $[a, b]$.

#remark[
  Let $L$ be locally Lipschitz continuous. Then $L$ is continuous, and
  $ L(x, y, t) <= L(x, y, 0) + abs(L)_(abs(t), 1) abs(t) quad "for all" (x, y, t). $
  Since $h(s) := s abs(L)_(s, 1)$ is non-decreasing, $L$ is a Nemitski loss with $b(x, y) := L(x, y, 0)$; this
  $b$ is $P$-integrable if and only if $risk(L, P)(0) < oo$. If $L$ is Lipschitz continuous, it is of order $1$
  with $c := abs(L)_1$. Hence all results of @sec:loss-nemitski apply to locally Lipschitz losses
  with $risk(L, P)(0) < oo$.
] <rem:loss-lipschitz-nemitski>

#proposition[
  Let $L$ be a locally Lipschitz continuous loss and $P$ a distribution on $X times Y$.
  + Let $B >= 0$ and $f, g in meas(X)$ with $abs(f), abs(g) <= B$ $P_X$-almost surely. Then
    $risk(L, P)(f) < oo$ if and only if $risk(L, P)(g) < oo$, and in this case
    $ abs(risk(L, P)(f) - risk(L, P)(g)) <= abs(L)_(B, 1) norm(f - g)_(L^1 (P_X)). $
  + If $L$ is Lipschitz continuous and $f, g in meas(X)$ satisfy $risk(L, P)(g) < oo$ and
    $f - g in cal(L)^1 (P_X)$, then $risk(L, P)(f) < oo$ and
    $ abs(risk(L, P)(f) - risk(L, P)(g)) <= abs(L)_1 norm(f - g)_(L^1 (P_X)). $
    In particular, if $risk(L, P)(0) < oo$, then $risk(L, P)$ is finite and Lipschitz continuous with
    constant $abs(L)_1$ on $L^1 (P_X)$.
] <prop:loss-lipschitz-risk>

#proof[
  (i) By @lem:loss-classes we may modify $f$ and $g$ on a null set and assume $abs(f(x)), abs(g(x)) <= B$ for
  all $x$. Then, for all $(x, y)$,
  $ abs(L(x, y, f(x)) - L(x, y, g(x))) <= abs(L)_(B, 1) abs(f(x) - g(x)) <= 2 B abs(L)_(B, 1). $ <eq:loss-lipschitz-pointwise>
  Integrating $L(x, y, f(x)) <= L(x, y, g(x)) + 2 B abs(L)_(B, 1)$ gives
  $risk(L, P)(f) <= risk(L, P)(g) + 2 B abs(L)_(B,1)$, and by symmetry the two risks are finite or infinite
  simultaneously. If they are finite, both integrands are $P$-integrable, and
  $ abs(risk(L, P)(f) - risk(L, P)(g)) & <= integral abs(L(x, y, f(x)) - L(x, y, g(x))) dif P(x, y) \
    & <= abs(L)_(B, 1) integral abs(f(x) - g(x)) dif P(x, y) = abs(L)_(B, 1) norm(f - g)_(L^1 (P_X)), $
  where the last integral is computed with the marginal $P_X$, as the integrand depends only on $x$.

  (ii) Now @eq:loss-lipschitz-pointwise holds with $abs(L)_1$ in place of $abs(L)_(B, 1)$ for all $f, g$ (the
  second inequality there is not needed). Hence
  $L(x, y, f(x)) <= L(x, y, g(x)) + abs(L)_1 abs(f(x) - g(x))$, whose integral is finite, and the estimate
  follows as in (i). The last statement is the case $g = 0$ together with the estimate itself.
]

For Lipschitz losses the risk thus inherits the Lipschitz continuity of $L$, with respect to the weakest
reasonable norm, that of $L^1 (P_X)$. In @sec:stab-outlook this is combined with
$norm(f)_(L^1 (P_X)) <= norm(f)_oo <= abs(K)_oo norm(f)_H$ to turn stability of $f_(D,lambda)$ in the RKHS
norm into closeness of risks. The hinge loss and the logistic loss are Lipschitz continuous with constant
$1$; the least squares loss on $Y = {-1, 1}$ is only locally Lipschitz with $abs(L)_(r,1) = 2r + 2$ (see
@sec:loss-catalogue); and the least squares loss on an unbounded $Y$ is not even locally Lipschitz
(@rem:loss-distance-lipschitz).

== Differentiability of the risk <sec:loss-differentiability>

To *compute* a minimizer of a smooth function $F: RR^n -> RR$, the first thing one does is to set its
gradient to zero. We want to do the same for the regularized risk, which is a function on an
infinite-dimensional space. This requires a notion of derivative on normed spaces, and a rule for
computing the derivative of $f |-> risk(L, P)(f)$. The payoff, in @sec:reg, is an integral equation
@eq:reg-integral-equation[] characterizing the regularized minimizer $f_(P, lambda)$, and, for the empirical
measure, a finite system of equations for its coefficients.

A loss $L$ is called *differentiable* if $L(x, y, dot): RR -> [0, oo)$ is differentiable for every
$(x, y) in X times Y$. We then write
$ L'(x, y, t) := partial_t L(x, y, t) = lim_(s -> 0) (L(x, y, t + s) - L(x, y, t)) / s. $

#definition(title: [Fréchet and Gâteaux derivatives])[
  Let $V$ and $W$ be normed spaces, $U subset.eq V$ open, $F: U -> W$ and $v in U$. The map $F$ is
  *Fréchet differentiable at $v$* if there is a bounded linear operator $A: V -> W$ such that
  $ lim_(h -> 0, h != 0) norm(F(v + h) - F(v) - A h)_W / norm(h)_V = 0. $
  Then $F'(v) := A$ is the *Fréchet derivative* of $F$ at $v$. $F$ is *Fréchet differentiable* if it is
  Fréchet differentiable at every point of $U$. The map $F$ is *Gâteaux differentiable at $v$* if there is a
  bounded linear operator $A: V -> W$ with
  $ lim_(s -> 0, s != 0) (F(v + s h) - F(v)) / s = A h quad "for every" h in V. $
] <def:loss-frechet>

The Fréchet derivative is unique: if $A_1$ and $A_2$ both satisfy the definition, put
$epsilon_i (k) := norm(F(v + k) - F(v) - A_i k)_W \/ norm(k)_V$; then for fixed $h != 0$ and $s -> 0^+$,
$ norm((A_1 - A_2) h)_W = 1/s norm((A_1 - A_2)(s h))_W <= norm(h)_V (epsilon_1 (s h) + epsilon_2 (s h)) -> 0. $ Fréchet differentiability at $v$
implies continuity at $v$ and Gâteaux differentiability with the same derivative (replace $h$ by $s h$
in the definition and let $s -> 0$). The converse fails already on $RR^2$: the function $F(x_1, x_2) = 1$ if
$x_2 = x_1^2$ and $x_1 != 0$, and $F(x_1, x_2) = 0$ otherwise, has $F(s h) = 0$ for all $h in RR^2$ and all
sufficiently small $s$ (a line through the origin meets the parabola in at most one point besides $0$), so
it is Gâteaux differentiable at $0$ with derivative $0$; but it is not continuous at $0$, since
$F(t, t^2) = 1$ for $t != 0$, hence not Fréchet differentiable there. Fréchet differentiability is the
notion for which the chain rule holds in general; we prove the case we need in
@prop:loss-frechet (iv).

#proposition(title: [Fréchet derivative of the risk])[
  Let $P$ be a distribution on $X times Y$ and let $L$ be a differentiable, $P$-integrable Nemitski loss.
  Assume that $abs(L')$ is a $P$-integrable Nemitski loss as well, that is, there are a measurable
  $b': X times Y -> [0, oo)$ with $integral b' dif P < oo$ and a non-decreasing $h': [0, oo) -> [0, oo)$ with
  $ abs(L'(x, y, t)) <= b'(x, y) + h'(abs(t)) quad "for all" (x, y, t) in X times Y times RR. $
  Then the following hold.
  + $L': X times Y times RR -> RR$ is measurable.
  + $risk(L, P): L^oo (P_X) -> [0, oo)$ is Fréchet differentiable. Its derivative at $f in L^oo (P_X)$ is
    the bounded linear functional $risk(L, P)'(f) in (L^oo (P_X))'$ given by
    $ risk(L, P)'(f) g = integral_(X times Y) g(x) L'(x, y, f(x)) dif P(x, y), quad g in L^oo (P_X). $ <eq:loss-frechet-derivative>
  + For every representative of $f$, the function $x |-> integral_Y L'(x, y, f(x)) dif P(y | x)$ is defined
    $P_X$-almost everywhere and defines an element $ell_f$ of $L^1 (P_X)$. It represents the derivative:
    $risk(L, P)'(f) g = integral_X g ell_f dif P_X$ for all $g in L^oo (P_X)$, and
    $norm(risk(L, P)'(f))_((L^oo (P_X))') = norm(ell_f)_(L^1 (P_X))$.
  + (Chain rule.) If $V$ is a normed space and $iota: V -> L^oo (P_X)$ is a bounded linear operator, then
    $risk(L, P) compose iota: V -> [0, oo)$ is Fréchet differentiable with
    $(risk(L, P) compose iota)'(v) = risk(L, P)'(iota v) compose iota$, that is,
    $ (risk(L, P) compose iota)'(v) w = integral_(X times Y) (iota w)(x) thin L'(x, y, (iota v)(x)) dif P(x, y), quad v, w in V. $
] <prop:loss-frechet>

#proof[
  (i) For every $n in NN$ the function $(x, y, t) |-> n (L(x, y, t + 1\/n) - L(x, y, t))$ is measurable, as
  it is built from $L$ and the measurable map $(x, y, t) |-> (x, y, t + 1\/n)$. By differentiability these
  functions converge pointwise to $L'$ as $n -> oo$, and pointwise limits of measurable functions are
  measurable.

  (ii) *The candidate derivative.* Fix $f in L^oo (P_X)$ and a representative with
  $abs(f(x)) <= norm(f)_(L^oo (P_X)) =: B$ for all $x in X$. For $g in L^oo (P_X)$ we have, $P$-almost
  surely,
  $ abs(g(x) L'(x, y, f(x))) <= norm(g)_(L^oo (P_X)) (b'(x, y) + h'(B)). $
  Hence the integral in @eq:loss-frechet-derivative exists, it does not depend on the representative of $g$
  (@lem:loss-classes applies verbatim), it is linear in $g$, and
  $abs(risk(L, P)'(f) g) <= (norm(b')_(L^1 (P)) + h'(B)) norm(g)_(L^oo (P_X))$. So $risk(L, P)'(f)$ is a bounded
  linear functional on $L^oo (P_X)$.

  *The remainder.* Since $L^oo (P_X)$ is a metric space, it suffices to show that
  $ Q_n := abs(risk(L, P)(f + g_n) - risk(L, P)(f) - risk(L, P)'(f) g_n) / norm(g_n)_(L^oo (P_X)) --> 0 $
  for every sequence $(g_n) subset.eq L^oo (P_X) without {0}$ with $norm(g_n)_(L^oo (P_X)) -> 0$. Discarding
  finitely many terms we may assume $norm(g_n)_(L^oo (P_X)) <= 1$, and we choose representatives with
  $abs(g_n (x)) <= norm(g_n)_(L^oo (P_X))$ for all $x$. All risks involved are finite by
  @rem:loss-nemitski-basic (i), so by linearity of the integral $Q_n <= integral G_n dif P$ with
  $ G_n (x, y) := abs(L(x, y, f(x) + g_n (x)) - L(x, y, f(x)) - g_n (x) L'(x, y, f(x))) / norm(g_n)_(L^oo (P_X)), $
  a nonnegative measurable function. We show $integral G_n dif P -> 0$ by dominated convergence.

  *Pointwise convergence.* Fix $(x, y)$. If $g_n (x) = 0$, then $G_n (x, y) = 0$. Otherwise
  $ G_n (x, y) = abs(g_n (x)) / norm(g_n)_(L^oo (P_X)) abs(Delta_n (x, y) - L'(x, y, f(x))) <= abs(Delta_n (x, y) - L'(x, y, f(x))), $
  where $Delta_n (x, y) := (L(x, y, f(x) + g_n (x)) - L(x, y, f(x))) \/ g_n (x)$ is a difference quotient
  of $L(x, y, dot)$ at $f(x)$ with increment $g_n (x)$. Since $abs(g_n (x)) <= norm(g_n)_(L^oo (P_X)) -> 0$ and
  $L(x, y, dot)$ is differentiable at $f(x)$, given $epsilon > 0$ there is $n_0$ such that for $n >= n_0$
  either $g_n (x) = 0$ or $abs(Delta_n (x, y) - L'(x, y, f(x))) < epsilon$. Hence $G_n (x, y) -> 0$ for
  every $(x, y) in X times Y$.

  *Majorant.* If $g_n (x) != 0$, the mean value theorem, applied to the differentiable function
  $L(x, y, dot)$, gives a $xi$ between $f(x)$ and $f(x) + g_n (x)$ with $Delta_n (x, y) = L'(x, y, xi)$.
  (We do not need $xi$ to depend measurably on $(x, y)$; it is only used to bound the measurable function
  $G_n$.) Since $abs(xi) <= abs(f(x)) + abs(g_n (x)) <= B + 1$ and $h'$ is non-decreasing,
  $ G_n (x, y) <= abs(L'(x, y, xi)) + abs(L'(x, y, f(x))) <= 2 b'(x, y) + 2 h'(B + 1), $
  which trivially also holds if $g_n (x) = 0$. The right-hand side is $P$-integrable. By dominated
  convergence (@thm:app-convergence), $integral G_n dif P -> 0$, hence $Q_n -> 0$.

  (iii) Put $u(x, y) := L'(x, y, f(x))$. By the bound above, $abs(u) <= b' + h'(B)$ is $P$-integrable. By
  the disintegration formula of @lem:learn-regular-conditional, applied to the nonnegative functions
  $u^+$, $u^-$ and $abs(u)$, the function $x |-> integral_Y abs(u(x, y)) dif P(y | x)$ is measurable with
  integral $integral abs(u) dif P < oo$, so it is finite outside a $P_X$-null set $N$. On $X without N$ define
  $ell_f (x) := integral_Y u(x, y) dif P(y|x) = integral_Y u^+ (x, y) dif P(y|x) - integral_Y u^- (x, y) dif P(y|x)$,
  and $ell_f := 0$ on $N$. Then $ell_f$ is measurable with $norm(ell_f)_(L^1 (P_X)) <= integral abs(u) dif P < oo$.
  For $g in L^oo (P_X)$, applying the disintegration formula to $(g u)^+$ and $(g u)^-$ gives
  $ risk(L, P)'(f) g = integral_X integral_Y g(x) u(x, y) dif P(y | x) dif P_X (x) = integral_X g(x) ell_f (x) dif P_X (x). $
  Consequently $abs(risk(L, P)'(f) g) <= norm(g)_(L^oo (P_X)) norm(ell_f)_(L^1 (P_X))$, and choosing
  $g := sign compose ell_f$ (which has $norm(g)_(L^oo (P_X)) <= 1$) gives
  $risk(L, P)'(f) g = norm(ell_f)_(L^1 (P_X))$. This proves the norm identity.

  (iv) Fix $v in V$. By (ii), for every $k in L^oo (P_X) without {0}$,
  $ abs(risk(L, P)(iota v + k) - risk(L, P)(iota v) - risk(L, P)'(iota v) k) = epsilon(k) norm(k)_(L^oo (P_X)) $
  with $epsilon(k) -> 0$ as $k -> 0$; put $epsilon(0) := 0$. Applying this with $k = iota w$, $w in V without {0}$,
  and using $norm(iota w)_(L^oo (P_X)) <= norm(iota) norm(w)_V$, we get
  $ abs(risk(L, P)(iota(v + w)) - risk(L, P)(iota v) - (risk(L, P)'(iota v) compose iota) w) / norm(w)_V <= norm(iota) thin epsilon(iota w) -> 0 quad (w -> 0), $
  because $iota w -> 0$ as $w -> 0$. Since $risk(L, P)'(iota v) compose iota$ is bounded and linear, it is the
  Fréchet derivative of $risk(L, P) compose iota$ at $v$.
]

#example[
  Let $L(y, t) = (y - t)^2$ be the least squares loss and assume $integral y^2 dif P(x,y) < oo$. Then
  $L'(y, t) = 2(t - y)$ and $abs(L'(y, t)) <= 2 abs(y) + 2 abs(t)$ with $integral abs(y) dif P < oo$, so
  @prop:loss-frechet applies. With $f_P (x) := integral_Y y dif P(y|x)$ the conditional mean of
  @ex:learn-least-squares, part (iii) gives $ell_f = 2 (f - f_P)$, that is,
  $ risk(L, P)'(f) g = 2 integral_X g(x) (f(x) - f_P (x)) dif P_X (x). $
  This is consistent with the decomposition @eq:learn-ls-decomposition[],
  $risk(L, P)(f) = norm(f - f_P)_(L^2 (P_X))^2 + sigma_P^2$: the derivative vanishes at $f in L^oo (P_X)$
  if and only if $f = f_P$ almost surely, so, when $f_P$ is bounded, the Bayes decision function is exactly
  the critical point of the risk.
] <ex:loss-ls-derivative>

#remark[
  + The derivative $risk(L, P)'(f)$ is an element of the dual $(L^oo (P_X))'$, a large and unwieldy space
    (unless $L^oo (P_X)$ is finite-dimensional, it is strictly larger than $L^1 (P_X)$). Part (iii) shows that the derivative of a risk is nevertheless always given by
    an $L^1 (P_X)$-function. In @sec:reg, the derivative is composed with the embedding $iota: H -> L^oo (P_X)$
    of an RKHS with bounded kernel (@prop:rkhs-bounded); by (iv) and the reproducing property,
    $(risk(L, P) compose iota)'(f_0) f = integral f(x) L'(x, y, f_0 (x)) dif P(x, y)$ becomes an inner product
    in $H$, which leads to the integral equation @eq:reg-integral-equation[].
  + The choice of $L^oo (P_X)$ is what makes the simple proof above work: it provides the uniform bound
    $abs(xi) <= B + 1$ and thus a majorant. On $L^p (P_X)$ with $p < oo$, perturbations $g_n$ of small norm
    may be large on small sets, and differentiability requires additional growth conditions on $L'$. We do
    not need this.
  + Many important losses, such as the hinge loss, the absolute loss and the $epsilon$-insensitive loss, are
    convex but not differentiable. For them the derivative is replaced by the *subdifferential*
    (@def:reg-subdifferential), which is developed in @sec:reg.
] <rem:loss-frechet-remarks>

== Distance-based losses <sec:loss-distance>

In regression, the output space is typically $Y = RR$ or an interval, and the loss usually depends only on the
*residual* $r = y - t$: overestimating by $1$ at $y = 0$ costs as much as overestimating by $1$ at
$y = 1000$. Such losses are called distance-based. Their structure lets us replace assumptions on the
three-variable function $L$ by assumptions on a function of one variable, and it links the finiteness of the
risk to moments of the output distribution.

#definition(title: [Distance-based losses])[
  A supervised loss $L: Y times RR -> [0, oo)$ is called *distance-based* if there is a measurable function
  $psi: RR -> [0, oo)$ with $psi(0) = 0$ such that
  $ L(y, t) = psi(y - t) quad "for all" y in Y, t in RR. $
  The function $psi$ is called the *representing function* of $L$. The loss $L$ is called *symmetric* if
  $psi(r) = psi(-r)$ for all $r in RR$.
] <def:loss-distance>

The requirement $psi(0) = 0$ says that a perfect prediction costs nothing. Conversely, for every measurable
$psi >= 0$ the function $(y, t) |-> psi(y - t)$ is measurable, so it is a loss. The representing function is
uniquely determined by $L$, however small $Y$ is: for any fixed $y_0 in Y$, the residual $y_0 - t$ runs
through all of $RR$ as $t$ does, so $psi(r) = L(y_0, y_0 - r)$ for all $r in RR$.

#lemma[
  Let $L$ be a distance-based loss with representing function $psi$. Then:
  + $L$ is convex, strictly convex, or continuous if and only if $psi$ is.
  + $L$ is Lipschitz continuous if and only if $psi$ is, and then $abs(L)_1 = abs(psi)_1$.
] <lem:loss-distance-basic>

#proof[
  For every $y in Y$, the map $t |-> L(y, t) = psi(y - t)$ is the composition of $psi$ with the affine
  bijection $t |-> y - t$ of $RR$, and, for a fixed $y_0 in Y$, $psi(r) = L(y_0, y_0 - r)$ is the
  composition of $L(y_0, dot)$ with the affine bijection $r |-> y_0 - r$. Convexity, strict convexity and continuity are preserved under composition with affine
  bijections of $RR$, which gives (i). For (ii), $abs(L(y, t) - L(y, t')) = abs(psi(y - t) - psi(y - t'))$
  and $abs((y - t) - (y - t')) = abs(t - t')$; as $(t, t')$ ranges over $RR^2$ with $t != t'$, so does
  $(y - t, y - t')$ (for each fixed $y$). Hence the supremum of the difference quotients of $L$ over
  $y in Y$, $t != t'$, equals that of $psi$.
]

#remark[
  For *local* Lipschitz continuity the analogous statement is false when $Y$ is unbounded. For the least
  squares loss, $psi(r) = r^2$ is locally Lipschitz, but for $t != t'$
  $ sup_(y in Y) abs((y - t)^2 - (y - t')^2) / abs(t - t') = sup_(y in Y) abs(2 y - t - t') = oo $
  if $Y$ is unbounded, because $(y - t)^2 - (y - t')^2 = (t' - t)(2y - t - t')$. In general:
  + If $Y subset.eq [-M, M]$ is bounded and $psi$ is locally Lipschitz, then $L$ is locally Lipschitz with
    $abs(L)_(r, 1) <= abs(psi|_([-M - r, M + r]))_1$, since $y - t in [-M - r, M + r]$ for
    $y in Y$, $t in [-r, r]$.
  + If $Y = RR$, then $L$ is locally Lipschitz if and only if $psi$ is Lipschitz. If $psi$ is Lipschitz,
    so is $L$ by @lem:loss-distance-basic (ii). Conversely, let $C := abs(L)_(1, 1) < oo$. Any $s, s' in RR$ with
    $abs(s - s') <= 2$ can be written as $s = y - t$, $s' = y - t'$ with $y := (s + s')\/2$ and
    $t, t' in [-1, 1]$, so $abs(psi(s) - psi(s')) <= C abs(s - s')$. For arbitrary $s < s'$ we subdivide
    $s = s_0 < s_1 < dots.c < s_m = s'$ with $s_(k+1) - s_k <= 2$ and sum up:
    $ abs(psi(s') - psi(s)) <= C sum_(k=0)^(m-1) (s_(k+1) - s_k) = C abs(s' - s). $
  So for regression with unbounded outputs, local Lipschitz arguments as in @prop:loss-lipschitz-risk (i) are
  available only for Lipschitz $psi$. For losses such as least squares, the growth conditions below take
  their place.
] <rem:loss-distance-lipschitz>

=== Growth of distance-based losses

The natural size scale of a distance-based loss is its growth as $abs(r) -> oo$: the least squares loss grows
like $r^2$, the absolute loss like $abs(r)$. The growth type determines which moments of $P$ are needed for
finite risks and in which $L^p$-space the risk lives.

#definition(title: [Growth type])[
  Let $L$ be a distance-based loss with representing function $psi$ and let $p in (0, oo)$. Then $L$ is
  called
  - *$p$-upper bounded* if there is a constant $c > 0$ with $psi(r) <= c (abs(r)^p + 1)$ for all $r in RR$;
  - *$p$-lower bounded* if there is a constant $c > 0$ with $psi(r) >= c abs(r)^p - 1$ for all $r in RR$;
  - *of growth type $p$* if it is both $p$-upper bounded and $p$-lower bounded.
] <def:loss-growth>

#remark[
  One might be tempted to require $psi(r) >= c (abs(r)^p - 1)$ for lower boundedness instead, so that the
  constant $c$ multiplies the whole bracket as in the upper bound. That condition is strictly stronger. It
  implies ours with the constant $min{c, 1}$: for $c <= 1$ we have $c(abs(r)^p - 1) >= c abs(r)^p - 1$, and for
  $c > 1$ we have $psi(r) >= abs(r)^p - 1$ both where $abs(r) >= 1$ (as $c(abs(r)^p - 1) >= abs(r)^p - 1 >= 0$ there)
  and where $abs(r) < 1$ (as $psi >= 0 > abs(r)^p - 1$ there). But it excludes, for example, the
  $epsilon$-insensitive loss $psi(r) = max{0, abs(r) - epsilon}$ with $epsilon > 1$: since $psi(r) = 0$ for
  $abs(r) <= epsilon$, the inequality $0 >= c (abs(r) - 1)$ fails for $1 < abs(r) <= epsilon$, whatever
  $c > 0$ is. As this $psi$ is convex with $psi(r) -> oo$, the stronger condition would make
  @lem:loss-growth-convex (i) below false. All results below that use lower bounds
  (@lem:loss-inner-risk (ii), (iii) and @prop:loss-distance-risk-bounds (iii)) only need
  $abs(r)^p <= (psi(r) + 1)\/c$, which is exactly our condition.
] <rem:loss-growth-definition>

We will frequently use the elementary inequality
$ abs(a + b)^p <= c_p (abs(a)^p + abs(b)^p), quad a, b in RR, quad c_p := max{1, 2^(p - 1)}, $ <eq:loss-cp>
which follows for $p >= 1$ from convexity of $s |-> abs(s)^p$ (apply it to $(a + b)\/2$), and for
$p in (0, 1)$ from the subadditivity $(u + v)^p <= u^p + v^p$ of $u |-> u^p$ on $[0, oo)$ (a concave
function vanishing at $0$). Convex representing functions are well behaved, as the next lemma shows. It is
based on the following facts about convex functions $g: RR -> RR$, proved in @lem:app-convex-lipschitz:
$g$ is locally Lipschitz with
$ abs(g|_([-r, r]))_1 <= 2/r norm(g|_([-2r, 2r]))_oo quad "for all" r > 0, $ <eq:loss-convex-lipschitz>
and if $g(0) = 0$, then $s |-> g(s)\/s$ is non-decreasing on $(0, oo)$.

#lemma[
  Let $L$ be a distance-based loss with representing function $psi$.
  + If $psi$ is convex and $lim_(abs(r) -> oo) psi(r) = oo$, then $L$ is $1$-lower bounded.
  + If $psi$ is Lipschitz continuous, then $L$ is $1$-upper bounded.
  + If $psi$ is convex, then for every $r > 0$
    $ abs(psi|_([-r, r]))_1 <= 2/r norm(psi|_([-2r, 2r]))_oo <= 4 abs(psi|_([-2r, 2r]))_1. $
  + If $psi$ is convex and $L$ is $p$-upper bounded for some $p >= 1$, then there is a constant
    $c_(L, p) > 0$ such that, with the convention $0^0 := 1$,
    $ abs(psi(r) - psi(r')) <= c_(L, p) (abs(r)^(p - 1) + abs(r')^(p - 1) + 1) abs(r - r') quad "for all" r, r' in RR. $
    In particular, if $psi$ is convex and $1$-upper bounded, then $psi$ is Lipschitz continuous.
] <lem:loss-growth-convex>

#proof[
  (i) Choose $R > 0$ with $psi(r) >= 1$ for $abs(r) >= R$. For $r >= R$, convexity and $psi(0) = 0$ give
  $psi(R) = psi((R\/r) r + (1 - R\/r) 0) <= (R\/r) psi(r)$, hence $psi(r) >= (r\/R) psi(R) >= r \/ R$. In the
  same way $psi(r) >= abs(r)\/R$ for $r <= -R$. For $abs(r) < R$ we have $psi(r) >= 0 > abs(r)\/R - 1$. Hence
  $psi(r) >= abs(r)\/R - 1$ for all $r$, and $L$ is $1$-lower bounded with $c = 1\/R$.

  (ii) Since $psi(0) = 0$, $psi(r) = abs(psi(r) - psi(0)) <= abs(psi)_1 abs(r) <= c (abs(r) + 1)$ with
  $c := max{abs(psi)_1, 1}$.

  (iii) The first inequality is @eq:loss-convex-lipschitz. For the second, $psi(0) = 0$ gives, for
  $abs(s) <= 2r$, $abs(psi(s)) = abs(psi(s) - psi(0)) <= abs(psi|_([-2r, 2r]))_1 abs(s) <= 2 r abs(psi|_([-2r, 2r]))_1$,
  so $2/r norm(psi|_([-2r, 2r]))_oo <= 4 abs(psi|_([-2r, 2r]))_1$.

  (iv) Let $c > 0$ be such that $psi(r) <= c(abs(r)^p + 1)$, and let $r, r' in RR$, $s := max{abs(r), abs(r')}$.
  If $s = 0$ there is nothing to show. If $s >= 1$, then by (iii)
  $ abs(psi|_([-s, s]))_1 <= 2/s c ((2s)^p + 1) = c thin 2^(p + 1) s^(p - 1) + (2c)/s <= 2 c (2^p + 1)(s^(p - 1) + 1). $
  If $0 < s < 1$, then by (iii) with $r = 1$,
  $abs(psi|_([-s, s]))_1 <= abs(psi|_([-1, 1]))_1 <= 2 norm(psi|_([-2, 2]))_oo <= 2 c (2^p + 1)$. In both cases
  $abs(psi|_([-s, s]))_1 <= 2c (2^p + 1)(s^(p-1) + 1)$. Since $p - 1 >= 0$ and $s in {abs(r), abs(r')}$, we have
  $s^(p - 1) <= abs(r)^(p - 1) + abs(r')^(p - 1)$. As $r, r' in [-s, s]$, we obtain the claim with
  $c_(L, p) := 2c(2^p + 1)$. For $p = 1$ the estimate reads $abs(psi(r) - psi(r')) <= 3 c_(L, 1) abs(r - r')$.
]

#remark[
  For convex losses only $p >= 1$ is relevant: if $psi$ is convex and $p$-upper bounded with $p < 1$, then
  $psi equiv 0$. Indeed, $psi(r)\/r$ is non-decreasing on $(0, oo)$ and tends to $0$ as $r -> oo$ (because
  $psi(r) <= c(r^p + 1)$), so $psi(r) \/ r <= 0$, i.e. $psi(r) <= 0$, for all $r > 0$; the same argument
  applies to $r |-> psi(-r)$. Since $psi >= 0$, $psi equiv 0$.
] <rem:loss-convex-p-small>

=== Moments and risk bounds

For a $p$-upper bounded loss the risk of $f = 0$ is at most $c(integral abs(y)^p dif P + 1)$. The
$p$-th moment of the output therefore enters naturally.

#definition(title: [Moments])[
  Let $Q$ be a distribution on $RR$ and $p in (0, oo)$. The *$p$-th moment* of $Q$ is
  $ abs(Q)_p := (integral_RR abs(y)^p dif Q(y))^(1\/p) in [0, oo], $
  and $abs(Q)_oo := sup{abs(y) : y in supp Q}$. For a distribution $P$ on $X times Y$ we define
  $ abs(P)_p := (integral_(X times Y) abs(y)^p dif P(x, y))^(1\/p), quad p in (0, oo), $
  and $abs(P)_oo := inf{M >= 0 : abs(y) <= M "for" P"-almost all" (x, y)}$ (with $inf emptyset = oo$).
] <def:loss-moments>

Some remarks on these quantities.
- The support $supp Q$ is the smallest closed set of full measure (it exists since $RR$ is second
  countable), so $abs(y) <= abs(Q)_oo$ for $Q$-almost all $y$, and $abs(Q)_oo < oo$ if and only if $supp Q$ is
  bounded, i.e. compact. For finite $p$, however, $abs(Q)_p < oo$ does *not* require bounded support: the
  standard normal distribution has finite moments of all orders.
- For $0 < q <= p <= oo$ we have $abs(Q)_q <= abs(Q)_p$, by Jensen's inequality for the concave function
  $u |-> u^(q\/p)$ if $p < oo$, and because $abs(y) <= abs(Q)_oo$ almost surely if $p = oo$. The same holds
  for $abs(P)_p$.
- By the disintegration formula (@lem:learn-regular-conditional),
  $abs(P)_p^p = integral_X abs(P(dot | x))_p^p dif P_X (x)$ for $p in (0, oo)$. Similarly $abs(P)_oo$ is the
  essential supremum of $x |-> abs(P(dot | x))_oo$ with respect to $P_X$ (@ex:loss-exercise-moments).

It is instructive to look first at a single conditional distribution. For a supervised loss $L$ and a
distribution $Q$ on $Y$, the *inner risk* is
$ I_(L, Q) (t) := integral_Y L(y, t) dif Q(y) in [0, oo], quad t in RR, quad I^*_(L, Q) := inf_(t in RR) I_(L, Q) (t). $
For $Q = P(dot | x)$ this is the inner risk of @def:learn-inner-risk at the input $x$:
$cal(C)_(L, P) (x, t) = I_(L, P(dot | x)) (t)$. Here we emphasize the distribution $Q$ rather than the input
$x$, because the estimates below hold for every $Q$ with constants independent of $Q$. By
@lem:learn-inner-risk, $risk(L, P)(f) = integral_X I_(L, P(dot | x)) (f(x)) dif P_X (x)$: the risk averages
the inner risks of the conditional distributions, and minimizing $t |-> I_(L, P(dot|x)) (t)$ separately for
each $x$ is how Bayes decision functions such as the conditional mean in @ex:learn-least-squares are found.

#lemma[
  Let $L$ be a distance-based loss, $p in (0, oo)$, and $Q$ a distribution on $Y$.
  + If $L$ is $p$-upper bounded, there is a constant $C_(L, p) > 0$, independent of $Q$, with
    $I_(L, Q) (t) <= C_(L, p) (abs(Q)_p^p + abs(t)^p + 1)$ for all $t in RR$.
  + If $L$ is $p$-lower bounded, there is a constant $C_(L, p) > 0$, independent of $Q$, with
    $ abs(Q)_p^p <= C_(L, p) (I_(L, Q) (t) + abs(t)^p + 1) quad "and" quad abs(t)^p <= C_(L, p) (I_(L, Q) (t) + abs(Q)_p^p + 1) quad "for all" t in RR. $
  + If $L$ is of growth type $p$, then $I^*_(L, Q) < oo$ if and only if $abs(Q)_p < oo$. In this case
    $I_(L, Q) (t) < oo$ for all $t in RR$, and $I_(L, Q) (t) -> oo$ as $abs(t) -> oo$.
] <lem:loss-inner-risk>

#proof[
  (i) Let $psi(r) <= c(abs(r)^p + 1)$. By @eq:loss-cp, $psi(y - t) <= c c_p (abs(y)^p + abs(t)^p) + c$, and
  integrating with respect to $Q$ gives the claim with $C_(L, p) := c c_p$ (recall $c_p >= 1$).

  (ii) Let $psi(r) >= c abs(r)^p - 1$, i.e. $abs(r)^p <= (psi(r) + 1)\/c$. By @eq:loss-cp,
  $ abs(y)^p <= c_p (abs(y - t)^p + abs(t)^p) <= c_p / c (psi(y - t) + 1) + c_p abs(t)^p, $
  and integrating over $y$ gives the first inequality with $C_(L, p) := c_p max{1, 1\/c}$. The second one
  follows in the same way from $abs(t)^p <= c_p (abs(t - y)^p + abs(y)^p)$. Both computations are valid in
  $[0, oo]$.

  (iii) If $abs(Q)_p < oo$, then $I_(L, Q) (t) < oo$ for every $t$ by (i), so $I^*_(L, Q) < oo$. Conversely,
  if $I^*_(L, Q) < oo$, then $I_(L, Q) (t) < oo$ for some $t in RR$, and the first inequality of (ii) shows
  $abs(Q)_p < oo$. Finally, the second inequality of (ii) gives
  $I_(L, Q) (t) >= abs(t)^p \/ C_(L, p) - abs(Q)_p^p - 1 -> oo$ as $abs(t) -> oo$.
]

Integrating these pointwise statements over $x$ yields bounds for the risk. Part (ii) of the next
proposition is the quantitative, $L^p$-version of @prop:loss-lipschitz-risk for losses that are not
Lipschitz, such as least squares.

#proposition[
  Let $L$ be a distance-based loss with representing function $psi$, $P$ a distribution on $X times Y$,
  and $p in (0, oo)$. We use the conventions $a^0 := 1$ for $a in [0, oo]$ and $0 dot oo := 0$.
  + If $L$ is $p$-upper bounded, there is a constant $c_(L, p) > 0$, independent of $P$, such that
    $ risk(L, P)(f) <= c_(L, p) (abs(P)_p^p + norm(f)_(L^p (P_X))^p + 1) quad "for all" f in meas(X). $
    If moreover $abs(P)_p < oo$, then $L$ is a $P$-integrable Nemitski loss of order $p$, and
    $risk(L, P)$ is finite on $L^p (P_X)$; if in addition $psi$ is continuous and $p >= 1$, then
    $risk(L, P): L^p (P_X) -> [0, oo)$ is continuous.
  + Let $L$ be convex and $p$-upper bounded for some $p >= 1$. Let $q in [p - 1, oo]$ with $q > 0$, and
    define $s in [1, oo]$ by $s := q \/ (q - p + 1)$, with $s := oo$ if $q = p - 1$ and $s := 1$ if $q = oo$.
    Then there is a constant $c_(L, p) > 0$, independent of $P$ and $q$, such that
    $ abs(risk(L, P)(f) - risk(L, P)(g)) <= c_(L, p) (abs(P)_q^(p - 1) + norm(f)_(L^q (P_X))^(p - 1) + norm(g)_(L^q (P_X))^(p - 1) + 1) norm(f - g)_(L^s (P_X)) $
    for all $f, g in meas(X)$ with $risk(L, P)(f) < oo$ and $risk(L, P)(g) < oo$.
  + If $L$ is $p$-lower bounded, there is a constant $c_(L, p) > 0$, independent of $P$, such that for all
    $f in meas(X)$
    $ abs(P)_p^p <= c_(L, p) (risk(L, P)(f) + norm(f)_(L^p (P_X))^p + 1) quad "and" quad norm(f)_(L^p (P_X))^p <= c_(L, p) (risk(L, P)(f) + abs(P)_p^p + 1). $
] <prop:loss-distance-risk-bounds>

#proof[
  (i) Let $psi(r) <= c(abs(r)^p + 1)$. As in @lem:loss-inner-risk (i),
  $ L(y, t) = psi(y - t) <= c thin c_p abs(y)^p + c + c thin c_p abs(t)^p. $ <eq:loss-upper-nemitski>
  Putting $t = f(x)$ and integrating gives the risk bound with $c_(L, p) := c thin c_p$. If $abs(P)_p < oo$, then
  @eq:loss-upper-nemitski shows that $L$ is a Nemitski loss of order $p$ with
  $b(x, y) := c thin c_p abs(y)^p + c$, and $integral b dif P = c thin c_p abs(P)_p^p + c < oo$. Finiteness on
  $L^p (P_X)$ follows from the risk bound (and @lem:loss-classes), and continuity from
  @prop:loss-risk-continuity (iii), since $L$ is continuous if $psi$ is (@lem:loss-distance-basic).

  (ii) By @lem:loss-growth-convex (iv) there is $c' > 0$ with
  $abs(psi(r) - psi(r')) <= c' (abs(r)^(p-1) + abs(r')^(p-1) + 1) abs(r - r')$. We apply this with
  $r = y - f(x)$ and $r' = y - g(x)$. By @eq:loss-cp with exponent $p - 1$ (for $p = 1$ it holds trivially
  with $c_0 = 1$ and our convention), $abs(y - f(x))^(p - 1) <= c_(p-1) (abs(y)^(p-1) + abs(f(x))^(p-1))$, and
  similarly for $g$. Since $c_(p-1) >= 1$, we obtain for all $(x, y)$
  $ abs(L(y, f(x)) - L(y, g(x))) <= c' c_(p - 1) thin u(x, y) thin abs(f(x) - g(x)), $
  where $u(x, y) := 2 abs(y)^(p - 1) + abs(f(x))^(p - 1) + abs(g(x))^(p - 1) + 1$.
  Since both risks are finite, both integrands are $P$-integrable, and
  $ abs(risk(L, P)(f) - risk(L, P)(g)) <= c' c_(p-1) integral_(X times Y) u(x, y) abs(f(x) - g(x)) dif P(x, y). $
  Let $q' := q \/ (p - 1) in [1, oo]$ (with $q' := oo$ if $p = 1$ or $q = oo$). Then $1\/q' + 1\/s = 1$: for
  $p > 1$ and $q < oo$ this is $(p - 1)\/q + (q - p + 1)\/q = 1$, and in the remaining cases $s = 1$ and
  $q' = oo$. By Hölder's inequality on $(X times Y, P)$,
  $integral u abs(f - g) dif P <= norm(u)_(L^(q') (P)) norm(f - g)_(L^s (P_X))$, where we used that the
  $L^s (P)$-norm of $(x, y) |-> f(x) - g(x)$ equals $norm(f - g)_(L^s (P_X))$. By Minkowski's inequality in
  $L^(q') (P)$ (valid since $q' >= 1$),
  $ norm(u)_(L^(q') (P)) & <= 2 norm(abs(y)^(p-1))_(L^(q') (P)) + norm(abs(f)^(p-1))_(L^(q') (P_X)) + norm(abs(g)^(p-1))_(L^(q') (P_X)) + 1 \
    & = 2 abs(P)_q^(p - 1) + norm(f)_(L^q (P_X))^(p-1) + norm(g)_(L^q (P_X))^(p-1) + 1, $
  because $(integral abs(y)^((p-1) q') dif P)^(1\/q') = (integral abs(y)^q dif P)^((p-1)\/q)$ for $p > 1$ and
  $q < oo$, with the obvious modifications for $q = oo$ (essential suprema) and for $p = 1$ (all terms
  equal $1$). This proves (ii) with $c_(L, p) := 2 c' c_(p - 1)$.

  (iii) Integrate the pointwise inequalities from the proof of @lem:loss-inner-risk (ii) with $t = f(x)$:
  $ abs(y)^p <= c_p / c (psi(y - f(x)) + 1) + c_p abs(f(x))^p quad "and" quad abs(f(x))^p <= c_p / c (psi(y - f(x)) + 1) + c_p abs(y)^p $
  with respect to $P$; this gives both inequalities with $c_(L, p) := c_p max{1, 1\/c}$.
]

#remark[
  + For $q = p$ we get $s = p$. So if $abs(P)_p < oo$, then $risk(L, P)$ is *locally Lipschitz continuous on
    $L^p (P_X)$*: on every ball ${norm(f)_(L^p (P_X)) <= B}$, where all risks are finite by (i), it is
    Lipschitz with respect to $norm(dot)_(L^p (P_X))$. For $q = oo$ we get $s = 1$, a bound in terms of
    $norm(f - g)_(L^1 (P_X))$ for bounded $f, g$ and bounded outputs. For least squares ($p = q = 2$) the
    bound reads
    $ abs(risk(L, P)(f) - risk(L, P)(g)) <= c (abs(P)_2 + norm(f)_(L^2 (P_X)) + norm(g)_(L^2 (P_X)) + 1) norm(f - g)_(L^2 (P_X)), $
    which can also be read off directly from
    $risk(L, P)(f) - risk(L, P)(g) = integral (g(x) - f(x))(2y - f(x) - g(x)) dif P(x, y)$ and the
    Cauchy–Schwarz inequality.
  + For a loss of growth type $p$ and $abs(P)_p < oo$, parts (i) and (iii) show that
    $risk(L, P)(f) < oo$ if and only if $f in cal(L)^p (P_X)$: the risk "lives" on $L^p (P_X)$. If
    $abs(P)_p = oo$, then (iii) gives $risk(L, P)(f) = oo$ for every $f in cal(L)^p (P_X)$. Note, however, that
    the Bayes risk may still be finite: for least squares with $P(dot | x) = cal(N)(m(x), 1)$ and $m in.not L^2 (P_X)$,
    we have $abs(P)_2 = oo$, but $risk(L, P)(m) = 1$.
] <rem:loss-distance-bounds-remarks>

== Margin-based losses <sec:loss-margin>

In binary classification, $Y = {-1, 1}$, and a real-valued decision function $f$ classifies $x$ as
$sign(f(x))$. The product $y f(x)$ is called the *margin* of $f$ at $(x, y)$. It is positive if and only if
the classification is correct (for $f(x) != 0$), and its size measures the confidence: $y f(x) = 3$ is a
confident correct answer, $y f(x) = -3$ a confident mistake. Losses that depend only on the margin treat
both classes symmetrically.

#definition(title: [Margin-based losses])[
  Let $Y = {-1, 1}$. A supervised loss $L: Y times RR -> [0, oo)$ is called *margin-based* if there is a
  measurable function $phi: RR -> [0, oo)$ such that
  $ L(y, t) = phi(y t) quad "for all" y in Y, t in RR. $
  The function $phi$ is called the *representing function* of $L$.
] <def:loss-margin>

Since $L(1, t) = phi(t)$ and $L(-1, t) = phi(-t)$, the representing function is uniquely determined by
$L$: $phi = L(1, dot)$. In contrast to distance-based losses on unbounded $Y$, margin-based losses inherit
all regularity from $phi$, including local Lipschitz continuity, because $y$ only takes the values $plus.minus 1$.

#proposition[
  Let $L$ be a margin-based loss with representing function $phi$. Then:
  + $L$ is convex, respectively strictly convex, if and only if $phi$ is.
  + $L$ is continuous if and only if $phi$ is.
  + $L$ is locally Lipschitz continuous if and only if $phi$ is, and then
    $abs(L)_(r, 1) = abs(phi|_([-r, r]))_1$ for all $r >= 0$. $L$ is Lipschitz continuous if and only if
    $phi$ is, and then $abs(L)_1 = abs(phi)_1$.
  + If $L$ is convex, then $L$ is locally Lipschitz continuous (in particular continuous).
  + If $phi$ is locally bounded (e.g. continuous, or convex), then $L$ is a $P$-integrable Nemitski loss for
    every distribution $P$ on $X times Y$; one can take $b = 0$ and $h(s) := sup_(abs(u) <= s) phi(u)$. If
    moreover $phi(u) <= c(abs(u)^p + 1)$ for some $c, p > 0$, then $L$ is a $P$-integrable Nemitski loss of
    order $p$ for every $P$. Conversely, if $L$ is a Nemitski loss, then $phi$ is locally bounded.
] <prop:loss-margin-properties>

#proof[
  (i), (ii) The functions $L(1, dot) = phi$ and $L(-1, dot) = phi compose (-id)$ are obtained from $phi$ by
  composition with affine bijections of $RR$, which preserve convexity, strict convexity and continuity;
  conversely $phi = L(1, dot)$.

  (iii) For $t, t' in [-r, r]$ we have
  $ abs(L(1, t) - L(1, t')) = abs(phi(t) - phi(t')) quad "and" quad abs(L(-1, t) - L(-1, t')) = abs(phi(-t) - phi(-t')), $
  where also $-t, -t' in [-r, r]$ and $abs((-t) - (-t')) = abs(t - t')$. Taking suprema of the difference quotients
  over $y in {-1, 1}$ and $t != t'$ in $[-r, r]$ gives $abs(L)_(r, 1) = abs(phi|_([-r, r]))_1$. Taking the
  supremum over $r >= 0$ gives the statement about $abs(L)_1$.

  (iv) If $L$ is convex, $phi$ is convex by (i), hence locally Lipschitz continuous by
  @lem:app-convex-lipschitz, and (iii) applies.

  (v) If $phi$ is locally bounded, then $h(s) := sup_(abs(u) <= s) phi(u)$ is finite for every $s >= 0$ and
  non-decreasing, and $L(y, t) = phi(y t) <= h(abs(y t)) = h(abs(t))$ since $abs(y) = 1$. So @eq:loss-nemitski
  holds with $b = 0$, which is integrable for every $P$. Continuous functions are bounded on compact
  intervals, and so are convex functions by (iv). If $phi(u) <= c(abs(u)^p + 1)$, then
  $L(y, t) <= c + c abs(t)^p$, which is @def:loss-nemitski of order $p$ with the integrable constant $b = c$.
  Conversely, if $L(y, t) <= b(x, y) + h(abs(t))$ for some $(x, y)$ with $y = 1$ (any fixed $x in X$), then
  $sup_(abs(t) <= s) phi(t) <= b(x, 1) + h(s) < oo$ for every $s$.
]

Local boundedness in (v) cannot be dropped: for the measurable function $phi(u) := 1\/abs(u)$ for
$u != 0$, $phi(0) := 0$, the loss $L(y, t) = phi(y t)$ is not a Nemitski loss for any $P$, by the last
statement of (v).

#context-note[
  Typical margin-based losses have a non-increasing representing function $phi$ with $phi(u) -> 0$ as
  $u -> oo$ (hinge, logistic, exponential), so they reward large positive margins and penalize negative
  ones. The least squares loss is margin-based on $Y = {-1, 1}$, but it also penalizes margins larger than
  $1$ ("too correct" predictions), which is one reason why it is less popular for classification. For
  convex $phi$, @bartlett2006 showed that the surrogate is *classification calibrated* (minimizing the
  $phi$-risk leads to Bayes-optimal classification) if and only if $phi$ is differentiable at $0$ with
  $phi'(0) < 0$.
]

== A catalogue of loss functions <sec:loss-catalogue>

We now collect the losses most frequently used in practice and verify their properties. They are the
running examples of the rest of the book: the hinge loss leads to support vector machines, the least squares
loss to kernel ridge regression (@ex:reg-krr). @tab:loss-properties summarizes the results and
@fig:loss-margin-losses, @fig:loss-regression-losses show the representing functions.

#example(title: [Catalogue of standard losses])[
  #set enum(numbering: "1.")
  *Classification losses* ($Y = {-1, 1}$, margin-based losses given by their representing functions $phi$,
  except for the first one):
  + *Classification (0-1) loss:* $L(y, t) = ind_((-oo, 0]) (y sign(t))$ with $sign(0) := 1$. It is bounded, not
    continuous, not convex, and *not* margin-based. Its margin-based variant
    $phi_(0-1) (u) := ind_((-oo, 0]) (u)$ agrees with it except at $(y, t) = (1, 0)$.
  + *Least squares loss:* $phi(u) = (1 - u)^2$, since $(y - t)^2 = (1 - y t)^2$ for $y in {-1, 1}$. Strictly
    convex, differentiable, locally Lipschitz with $abs(L)_(r, 1) = 2r + 2$, not Lipschitz, Nemitski of order
    $2$.
  + *Hinge loss:* $phi(u) = max{0, 1 - u}$. Convex, not strictly convex, Lipschitz with $abs(L)_1 = 1$, not
    differentiable (at $u = 1$), Nemitski of order $1$.
  + *Squared hinge loss:* $phi(u) = (max{0, 1 - u})^2$. Convex, not strictly convex, continuously
    differentiable, locally Lipschitz with $abs(L)_(r, 1) = 2r + 2$, not Lipschitz, Nemitski of order $2$.
  + *Logistic loss:* $phi(u) = ln(1 + e^(-u))$. Strictly convex, infinitely differentiable, Lipschitz with
    $abs(L)_1 = 1$, Nemitski of order $1$.
  + *Exponential loss:* $phi(u) = e^(-u)$. Strictly convex, infinitely differentiable, locally Lipschitz with
    $abs(L)_(r, 1) = e^r$, not Lipschitz, Nemitski (with $h(s) = e^s$) but not of any order $p$.

  *Regression losses* ($Y subset.eq RR$, distance-based losses given by their representing functions
  $psi$, all continuous):
  7. *$L_p$-loss*, $p in (0, oo)$: $psi(r) = abs(r)^p$. Symmetric, of growth type $p$; convex if and only if
    $p >= 1$, strictly convex if and only if $p > 1$; Lipschitz if and only if $p = 1$, and not even
    locally Lipschitz if $p < 1$; differentiable if and only if $p > 1$. The case $p = 2$ is the least
    squares loss, $p = 1$ the *absolute loss*.
  + *Logistic loss for regression:* $psi(r) = -ln (4 e^r \/ (1 + e^r)^2)$. Symmetric, strictly convex,
    infinitely differentiable, Lipschitz with $abs(psi)_1 = 1$, of growth type $1$.
  + *Huber loss* with parameter $alpha > 0$: $psi(r) = r^2 \/ 2$ for $abs(r) <= alpha$ and
    $psi(r) = alpha abs(r) - alpha^2 \/ 2$ for $abs(r) > alpha$. Symmetric, convex, not strictly convex,
    continuously differentiable, Lipschitz with $abs(psi)_1 = alpha$, of growth type $1$.
  + *$epsilon$-insensitive loss* with parameter $epsilon > 0$: $psi(r) = max{0, abs(r) - epsilon}$. Symmetric,
    convex, not strictly convex, not differentiable, Lipschitz with $abs(psi)_1 = 1$, of growth type $1$.
  + *Pinball (quantile) loss* with parameter $tau in (0, 1)$: $psi(r) = tau r$ for $r >= 0$ and
    $psi(r) = (tau - 1) r$ for $r < 0$. Convex, not strictly convex, not differentiable, Lipschitz with
    $abs(psi)_1 = max{tau, 1 - tau}$, of growth type $1$; symmetric only for $tau = 1\/2$, where it is half the
    absolute loss.
] <ex:loss-catalogue>

#figure(
  cetz.canvas({
    plot.plot(
      size: (8, 5.5),
      x-tick-step: 1, y-tick-step: 1,
      x-min: -2, x-max: 3, y-min: 0, y-max: 4,
      x-label: $u = y t$, y-label: $phi(u)$,
      axis-style: "scientific",
      legend: "east",
      legend-style: (stroke: 0.4pt + luma(150), fill: white),
      {
        plot.add(((-2, 1), (0, 1)), style: (stroke: 1.4pt + black), label: [0-1 (margin variant)])
        plot.add(((0, 0), (3, 0)), style: (stroke: 1.4pt + black))
        plot.add(domain: (-2, 3), x => calc.max(0, 1 - x),
          style: (stroke: 1.2pt + rgb("#1f5fa8")), label: [hinge])
        plot.add(domain: (-2, 3), samples: 120, x => calc.pow(calc.max(0, 1 - x), 2),
          style: (stroke: (paint: rgb("#1f5fa8"), thickness: 1.2pt, dash: "dashed")), label: [squared hinge])
        plot.add(domain: (-2, 3), samples: 120, x => calc.ln(1 + calc.exp(-x)),
          style: (stroke: 1.2pt + rgb("#2a8a3e")), label: [logistic])
        plot.add(domain: (-2, 3), samples: 120, x => calc.exp(-x),
          style: (stroke: 1.2pt + rgb("#8e44ad")), label: [exponential])
        plot.add(domain: (-2, 3), samples: 120, x => calc.pow(1 - x, 2),
          style: (stroke: (paint: rgb("#c0392b"), thickness: 1.2pt, dash: "dotted")), label: [least squares])
      },
    )
  }),
  caption: [Representing functions $phi$ of margin-based classification losses. Negative margins
    $u = y t < 0$ correspond to misclassifications. The convex losses are surrogates for the 0-1 loss; the
    hinge loss and the exponential loss are upper bounds of it, and so is the logistic loss after division by
    $ln 2$. The least squares loss also penalizes large positive margins.],
) <fig:loss-margin-losses>

#figure(
  grid(
    columns: 2,
    column-gutter: 0.6cm,
    cetz.canvas({
      plot.plot(
        size: (6, 4.2),
        x-tick-step: 1, y-tick-step: 1,
        x-min: -3, x-max: 3, y-min: 0, y-max: 3,
        x-label: $r = y - t$, y-label: $psi(r)$,
        legend: "south",
        legend-style: (stroke: 0.4pt + luma(150), fill: white),
        {
          plot.add(domain: (-3, 3), samples: 120, x => x * x,
            style: (stroke: (paint: rgb("#c0392b"), thickness: 1.2pt, dash: "dotted")), label: [least squares])
          plot.add(domain: (-3, 3), x => calc.abs(x),
            style: (stroke: 1.2pt + black), label: [absolute])
          plot.add(domain: (-3, 3), samples: 120,
            x => if calc.abs(x) <= 1 { x * x / 2 } else { calc.abs(x) - 0.5 },
            style: (stroke: 1.2pt + rgb("#1f5fa8")), label: [Huber, $alpha = 1$])
          plot.add(domain: (-3, 3), samples: 120,
            x => 2 * calc.ln(1 + calc.exp(x)) - x - calc.ln(4),
            style: (stroke: (paint: rgb("#2a8a3e"), thickness: 1.2pt, dash: "dashed")), label: [logistic])
        },
      )
    }),
    cetz.canvas({
      plot.plot(
        size: (6, 4.2),
        x-tick-step: 1, y-tick-step: 1,
        x-min: -3, x-max: 3, y-min: 0, y-max: 3,
        x-label: $r = y - t$, y-label: none,
        legend: "south",
        legend-style: (stroke: 0.4pt + luma(150), fill: white),
        {
          plot.add(domain: (-3, 3), x => calc.max(0, calc.abs(x) - 0.5),
            style: (stroke: 1.2pt + rgb("#8e44ad")), label: [$epsilon$-insensitive, $epsilon = 1\/2$])
          plot.add(domain: (-3, 3), x => if x >= 0 { 0.25 * x } else { -0.75 * x },
            style: (stroke: 1.2pt + rgb("#d35400")), label: [pinball, $tau = 1\/4$])
          plot.add(domain: (-3, 3), samples: 120, x => calc.sqrt(calc.abs(x)),
            style: (stroke: (paint: luma(90), thickness: 1.2pt, dash: "dashed")), label: [$L_p$, $p = 1\/2$])
        },
      )
    }),
  ),
  caption: [Representing functions $psi$ of distance-based regression losses. Left: smooth and robust
    variants of least squares. Right: losses with a flat or asymmetric part, and the non-convex $L_(1\/2)$-loss.],
) <fig:loss-regression-losses>

=== Verification of the properties

Throughout we use the following standard facts from real analysis: a differentiable function on an interval
with non-decreasing derivative is convex, and with strictly increasing derivative (e.g. positive second
derivative) it is strictly convex; the pointwise maximum of convex functions is convex; a function that is
affine on a nondegenerate interval is not strictly convex; a bounded convex function on $RR$ is constant
(by the monotonicity of difference quotients); and $abs(g|_([a,b]))_1 = sup_([a, b]) abs(g')$ for
differentiable $g$ (@sec:loss-lipschitz). For margin-based losses, @prop:loss-margin-properties transfers
properties of $phi$ to $L$; for distance-based losses, @lem:loss-distance-basic does the same (for local
Lipschitz continuity of $L$ see @rem:loss-distance-lipschitz), and @lem:loss-growth-convex (i), (ii) give
growth type $1$ for convex Lipschitz $psi$ with $psi(r) -> oo$ as $abs(r) -> oo$.

*Classification loss.* Recall $L(1, t) = ind_((-oo, 0)) (t)$ and $L(-1, t) = ind_([0, oo)) (t)$ (with
$sign(0) = 1$, the prediction $t = 0$ is read as class $+1$). If $L(y, t) = phi(y t)$, then $y = 1$ forces
$phi(0) = L(1, 0) = 0$, while $y = -1$ forces $phi(0) = L(-1, 0) = 1$, a contradiction; so $L$ is not
margin-based. The discrepancy sits only at $t = 0$: the margin-based variant $phi_(0-1) (y t)$ counts $t = 0$
as an error for both classes. Whether "the 0-1 loss is margin-based" thus depends on the convention at
$t = 0$. $L(y, dot)$ jumps at $0$, so $L$ is not continuous; a nonconstant bounded function on $RR$ is not
convex. $L <= 1$ makes it a $P$-integrable Nemitski loss for every $P$.

*Least squares.* $phi(u) = (1 - u)^2$ has $phi'' = 2 > 0$, and
$abs(phi|_([-r, r]))_1 = sup_(abs(u) <= r) 2 abs(u - 1) = 2 r + 2$, which is unbounded in $r$. The bound
$phi(u) <= 2 + 2u^2$ gives order $2$.

*Hinge loss.* The function $phi$ is the maximum of the affine functions $0$ and $1 - u$, hence convex; it vanishes on
$[1, oo)$, so it is not strictly convex. Since $abs(max{a, b} - max{a', b'}) <= max{abs(a - a'), abs(b - b')}$,
$phi$ is $1$-Lipschitz, and the constant $1$ is attained on $(-oo, 1)$ where $phi' = -1$. The one-sided
derivatives at $u = 1$ are $-1$ and $0$. Finally $phi(u) <= 1 + abs(u)$.

*Squared hinge loss.* $phi = g^2$ with $g(u) = max{0, 1 - u}$ convex and nonnegative; as $v |-> v^2$ is
convex and non-decreasing on $[0, oo)$, $phi$ is convex. It is differentiable with the continuous derivative
$phi'(u) = -2 max{0, 1 - u}$, so $abs(phi|_([-r, r]))_1 = 2(1 + r)$. It vanishes on $[1, oo)$, and
$phi(u) <= (1 + abs(u))^2 <= 2 + 2 u^2$.

*Logistic loss.* Here
$ phi'(u) = - e^(-u) / (1 + e^(-u)) = - 1 / (1 + e^u) in (-1, 0) quad "and" quad phi''(u) = e^u / (1 + e^u)^2 > 0. $
Hence $phi$ is strictly convex, and $abs(phi)_1 = sup abs(phi') = 1$
(approached as $u -> -oo$, not attained). By the Lipschitz property, $phi(u) <= phi(0) + abs(u) = ln 2 + abs(u)$.

*Exponential loss.* $phi'' = e^(-u) > 0$ and $abs(phi|_([-r, r]))_1 = sup_(abs(u) <= r) e^(-u) = e^r$. With
$h(s) = e^s$ we have $phi(y t) <= e^(abs(t))$, so $L$ is Nemitski. It is not of any order $p$: for fixed $y = 1$
and $t -> -oo$, $e^(-t)$ grows faster than $c abs(t)^p$ plus a constant.

*$L_p$-losses.* $psi(r) = abs(r)^p$ satisfies $abs(r)^p - 1 <= psi(r) <= abs(r)^p + 1$, so it is of growth type
$p$ with $c = 1$ in both bounds. For $p >= 1$, $psi$ is the composition of the convex function $abs(dot)$ with
the convex non-decreasing function $v |-> v^p$ on $[0, oo)$, hence convex. For $p < 1$ it is not convex:
$psi(1\/2) = 2^(-p) > 1\/2 = (psi(0) + psi(1))\/2$. For $p > 1$ it is strictly convex: let $r != r'$ and
$alpha in (0, 1)$; then
$abs(alpha r + (1 - alpha) r')^p <= (alpha abs(r) + (1 - alpha) abs(r'))^p <= alpha abs(r)^p + (1 - alpha) abs(r')^p$.
If $abs(r) != abs(r')$, the second inequality is strict by strict convexity of $v |-> v^p$. If
$abs(r) = abs(r')$, then $r' = -r != 0$ and $abs(alpha r + (1 - alpha) r') = abs(2 alpha - 1) abs(r) < abs(r)$, so the
first inequality is strict because $v |-> v^p$ is strictly increasing. For $p = 1$, $psi$ is linear on
$[0, oo)$, hence not strictly convex. Lipschitz continuity: $abs(dot)$ is $1$-Lipschitz. For $p > 1$,
$(psi(r) - psi(0))\/r = r^(p - 1) -> oo$ as $r -> oo$, and for $p < 1$ the same quotient tends to $oo$ as
$r -> 0^+$, so $psi$ is not even Lipschitz on $[-1, 1]$. Differentiability: away from $0$, $psi$ is smooth,
and at $0$ the quotient $psi(r)\/r = sign(r) abs(r)^(p - 1)$ tends to $0$ if $p > 1$ and has no limit if
$p <= 1$.

*Logistic loss for regression.* Writing $psi(r) = 2 ln(1 + e^r) - r - ln 4$, we get $psi(0) = 0$ and, using
$ln(1 + e^(-r)) = ln(1 + e^r) - r$, also $psi(-r) = 2 ln (1 + e^r) - 2r + r - ln 4 = psi(r)$, so $psi$ is
symmetric. Further
$ psi'(r) = (2 e^r) / (1 + e^r) - 1 = tanh(r / 2) in (-1, 1) quad "and" quad psi''(r) = (2 e^r) / (1 + e^r)^2 > 0. $ Hence $psi$ is strictly convex and $1$-Lipschitz with
$abs(psi)_1 = 1$, and $psi(r) -> oo$ as $abs(r) -> oo$; by @lem:loss-growth-convex (i), (ii) it is of growth
type $1$. Since $psi''(0) = 1\/2$, it behaves like $r^2\/4$ near $0$ and like $abs(r) - ln 4$ for large
$abs(r)$: a smooth compromise between least squares and the absolute loss.

*Huber loss.* $psi$ is continuous at $abs(r) = alpha$ (both expressions equal $alpha^2 \/ 2$) and
differentiable with $psi'(r) = max{-alpha, min{r, alpha}}$, which is continuous and non-decreasing; hence
$psi$ is convex and $abs(psi)_1 = sup abs(psi') = alpha$. It is affine on $[alpha, oo)$, so not strictly
convex; $psi'$ is not differentiable at $plus.minus alpha$. Growth type $1$ follows from
@lem:loss-growth-convex (i), (ii).

*$epsilon$-insensitive loss.* $psi$ is the maximum of the convex functions $0$ and $abs(r) - epsilon$, hence
convex; it vanishes on $[-epsilon, epsilon]$, so it is not strictly convex, and it has kinks at
$plus.minus epsilon$. As a maximum of $1$-Lipschitz functions it is $1$-Lipschitz, with slope $plus.minus 1$
outside $[-epsilon, epsilon]$. Growth type $1$ follows as before.

*Pinball loss.* $psi(r) = max{tau r, (tau - 1) r}$ (for $r >= 0$ the first term is the larger one, for
$r < 0$ the second), a maximum of linear functions, hence convex; it is linear on $[0, oo)$, so not strictly
convex, and has a kink at $0$. Its slopes are $tau$ and $tau - 1$, so $abs(psi)_1 = max{tau, 1 - tau}$.
Finally $min{tau, 1 - tau} abs(r) <= psi(r) <= max{tau, 1 - tau} abs(r)$ gives growth type $1$ directly.

#figure(
  placement: auto,
  {
  set text(size: 9pt)
  set par(justify: false)
  table(
    columns: (auto, auto, auto, auto, auto, auto, auto),
    align: (left, center, center, center, center, center, center),
    stroke: (x, y) => (
      top: if y == 0 { 0.8pt } else if y == 1 or y == 7 { 0.5pt } else { 0pt },
      bottom: if y == 13 { 0.8pt } else { 0pt },
    ),
    inset: (x: 4pt, y: 3.5pt),
    table.header(
      [*Loss*], [*convex*], [*strictly \ convex*], [*differ- \ entiable*], [*Lipschitz \ constant*], [*local constant \ on $[-r, r]$*], [*growth \ or order*],
    ),
    [0-1], [no], [no], [no], [—], [—], [bounded],
    [least squares], [yes], [yes], [yes], [—], [$2r + 2$], [order 2],
    [hinge], [yes], [no], [no], [$1$], [$1$ $(r > 0)$], [order 1],
    [squared hinge], [yes], [no], [yes], [—], [$2r + 2$], [order 2],
    [logistic], [yes], [yes], [yes], [$1$], [$1\/(1 + e^(-r))$], [order 1],
    [exponential], [yes], [yes], [yes], [—], [$e^r$], [none],
    [$L_p$, $0 < p < 1$], [no], [no], [no], [—], [$oo$], [type $p$],
    [absolute ($L_1$)], [yes], [no], [no], [$1$], [$1$ $(r > 0)$], [type 1],
    [$L_p$, $1 < p < oo$], [yes], [yes], [yes], [—], [$p r^(p-1)$], [type $p$],
    [logistic (regr.)], [yes], [yes], [yes], [$1$], [$tanh(r\/2)$], [type 1],
    [Huber], [yes], [no], [yes], [$alpha$], [$min{r, alpha}$], [type 1],
    [$epsilon$-insensitive], [yes], [no], [no], [$1$], [$ind_((epsilon, oo)) (r)$], [type 1],
    [pinball], [yes], [no], [no], [$max{tau, 1 - tau}$], [$max{tau, 1 - tau}$ $(r > 0)$], [type 1],
  )
  },
  kind: table,
  caption: [Properties of the standard losses of @ex:loss-catalogue. The first six rows are classification
    losses on $Y = {-1, 1}$; for the margin-based ones, properties of $phi$ and $L$ coincide
    (@prop:loss-margin-properties), and the local constant is $abs(L)_(r, 1) = abs(phi|_([-r, r]))_1$. The 0-1
    loss is not continuous. The last seven rows are distance-based regression losses; there the Lipschitz
    constant, the local constant $abs(psi|_([-r, r]))_1$ and the growth type (@def:loss-growth) refer to
    $psi$, and $L$ itself is locally Lipschitz on an unbounded $Y$ only if $psi$ is Lipschitz
    (@rem:loss-distance-lipschitz). A dash means "not Lipschitz". "Order $p$" means Nemitski of order $p$
    for every $P$ (@def:loss-nemitski).],
) <tab:loss-properties>

=== The $L_p$-losses for $p < 1$

The $L_p$-losses with $p < 1$ are even more robust against outliers than the absolute loss, since they grow
sublinearly (@fig:loss-lp). But they are not convex, and the associated function space is badly behaved.
If $Y = {0}$, say, then $risk(L_p, P)(f) = integral abs(f)^p dif P_X$, so the risk is finite exactly on
$L^p (P_X)$, and the natural "size" of $f$ is $integral abs(f)^p dif P_X$. For $p < 1$ this quantity does not
come from a norm. Suppose there are two disjoint events $A, B subset.eq X$ with $P_X (A) = P_X (B) = 1\/2$
(for instance, if $P_X$ has no atoms) and put
$f := 2^(1\/p) ind_A$, $g := 2^(1\/p) ind_B$. Then $integral abs(f)^p dif P_X = integral abs(g)^p dif P_X = 1$, but
$ integral abs((f + g) / 2)^p dif P_X = 2^(1 - p) dot integral ind_(A union B) dif P_X = 2^(1 - p) > 1. $
So the "unit ball" ${f : integral abs(f)^p dif P_X <= 1}$ is not convex, and
$f |-> (integral abs(f)^p dif P_X)^(1\/p)$ violates the triangle inequality. In fact, if $P_X$ has no atoms,
$L^p (P_X)$ is not normable at all (@sec:app-lp): no norm induces its topology. It is still a complete metric
vector space with the metric $d_p (f, g) = integral abs(f - g)^p dif P_X$, but the Banach-space tools used
in this book (duality, convex analysis, Hilbert-space geometry) are not available. This is one more reason
to restrict attention to convex losses in the following chapters.

The lecture summarized this as "for $p < 1$, $L^p$ is not a Banach space but an Orlicz space". The
statement refers to spaces defined by a *modular* $integral Phi(abs(f)) dif P_X$ with a non-decreasing
$Phi: [0, oo) -> [0, oo)$, $Phi(0) = 0$, namely the space of all $f$ with $integral Phi(abs(f) \/ c) dif P_X < oo$
for some $c > 0$. For convex $Phi$ these are the classical Orlicz spaces, which are Banach spaces
($Phi(u) = u^p$ with $p >= 1$ gives $L^p$). For $Phi(u) = u^p$ with $p < 1$ the modular is not convex, and
one obtains a complete metric vector space, but not a normed one.

#figure(
  cetz.canvas({
    plot.plot(
      size: (7, 5),
      x-tick-step: 0.5, y-tick-step: 0.5,
      x-min: 0, x-max: 1.6, y-min: 0, y-max: 2,
      x-label: $abs(r)$, y-label: $abs(r)^p$,
      legend: "inner-north-west",
      legend-style: (stroke: 0.4pt + luma(150), fill: white),
      {
        plot.add(domain: (0, 1.6), samples: 200, x => calc.pow(x, 0.25),
          style: (stroke: 1.2pt + rgb("#8e44ad")), label: [$p = 1\/4$])
        plot.add(domain: (0, 1.6), samples: 200, x => calc.sqrt(x),
          style: (stroke: 1.2pt + rgb("#1f5fa8")), label: [$p = 1\/2$])
        plot.add(domain: (0, 1.6), x => x,
          style: (stroke: 1.2pt + black), label: [$p = 1$])
        plot.add(domain: (0, 1.6), samples: 100, x => x * x,
          style: (stroke: 1.2pt + rgb("#2a8a3e")), label: [$p = 2$])
        plot.add(domain: (0, 1.6), samples: 100, x => calc.pow(x, 4),
          style: (stroke: 1.2pt + rgb("#c0392b")), label: [$p = 4$])
        plot.add(((1, 0), (1, 1), (0, 1)), style: (stroke: (paint: luma(140), thickness: 0.5pt, dash: "dashed")))
      },
    )
  }),
  caption: [The $L_p$-losses $psi(r) = abs(r)^p$ for several $p$ (a redrawing of the lecture's sketch). All
    curves pass through $(1, 1)$. For $p > 1$ small residuals are forgiven and large ones heavily penalized;
    for $p < 1$ the graph is concave on $[0, oo)$, large residuals are penalized only mildly, and the loss is
    not convex.],
) <fig:loss-lp>

=== Where these losses are used

#context-note[
  - *Least squares* is the classical loss of regression; its Bayes decision function is the conditional mean
    (@ex:learn-least-squares). Regularized least squares in an RKHS is *kernel ridge regression*
    (@ex:reg-krr), whose solution coincides with the posterior mean of Gaussian process regression with a
    suitable noise variance @rasmussen2006 and, for suitable kernels, with smoothing splines @wahba1990.
  - The *absolute loss* leads to the conditional median, and the *pinball loss* with parameter $tau$ to the
    conditional $tau$-quantile (@ex:loss-exercise-pinball); this is the basis of quantile regression
    @koenker2005.
  - The *Huber loss* was introduced by @huber1964 for robust estimation of a location parameter: it is
    quadratic for small residuals and linear for large ones, so outliers have bounded influence on the
    derivative.
  - The *$epsilon$-insensitive loss* is used in support vector regression @vapnik1998; residuals smaller than
    $epsilon$ are ignored, which leads to sparse solutions.
  - The *hinge loss* defines the support vector machine @cortes1995 @steinwart2008; the flat part on
    $[1, oo)$ is responsible for the sparsity of its solutions (support vectors, @thm:reg-general-representer).
  - The *logistic loss* is the negative log-likelihood of the model in which $P(y = 1 | x) = 1 \/ (1 + e^(-f(x)))$;
    indeed, then $P(y | x) = 1 \/ (1 + e^(-y f(x)))$ for both $y in {-1, 1}$. Minimizing it is (penalized)
    logistic regression @hastie2009.
  - The *exponential loss* underlies AdaBoost @freund1997, which can be interpreted as a stagewise
    minimization of the empirical exponential risk @hastie2009.
  - The *logistic loss for regression* is the negative log-likelihood of logistic noise, normalized to vanish
    at $0$: $e^r \/ (1 + e^r)^2$ is the density of the standard logistic distribution, with value $1\/4$ at $0$.
]

== Summary <sec:loss-summary>

- The risk $risk(L, P)(f) = integral L(x, y, f(x)) dif P(x, y)$ is a nonlinear functional with values in
  $[0, oo]$ that depends only on the $P_X$-equivalence class of $f$ (@lem:loss-classes). On separable complete
  function spaces dominating pointwise convergence, such as separable RKHSs, it is measurable
  (@prop:loss-measurability).
- Convexity of $L$ passes to the risk without further assumptions; strict convexity passes for functions
  with finite risk that differ on a set of positive measure (@prop:loss-convex-risk).
- Continuity of $L$ does not make the risk continuous (@ex:loss-spike), but it makes it lower semicontinuous
  under convergence in probability (@prop:loss-lsc).
- Nemitski conditions $L(x, y, t) <= b(x, y) + h(abs(t))$ with $b in L^1 (P)$ provide integrable majorants.
  For continuous $P$-integrable Nemitski losses the risk is continuous on $L^oo (P_X)$, and on $L^p (P_X)$ for
  losses of order $p$ (@prop:loss-risk-continuity). Convex losses are continuous, so this covers all convex
  Nemitski losses.
- Lipschitz losses give Lipschitz risks with respect to $norm(dot)_(L^1 (P_X))$ (@prop:loss-lipschitz-risk);
  differentiable losses with Nemitski derivative give Fréchet differentiable risks on $L^oo (P_X)$ with
  derivative $g |-> integral g(x) L'(x, y, f(x)) dif P(x, y)$ (@prop:loss-frechet).
- Distance-based losses $psi(y - t)$ are classified by their growth type $p$; the risk is then finite on
  $L^p (P_X)$ if and only if the output has a finite $p$-th moment, and it is locally Lipschitz on $L^p$ for
  convex $psi$ (@prop:loss-distance-risk-bounds). Margin-based losses $phi(y t)$ inherit all properties of $phi$
  and are Nemitski for every $P$ (@prop:loss-margin-properties).
- @tab:loss-properties summarizes the properties of the standard losses.

In the next chapter we turn to the second ingredient of regularized learning, the hypothesis space: we
construct reproducing kernel Hilbert spaces and study their functions. The two threads come together in
@sec:reg, where the continuity and convexity results of this chapter give existence of regularized
minimizers.

== Notes and further reading <sec:loss-notes>

This chapter follows Chapter 2 of @steinwart2008 closely, which treats losses, risks and Nemitski losses in
more detail and contains many further examples; the distance-based risk bounds of @prop:loss-distance-risk-bounds are @steinwart2008[Lemma 2.38]. The
question of how surrogate losses relate to the loss one is really interested in (for example, hinge versus
0-1 loss) is the subject of @steinwart2008[Chapter 3] and of @bartlett2006; the 0-1 loss and the Bayes
classifier are treated in depth in @devroye1996.

Integral functionals $f |-> integral L(x, y, f(x)) dif P$ and the superposition (Nemytskii) operators behind
them are classical objects of nonlinear and convex analysis; @appell1990 is a monograph on superposition
operators. Convex integral functionals and their subdifferentials, which will appear in
@prop:reg-subdifferential-integral, go back to @rockafellar1968 and are treated in @ekeland1976. Fréchet and Gâteaux differentiability, in particular
of convex functions, is discussed in @phelps1993.

For the statistical background of the individual losses see @hastie2009 (least squares, logistic
regression, exponential loss and boosting, Huber loss), @huber1964 (robust estimation), @vapnik1998 and
@schoelkopf2002 (the $epsilon$-insensitive loss and support vector regression) and @cortes1995 (the hinge loss
and the soft-margin support vector machine). The spaces $L^p$ with $0 < p < 1$ are the standard examples of
complete metric vector spaces that are not locally convex; see @sec:app-lp.

== Exercises <sec:loss-exercises>

#exercise[
  Let $F: U -> W$ be a map between normed spaces as in @def:loss-frechet. Show that Fréchet
  differentiability at $v$ implies continuity at $v$ and Gâteaux differentiability at $v$ with the same
  derivative. Verify the details of the example $F(x_1, x_2) = ind_({x_2 = x_1^2, x_1 != 0})$ given after
  @def:loss-frechet.
] <ex:loss-exercise-frechet>

#exercise[
  Let $p in (0, 1)$. Show that $d_p (f, g) := integral abs(f - g)^p dif P_X$ defines a metric on $L^p (P_X)$.
  Prove that @prop:loss-risk-continuity (iii) holds for $p in (0, 1)$ with respect to this metric, constructing
  the majorant $G$ by hand instead of citing @thm:app-convergence (vi).

  _Hint:_ Use $(u + v)^p <= u^p + v^p$ for $u, v >= 0$, extended to countable sums, and choose a subsequence
  with $d_p (g_j, f) <= 2^(-j)$.
] <ex:loss-exercise-p-small>

#exercise[
  Let $L$ be the exponential loss $L(y, t) = e^(-y t)$ on $Y = {-1, 1}$.
  + Show that $L$ is a $P$-integrable Nemitski loss for every $P$, so that $risk(L, P)$ is continuous on
    $L^oo (P_X)$.
  + Let $X = (0, 1]$, $P_X$ the Lebesgue measure and $y = 1$ almost surely. Show that $f(x) := ln x$ lies in
    $L^p (P_X)$ for every $p in (0, oo)$, but $risk(L, P)(f) = oo$. Conclude that the order assumption in
    @prop:loss-risk-continuity (iii) cannot be dropped.
] <ex:loss-exercise-exp>

#exercise[
  Let $L$ be the pinball loss with parameter $tau in (0, 1)$ and let $Q$ be a distribution on $RR$ with
  $abs(Q)_1 < oo$. Show that $t^*$ minimizes the inner risk $I_(L, Q)$ if and only if $t^*$ is a
  $tau$-quantile of $Q$, that is, $Q((-oo, t^*)) <= tau <= Q((-oo, t^*])$. Deduce that the absolute loss
  leads to medians.

  _Hint:_ $I_(L, Q)$ is convex and finite. Show that its right and left derivatives are
  $Q((-oo, t]) - tau$ and $Q((-oo, t)) - tau$, respectively (use dominated convergence for the difference
  quotients), and use that a convex function has a minimum at $t^*$ if and only if its left derivative is
  $<= 0$ and its right derivative is $>= 0$ there.
] <ex:loss-exercise-pinball>

#exercise[
  Show that $abs(P)_oo = esssup_(x in X) abs(P(dot | x))_oo$, where the essential supremum is taken with respect
  to $P_X$.

  _Hint:_ For a distribution $Q$ on $RR$ and $M >= 0$, show that $abs(Q)_oo <= M$ if and only if
  $Q(RR without [-M, M]) = 0$. Then use $P({abs(y) > M}) = integral_X P({y : abs(y) > M} | x) dif P_X (x)$, and
  note that $x |-> abs(P(dot | x))_oo$ is measurable because $abs(P(dot|x))_oo <= M$ if and only if
  $P({abs(y) > M} | x) = 0$.
] <ex:loss-exercise-moments>

#exercise[
  Let $L$ be the least squares loss on $Y = RR$ and let $integral y^2 dif P(x, y) < oo$.
  + Show directly, without @prop:loss-distance-risk-bounds, that $risk(L, P)$ is finite and continuous on
    $L^2 (P_X)$.
  + Assume that the conditional mean $f_P$ is bounded. Show, using @ex:loss-ls-derivative, that $f_P$ is the
    unique (up to null sets) critical point of $risk(L, P)$ on $L^oo (P_X)$, and compare with
    @eq:learn-ls-decomposition.
] <ex:loss-exercise-ls>

#exercise[
  Let $L$ be a margin-based loss whose representing function $phi$ is convex, differentiable, and satisfies
  $abs(phi'(u)) <= c(abs(u)^(p-1) + 1)$ for some $c > 0$, $p >= 1$. Show that $L$ satisfies the hypotheses of
  @prop:loss-frechet for every distribution $P$, and compute $risk(L, P)'(f)$ for the logistic loss. Which of
  the losses in @ex:loss-catalogue satisfy these assumptions?
] <ex:loss-exercise-margin-derivative>
