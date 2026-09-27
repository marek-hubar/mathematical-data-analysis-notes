#import "/template.typ": *

// ---------------------------------------------------------------------------
// Local shorthands for this chapter
// ---------------------------------------------------------------------------
#let RH = $cal(R)^*_(L,P,H)$
#let Pb = $overline(P)$

// Closed forms for the spectral example (Example ex:stab-spectral), used in the figure.
// coth written in a numerically stable way.
#let stab-coth(x) = 1 + 2 / (calc.exp(2 * x) - 1)
#let stab-Ab(l) = if l <= 0 { 0 } else {
  (calc.pi * calc.sqrt(l) * stab-coth(calc.pi / calc.sqrt(l)) - l) / 2
}
#let stab-Aa(l) = l * (calc.pow(calc.pi, 2) / 6 - stab-Ab(l))

// Data for the L-curve figure: kernel ridge regression in eigen-coordinates
// (Remark rem:stab-krr-spectral) with w_j = j^(-3), c_j = j^(-2) + 0.01 (-1)^j.
#let stab-m = 100
#let stab-ws = range(1, stab-m + 1).map(j => calc.pow(j, -3.0))
#let stab-ss = range(1, stab-m + 1).map(j => calc.pow(j, -2.0))
#let stab-cs = range(1, stab-m + 1).map(j => calc.pow(j, -2.0) + if calc.rem(j, 2) == 0 { 0.01 } else { -0.01 })
#let stab-stats(l) = {
  let res = 0.0
  let nrm = 0.0
  let err = 0.0
  for j in range(stab-m) {
    let w = stab-ws.at(j)
    let c = stab-cs.at(j)
    res += calc.pow(l * c / (w + l), 2)
    nrm += w * c * c / calc.pow(w + l, 2)
    err += calc.pow(w * c / (w + l) - stab-ss.at(j), 2)
  }
  (res, nrm, err)
}
#let stab-lams = range(0, 71).map(k => calc.pow(10, -6 + k / 10))
#let stab-pts = stab-lams.map(l => stab-stats(l))
#let stab-best = {
  let b = 0
  for k in range(stab-pts.len()) {
    if stab-pts.at(k).at(2) < stab-pts.at(b).at(2) { b = k }
  }
  b
}

= Stability of Regularized Solutions <sec:stab>

In @sec:reg we saw that for a convex, $P$-integrable Nemitski loss $L$ and a bounded measurable kernel
$K$, the regularized risk
$ risk(L, P, lambda)(f) = risk(L, P)(f) + lambda norm(f)_H^2, quad f in H, $
has exactly one minimizer $f_(P,lambda)$ for every $lambda > 0$, and that representer theorems describe
it. This answered the questions Q1–Q3, Q6 and Q7 of @sec:reg-questions: existence, uniqueness and
representation. The present chapter is about the _behaviour_ of the solution, that is, about two kinds of
stability.

The first question (Q4) is how $f_(P,lambda)$ depends on the regularization parameter $lambda$. The
parameter is chosen by the user. If a tiny change of $lambda$ could change $f_(P,lambda)$
drastically, there would be no sensible way to choose it. Moreover, $lambda$ controls a trade-off: small
$lambda$ lets the solution fit the risk well, large $lambda$ keeps its norm small. We want to understand
both ends of this trade-off. What does $f_(P,lambda)$ approach as $lambda -> 0$, and how much risk do we
lose by regularizing? The central tool is the _approximation error function_
$A(lambda)$, which measures this loss.

The second question (Q8) is how $f_(P,lambda)$ depends on the distribution $P$. This is the heart of
learning: $P$ is unknown, and all we can compute is $f_(D,lambda)$ for the empirical measure $D$ of a
sample. If $f_(P,lambda)$ depends continuously, and even Lipschitz continuously, on $P$ in a suitable
sense, then $f_(D,lambda)$ is close to $f_(P,lambda)$ whenever $D$ is close to $P$. The same property
also means that the method is _robust_: a small fraction of contaminated data can move the solution only
a little.

The main results, stated informally, are the following.
- $A$ is non-decreasing, concave and continuous with $A(0) = 0$. It decays at most linearly: $A(lambda) = o(lambda)$
  only in the trivial case $A equiv 0$. Moreover, $A(lambda) = O(lambda)$ holds if and only if the risk has a minimizer in $H$
  (@prop:stab-approx-error, @cor:stab-equivalences).
- $lambda |-> f_(P,lambda)$ is continuous. As $lambda -> 0$, $f_(P,lambda)$ converges to the risk minimizer of
  _minimal norm_ $f_(P,H)$ whenever a risk minimizer exists. Otherwise $norm(f_(P,lambda))_H -> oo$
  (@thm:stab-lambda).
- $f_(P,lambda)$ depends Lipschitz continuously on $P$ with constant $1 \/ lambda$ (@thm:stab-measure).
- In the outlook (@sec:stab-outlook) we combine the last result with a law of large numbers in $H$ and
  obtain a consistency theorem: $risk(L, P)(f_(D,lambda_N)) -> RH$ in probability when $lambda_N -> 0$
  slowly enough. For universal kernels, the limit is the Bayes risk.

== The approximation error function <sec:stab-approx>

=== Setting

Throughout this chapter, $(X, cal(A))$ is a measurable space, $Y subset.eq RR$ is closed, $P$ is a
distribution on $X times Y$, $L: X times Y times RR -> [0, oo)$ is a loss function, and $H$ is an RKHS
of real-valued functions on $X$ with a measurable kernel $K$. As in @sec:reg, this means that $K$ is
$cal(A) times.o cal(A)$-measurable; in particular every section $K_x$, and hence every $f in H$, is
measurable (@prop:rkhs-measurable). We write
$ RH = inf_(f in H) risk(L, P)(f) quad "and" quad cal(M) := {f in H : risk(L, P)(f) = RH} $
for the smallest risk attainable in $H$ and the (possibly empty) set of risk minimizers in $H$. Most
results require the following *standard assumptions*:

#block(inset: (left: 1em))[
  *(S)* $L$ is convex and a $P$-integrable Nemitski loss, and $K$ is bounded, $abs(K)_oo < oo$.
]

Recall (@def:loss-nemitski) that the Nemitski condition means that there are a measurable
$b: X times Y -> [0, oo)$ with $integral b dif P < oo$ and a non-decreasing function
$rho: [0, oo) -> [0, oo)$ such that
$ L(x, y, t) <= b(x, y) + rho(abs(t)) quad "for all" (x, y, t) in X times Y times RR. $
(@def:loss-nemitski calls this function $h$; we write $rho$ because $h$ will denote subgradients.) Under
(S) we have the following facts, which we will use constantly.

+ Every $f in H$ is bounded with $norm(f)_oo <= abs(K)_oo norm(f)_H$ (@prop:rkhs-bounded). If $f_n -> f$
  weakly in $H$, then $f_n -> f$ pointwise, because $f_n (x) = ip(f_n, K_x)_H -> ip(f, K_x)_H = f(x)$ by
  the reproducing property @eq:rkhs-reproducing (@prop:rkhs-norm-convergence (ii)).
+ For every $lambda > 0$ there is exactly one minimizer $f_(P,lambda)$ of $risk(L, P, lambda)$
  (@thm:reg-existence, @prop:reg-uniqueness), and $lambda norm(f_(P,lambda))_H^2 <= risk(L, P)(0)$
  (@prop:reg-norm-bound).
+ The risk behaves well along bounded sequences in $H$. This is the content of the next lemma.

#lemma(title: [Continuity of the risk on $H$])[
  Assume (S). Let $f in H$ and let $(f_n)_(n in NN) subset H$ be a sequence with
  $sup_n norm(f_n)_H < oo$ and $f_n (x) -> f(x)$ for every $x in X$. Then
  $risk(L, P)(f_n) -> risk(L, P)(f)$. In particular, $risk(L, P)(f) < oo$ for all $f in H$, and
  $risk(L, P): H -> [0, oo)$ is convex and continuous with respect to the norm of $H$.
] <lem:stab-risk-continuity>

#proof[
  Put $B := abs(K)_oo max{sup_n norm(f_n)_H, norm(f)_H}$. Then $abs(f_n (x)) <= B$ for all $x$ and $n$
  (@prop:rkhs-bounded), and $L$ is continuous because it is convex (@def:loss-convex-continuous). So
  @prop:loss-risk-continuity (i) applies and gives $risk(L, P)(f_n) -> risk(L, P)(f)$. The remaining
  claims are @thm:reg-existence (ii).
]

=== Definition and first examples

Regularization comes at a price. The regularized solution $f_(P,lambda)$ does not minimize the risk
$risk(L, P)$ over $H$; it minimizes the risk _plus_ $lambda norm(f)_H^2$. How much risk do we give away?
A natural way to quantify this is to compare the optimal value of the regularized problem with the best
risk $RH$ achievable in $H$.

#definition(title: [Approximation error function])[
  Assume that $RH < oo$. The _approximation error function_ $A: [0, oo) -> [0, oo)$ is
  $ A(lambda) := inf_(f in H) (risk(L, P)(f) + lambda norm(f)_H^2) - RH
    = inf_(f in H) (risk(L, P)(f) - RH + lambda norm(f)_H^2). $
] <def:stab-approx-error>

$A$ is well defined with values in $[0, oo)$. Every term in the infimum is at least
$risk(L, P)(f) - RH >= 0$. Since $RH < oo$, there is some $f_0 in H$ with $risk(L, P)(f_0) < oo$, and
then $A(lambda) <= risk(L, P)(f_0) - RH + lambda norm(f_0)_H^2 < oo$. Under (S), $RH <= risk(L, P)(0) < oo$
automatically.

The second form of the definition shows what $A$ measures. To make $A(lambda)$ small, we need a function $f$
whose excess risk $risk(L, P)(f) - RH$ is small _and_ whose norm is small, measured on the scale
$lambda$. If, for some $lambda > 0$, the minimizer $f_(P,lambda)$ exists, then the infimum is attained there and
$ A(lambda) = underbrace(risk(L, P)(f_(P,lambda)) - RH, >= 0) + underbrace(lambda norm(f_(P,lambda))_H^2, >= 0). $ <eq:stab-A-at-minimizer>
Hence $A(lambda)$ bounds two quantities at once:
$ risk(L, P)(f_(P,lambda)) - RH <= A(lambda) quad "and" quad norm(f_(P,lambda))_H^2 <= A(lambda) / lambda. $ <eq:stab-two-bounds>
The first inequality explains the name. $A(lambda)$ controls how far the regularized solution is from being
optimal in $H$: it bounds the deterministic regularization error in the error analysis of
@sec:stab-outlook. The
second inequality will be the key to the behaviour of $norm(f_(P,lambda))_H$.

#remark[
  $A$ measures the approximation error _within_ $H$, relative to $RH$. The Bayes risk
  $bayes(L, P) <= RH$ may be strictly smaller, and closing the remaining gap $RH - bayes(L, P)$ is a
  question about the richness of $H$, the topic of @sec:univ. In @sec:stab-outlook both pieces will be
  combined.
]

Before proving general properties, let us compute $A$ in a model where everything is explicit.

#example(title: [A spectral model for least squares])[
  Let $L(y, t) = (y - t)^2$ be the least squares loss and let $P$ be a distribution on $X times RR$ with
  $integral y^2 dif P(x, y) < oo$. Let $f_P (x) = integral y dif P(y|x)$ be the conditional mean and
  $sigma_P^2$ the noise variance of @ex:learn-least-squares, so that by @eq:learn-ls-decomposition
  $ risk(L, P)(f) = norm(f - f_P)_(L^2(P_X))^2 + sigma_P^2 quad "for" f in L^2(P_X). $
  By Jensen's inequality, $integral f_P^2 dif P_X <= integral y^2 dif P < oo$, so $f_P in L^2(P_X)$.

  Let $J = {1, ..., m}$ or $J = NN$. Let $(e_j)_(j in J)$ be bounded measurable functions
  $X -> RR$ that are orthonormal in $L^2(P_X)$. Let $(w_j)_(j in J)$ be positive weights with
  $kappa^2 := sum_j w_j norm(e_j)_oo^2 < oo$. Define
  $ K(x, x') := sum_(j in J) w_j e_j (x) e_j (x'). $

  _The RKHS._ With $phi_j := sqrt(w_j) e_j$ we have $sum_j phi_j (x)^2 <= kappa^2$, so by
  @prop:rkhs-series the series defining $K$ converges absolutely, $abs(K(x, x')) <= kappa^2$, and
  $H = H_K = {sum_j a_j phi_j : a in ell^2(J)}$. Clearly $K$ is bounded and measurable. The family
  $(phi_j)$ is $ell^2$-independent: if $a in ell^2(J)$, then $(sqrt(w_j) a_j)_j$ is square summable
  (as $w_j = w_j norm(e_j)_(L^2(P_X))^2 <= kappa^2$), so $sum_j a_j phi_j$ also converges in $L^2(P_X)$; a
  subsequence of the partial sums converges $P_X$-almost everywhere, so the $L^2$-limit is the pointwise
  sum, and orthonormality gives $ip(sum_k a_k phi_k, e_j)_(L^2(P_X)) = sqrt(w_j) a_j$. Hence
  $sum_j a_j phi_j = 0$ forces $a = 0$, and @prop:rkhs-series gives $norm(sum_j a_j phi_j)_H = norm(a)_(ell^2)$.
  Writing $c_j := sqrt(w_j) a_j$, we obtain
  $ H = {sum_(j in J) c_j e_j : sum_j c_j^2 / w_j < oo}, quad norm(sum_j c_j e_j)_H^2 = sum_j c_j^2 / w_j, $
  where the series converge pointwise and in $L^2(P_X)$, and $c_j = ip(f, e_j)_(L^2(P_X))$ for $f in H$.
  This is the spectral picture of @prop:mercer-rkhs-spectral, but we need neither Mercer's theorem nor
  a topology on $X$: an orthonormal system in $L^2(P_X)$ suffices.

  _The risk in coordinates._ Let $beta_j := ip(f_P, e_j)_(L^2(P_X))$ and
  $delta^2 := norm(f_P)_(L^2(P_X))^2 - sum_j beta_j^2 >= 0$ (Bessel's inequality). The function
  $f_P - sum_j beta_j e_j$ is orthogonal to every $e_j$, and $delta$ is its norm. For
  $f = sum_j c_j e_j in H$, Pythagoras and Parseval in the closed span of $(e_j)$ give
  $ risk(L, P)(f) = sigma_P^2 + delta^2 + sum_(j in J) (c_j - beta_j)^2. $ <eq:stab-spectral-risk>
  Taking $c_j = beta_j$ for $j <= n$ and $c_j = 0$ otherwise (a finite sum, hence in $H$) and letting
  $n -> oo$ shows $RH = sigma_P^2 + delta^2$. The infimum is attained if and only if $c = beta$ is
  admissible, that is, if and only if $sum_j beta_j^2 \/ w_j < oo$. In that case
  $cal(M) = {sum_j beta_j e_j}$ is a singleton.

  _The regularized problem._ By @eq:stab-spectral-risk,
  $ risk(L, P, lambda)(f) = sigma_P^2 + delta^2 + sum_(j in J) ((c_j - beta_j)^2 + lambda c_j^2 / w_j). $
  The $j$-th summand is a quadratic in $c_j$. It is minimized at $c_j = w_j beta_j \/ (w_j + lambda)$, where it
  equals $lambda beta_j^2 \/ (w_j + lambda)$. These optimal coefficients are admissible, because
  $(w_j + lambda)^2 >= 4 w_j lambda$ gives
  $sum_j w_j beta_j^2 \/ (w_j + lambda)^2 <= sum_j beta_j^2 \/ (4 lambda) < oo$. Minimizing each summand
  separately therefore minimizes the sum, and
  $ f_(P,lambda) = sum_(j in J) w_j / (w_j + lambda) beta_j e_j, quad
    A(lambda) = sum_(j in J) (lambda beta_j^2) / (w_j + lambda), $ <eq:stab-spectral-A>
  $ norm(f_(P,lambda))_H^2 = sum_(j in J) (w_j beta_j^2) / (w_j + lambda)^2, quad
    risk(L, P)(f_(P,lambda)) - RH = sum_(j in J) (lambda^2 beta_j^2) / (w_j + lambda)^2. $
] <ex:stab-spectral>

The formula for $f_(P,lambda)$ shows how regularization acts. Each component $beta_j e_j$ of the target
is multiplied by the _filter factor_ $w_j \/ (w_j + lambda) in (0, 1)$. This factor is close to $1$ when
$w_j >> lambda$ and close to $w_j \/ lambda$ when $w_j << lambda$. So $lambda$ acts as a soft threshold
on the spectrum: components with large weight are kept, components with small weight are damped. Here
$T_K e_j = w_j e_j$ for the integral operator $T_K$ on $L^2(P_X)$ of @sec:mercer (integrate term by
term, which is allowed by dominated convergence since $sum_j w_j abs(e_j (x) e_j (x')) <= kappa^2$). So
@eq:stab-spectral-A reads $f_(P,lambda) = (T_K + lambda)^(-1) T_K f_P$ as an identity in $L^2(P_X)$, the
classical Tikhonov-regularized solution. The same computation, under the hypotheses of Mercer's theorem
and with the eigenvalues of $T_K$ written $lambda_j$ instead of $w_j$, is the spectral-filter example of
@sec:mercer following @prop:mercer-rkhs-spectral. There $f_P^0$ denotes the component of $f_P$ in
$Ker T_K = {e_j : j in J}^perp$, so $norm(f_P^0)_(L^2(P_X))^2$ there is our $delta^2$, and the
formula for $A(lambda)$ obtained there is @eq:stab-spectral-A. All the general results of this chapter can be checked in this example. We now make
it fully concrete.

#example(title: [Two explicit approximation error functions])[
  Let $X = [0, 1]$, $P_X$ the Lebesgue measure, $e_j (x) = sqrt(2) cos(pi j x)$ ($j in NN$, an orthonormal
  system in $L^2[0,1]$), and $w_j = j^(-2)$, so $kappa^2 = 2 sum_j j^(-2) = pi^2 \/ 3$. Let $P$ be any
  distribution with this marginal and with conditional mean $f_P = sum_j beta_j e_j$. For instance,
  $y = f_P (x) + epsilon$ with independent centred noise $epsilon$ of finite variance. Then $delta = 0$.
  We use the classical partial fraction expansion
  $sum_(j=1)^oo 1 \/ (j^2 + a^2) = (pi a coth(pi a) - 1) \/ (2 a^2)$ for $a > 0$.

  + $beta_j = j^(-1)$. Then $sum_j beta_j^2 \/ w_j = sum_j 1 = oo$, so $risk(L, P)$ has _no_ minimizer in $H$.
    With $a = lambda^(-1\/2)$,
    $ A(lambda) = sum_(j=1)^oo lambda / (1 + lambda j^2) = sum_(j=1)^oo 1 / (j^2 + 1\/lambda)
      = 1/2 (pi sqrt(lambda) coth(pi / sqrt(lambda)) - lambda) ~ pi / 2 sqrt(lambda) quad (lambda -> 0). $
  + $beta_j = j^(-2)$. Then $f_(P,H) = sum_j j^(-2) e_j in H$ with
    $norm(f_(P,H))_H^2 = sum_j j^(-2) = pi^2 \/ 6$. Using
    $1 \/ (j^2 (1 + lambda j^2)) = j^(-2) - lambda \/ (1 + lambda j^2)$,
    $ A(lambda) = sum_(j=1)^oo lambda / (j^2 (1 + lambda j^2)) = lambda pi^2 / 6 - lambda dot 1/2 (pi sqrt(lambda) coth(pi / sqrt(lambda)) - lambda). $
    The expression in brackets tends to $0$, so $A(lambda) \/ lambda -> pi^2 \/ 6 = norm(f_(P,H))_H^2$.

  The least squares loss is convex and, since $(y - t)^2 <= 2 y^2 + 2 t^2$, a $P$-integrable Nemitski
  loss, and $K$ is bounded. So (S) holds and all results of this chapter apply.

  In both cases $A(lambda) -> sum_j beta_j^2 = risk(L, P)(0) - RH$ as $lambda -> oo$. The two functions
  are shown in @fig:stab-approx-error.
] <ex:stab-explicit>

#figure(
  cetz.canvas({
    import cetz.draw: *
    plot.plot(
      size: (9, 5.5),
      x-tick-step: 0.25,
      y-tick-step: 0.5,
      x-label: $lambda$,
      y-label: none,
      x-min: 0, x-max: 1, y-min: 0, y-max: 2.2,
      legend: "inner-north-west",
      {
        plot.add(domain: (0.000001, 1), samples: 300, stab-Ab, label: [$A(lambda)$ for $beta_j = j^(-1)$])
        plot.add(domain: (0, 1), samples: 150, stab-Aa, label: [$A(lambda)$ for $beta_j = j^(-2)$])
        plot.add(
          domain: (0, 1), samples: 2, l => l * calc.pow(calc.pi, 2) / 6,
          style: (stroke: (dash: "dashed", paint: gray)),
          label: [$lambda norm(f_(P,H))_H^2$ in case (ii)],
        )
      },
    )
  }),
  caption: [The approximation error functions of @ex:stab-explicit. Both are concave, non-decreasing
    and vanish at $0$. In case (ii), where a risk minimizer exists, $A$ is tangent to the line
    $lambda norm(f_(P,H))_H^2$ at $0$. In case (i), where no minimizer exists, $A$ behaves like
    $sqrt(lambda)$ and has infinite slope at $0$.],
) <fig:stab-approx-error>

=== General properties

The picture in @fig:stab-approx-error is typical. The next result collects the general properties.

#proposition(title: [Properties of the approximation error function])[
  Let $L$ be a loss function, $H$ an RKHS on $X$ with measurable kernel, and $P$ a distribution on
  $X times Y$ with $RH < oo$. Then the approximation error function $A$ has the following properties.
  + $A(0) = 0$ and $0 <= A(lambda) <= risk(L, P)(0) - RH$ for all $lambda >= 0$ (the upper bound may be $+oo$).
  + $A$ is non-decreasing and concave on $[0, oo)$.
  + $A(theta) \/ theta <= A(lambda) \/ lambda$ for $0 < lambda <= theta$, that is, $lambda |-> A(lambda) \/ lambda$
    is non-increasing on $(0, oo)$. Together with monotonicity,
    $ A(lambda) <= A(theta) <= theta / lambda A(lambda) quad "for" 0 < lambda <= theta. $
  + $A$ is continuous on $[0, oo)$.
  + $A$ is subadditive: $A(lambda + theta) <= A(lambda) + A(theta)$ for all $lambda, theta >= 0$.
  + If there are $lambda_0 > 0$ and a function $h: (0, lambda_0] -> [0, oo)$ with
    $lim_(lambda -> 0^+) h(lambda) = 0$ and $A(lambda) <= lambda h(lambda)$ for all
    $lambda in (0, lambda_0]$, then $A(lambda) = 0$ for all $lambda >= 0$.
] <prop:stab-approx-error>

#proof[
  For $f in H$ let $a_f (lambda) := risk(L, P)(f) + lambda norm(f)_H^2$, so that
  $A(lambda) = inf_(f in H) a_f (lambda) - RH$. Each $a_f$ is either identically $+oo$ (if
  $risk(L, P)(f) = oo$) or an affine function of $lambda$ with slope $norm(f)_H^2 >= 0$.

  (i) $A(0) = inf_f risk(L, P)(f) - RH = 0$. The bounds follow from the discussion after
  @def:stab-approx-error and from choosing $f = 0$ in the infimum.

  (ii) Each $a_f$ is non-decreasing in $lambda$, hence so is their infimum. For concavity let
  $lambda, theta >= 0$ and $t in [0, 1]$. For every $f$ with $risk(L, P)(f) < oo$,
  $ a_f (t lambda + (1 - t) theta) = t a_f (lambda) + (1 - t) a_f (theta)
    >= t inf_g a_g (lambda) + (1 - t) inf_g a_g (theta), $
  and this also holds trivially if $risk(L, P)(f) = oo$. Taking the infimum over $f$ and subtracting $RH$
  gives $A(t lambda + (1 - t) theta) >= t A(lambda) + (1 - t) A(theta)$. (This is the concave
  counterpart of the fact that suprema of affine functions are convex, @lem:app-sup-affine.)

  (iii) Let $0 < lambda <= theta$. Writing $lambda = (lambda \/ theta) theta + (1 - lambda \/ theta) dot 0$,
  concavity and $A(0) = 0$ give $A(lambda) >= (lambda \/ theta) A(theta)$. This is the claim. The
  inequality $A(lambda) <= A(theta)$ is monotonicity.

  (iv) _Continuity on $(0, oo)$._ Fix $lambda_0 > 0$. By (iii), for $theta >= lambda_0$ we have
  $A(lambda_0) <= A(theta) <= (theta \/ lambda_0) A(lambda_0)$, and for $0 < lambda <= lambda_0$ we have
  $(lambda \/ lambda_0) A(lambda_0) <= A(lambda) <= A(lambda_0)$. Letting $theta arrow.b lambda_0$ and
  $lambda arrow.t lambda_0$ shows that $A$ is continuous at $lambda_0$.

  _Continuity at $0$._ This does not follow from concavity alone (see @ex:stab-concave-jump). Let
  $epsilon > 0$ and choose $f_epsilon in H$ with $risk(L, P)(f_epsilon) <= RH + epsilon$. Then for all $lambda >= 0$,
  $ 0 <= A(lambda) <= risk(L, P)(f_epsilon) - RH + lambda norm(f_epsilon)_H^2 <= epsilon + lambda norm(f_epsilon)_H^2, $
  so $limsup_(lambda -> 0^+) A(lambda) <= epsilon$. Since $epsilon$ was arbitrary, $A(lambda) -> 0 = A(0)$.
  (Alternatively, $A + RH$ is the infimum of the affine functions $a_f$, $f in H$ with
  $risk(L, P)(f) < oo$, extended to all of $RR$. This infimum is finite on $[0, oo)$, hence continuous
  there, including the end point, by @lem:app-sup-affine (iii). What rules out a jump at $0$ is thus the
  upper semicontinuity of infima of continuous functions, not concavity.)

  (v) If $lambda = 0$ or $theta = 0$, the claim is trivial because $A(0) = 0$. By symmetry we may assume
  $0 < lambda <= theta$. Applying (iii) to $theta <= lambda + theta$ gives
  $ A(lambda + theta) <= (lambda + theta) / theta A(theta) = A(theta) + lambda / theta A(theta), $
  and applying (iii) to $lambda <= theta$ gives $(lambda \/ theta) A(theta) <= A(lambda)$. Together,
  $A(lambda + theta) <= A(theta) + A(lambda)$.

  (vi) Let $theta > 0$. For $0 < lambda <= min{theta, lambda_0}$, (iii) gives
  $A(theta) \/ theta <= A(lambda) \/ lambda <= h(lambda)$. Letting $lambda -> 0^+$ yields
  $A(theta) <= 0$, hence $A(theta) = 0$. Together with $A(0) = 0$ this proves the claim.
]

Part (iii) contains a lower bound in disguise: for $0 < lambda <= 1$ we have $A(lambda) >= lambda A(1)$.
So _the approximation error can never decay faster than linearly_ unless it vanishes identically, and
(vi) says the same thing in a limit form. What does $A equiv 0$ mean? The next corollary shows that it is
the degenerate case in which regularization does nothing because the zero function is already optimal.

#corollary(title: [Degenerate and limiting behaviour of $A$])[
  Let $L$ be a continuous loss function (@def:loss-convex-continuous), $H$ an RKHS on $X$ with
  measurable kernel $K$, and $P$ a distribution with $risk(L, P)(0) < oo$. Then:
  + $lim_(lambda -> oo) A(lambda) = risk(L, P)(0) - RH$.
  + $A equiv 0$ if and only if $risk(L, P)(0) = RH$, that is, if and only if $0$ minimizes $risk(L, P)$ over $H$.
    In this case, $f = 0$ is the unique minimizer of $risk(L, P, lambda)$ for every $lambda > 0$.
  + In particular, if $A(lambda) = o(lambda)$ as $lambda -> 0^+$, then $f_(P,lambda) = 0$ for all $lambda > 0$.
] <cor:stab-trivial>

#proof[
  (i) Let $lambda_n -> oo$. By the definition of $A$ we can choose $g_n in H$ with
  $ risk(L, P)(g_n) + lambda_n norm(g_n)_H^2 <= RH + A(lambda_n) + 1/n. $
  By @prop:stab-approx-error (i), the right-hand side is at most $risk(L, P)(0) + 1\/n$, so
  $norm(g_n)_H^2 <= (risk(L, P)(0) + 1) \/ lambda_n -> 0$. Hence, for every $x in X$,
  $ abs(g_n (x)) = abs(ip(g_n, K_x)_H) <= sqrt(K(x, x)) norm(g_n)_H -> 0. $
  By continuity of $L$,
  $L(x, y, g_n (x)) -> L(x, y, 0)$ pointwise, and Fatou's lemma (@thm:app-convergence) gives
  $ risk(L, P)(0) <= liminf_(n -> oo) risk(L, P)(g_n) <= liminf_(n -> oo) (RH + A(lambda_n) + 1\/n). $
  So $liminf_n A(lambda_n) >= risk(L, P)(0) - RH$. The reverse inequality is @prop:stab-approx-error (i).
  Since $A$ is monotone, the limit exists.

  (ii) If $risk(L, P)(0) = RH$, then (i) of @prop:stab-approx-error gives $A equiv 0$. Conversely, if
  $A(1) = 0$, choose $g_n$ with $risk(L, P)(g_n) + norm(g_n)_H^2 <= RH + 1\/n$. Since
  $risk(L, P)(g_n) >= RH$, we get $norm(g_n)_H^2 <= 1\/n$ and $risk(L, P)(g_n) -> RH$. As in (i), $g_n -> 0$
  pointwise and Fatou's lemma yields $risk(L, P)(0) <= RH$. Now let $lambda > 0$. Then
  $risk(L, P, lambda)(0) = RH <= inf_f risk(L, P, lambda)(f)$, so $0$ is a minimizer. If $f$ is any
  minimizer, then $risk(L, P)(f) + lambda norm(f)_H^2 = RH <= risk(L, P)(f)$, and $risk(L, P)(f) <= RH < oo$. Hence
  $norm(f)_H = 0$.

  (iii) follows from (ii) and @prop:stab-approx-error (vi) with $h(lambda) := A(lambda) \/ lambda$.
]

#remark[
  In practice, one works with bounds of the form $A(lambda) <= c lambda^gamma$ for some $gamma in (0, 1]$.
  By @prop:stab-approx-error, the exponent $gamma = 1$ is the best possible for a non-trivial problem. In
  @cor:stab-equivalences we will see that $gamma = 1$ is achievable exactly when $risk(L, P)$ has a
  minimizer in $H$. Intermediate exponents correspond to targets that lie "between" $H$ and its closure in $L^2(P_X)$.
  In @ex:stab-spectral they correspond to _source conditions_ $sum_j beta_j^2 w_j^(-2 s) < oo$ with
  $s = gamma \/ 2$ (@ex:stab-source). Such assumptions are the starting point of learning rates
  (@sec:stab-outlook).
]

== Minimal-norm minimizers <sec:stab-min-norm>

What happens to $f_(P,lambda)$ as $lambda -> 0$? The limiting problem is to minimize $risk(L, P)$ over
$H$, and this problem may have no solution or many. In @ex:stab-explicit (i) there is no minimizer at
all. The next example shows that there may also be infinitely many.

#example(title: [A point mass: many risk minimizers])[
  Let $L$ be the least squares loss, $Y = RR$, and let $P = delta_(x_0) times.o Q$ for a point
  $x_0 in X$ and a distribution $Q$ on $RR$ with mean $m$ and finite variance $v$. Then
  $risk(L, P)(f) = integral (y - f(x_0))^2 dif Q(y) = (f(x_0) - m)^2 + v$. Put $k := K(x_0, x_0)$ and
  assume $k > 0$. (If $k = 0$, every $f in H$ vanishes at $x_0$ because $abs(f(x_0)) <= sqrt(k) norm(f)_H$,
  and everything is trivial.) The minimizers of $risk(L, P)$ over $H$ are
  $ cal(M) = {f in H : f(x_0) = m} = {f in H : ip(f, K_(x_0))_H = m}, $
  a closed affine hyperplane in $H$. It contains infinitely many functions as soon as $dim H >= 2$.

  Every $f in H$ decomposes uniquely as $f = a K_(x_0) + g$ with $a in RR$ and $g perp K_(x_0)$, that is,
  $g(x_0) = 0$. Then $f(x_0) = a k$ and $norm(f)_H^2 = a^2 k + norm(g)_H^2$. Consequently:
  - the element of $cal(M)$ of smallest norm is $(m \/ k) K_(x_0)$ (take $g = 0$);
  - $risk(L, P, lambda)(f) = (a k - m)^2 + v + lambda (a^2 k + norm(g)_H^2)$ is minimized by $g = 0$ and
    $a = m \/ (k + lambda)$, so $f_(P,lambda) = m \/ (k + lambda) dot K_(x_0)$;
  - substituting gives $A(lambda) = m^2 lambda \/ (k + lambda)$.
  As $lambda -> 0$, $f_(P,lambda) -> (m \/ k) K_(x_0)$ in $H$. Among the infinitely many risk minimizers,
  the regularized solutions select the one of minimal norm.
] <ex:stab-point-mass>

This is no accident. However small $lambda > 0$ is, the penalty $lambda norm(f)_H^2$ breaks ties between
functions of equal risk in favour of the one with smaller norm. So if the regularized solutions converge,
the natural candidate for the limit is the risk minimizer of minimal norm. The first step is to show
that this object exists.

#proposition(title: [Minimal-norm risk minimizer])[
  Let $L$ be a convex loss function, $H$ an RKHS on $X$ with measurable kernel $K$, and $P$ a distribution
  on $X times Y$ with $RH < oo$. Assume that the set $cal(M) = {f in H : risk(L, P)(f) = RH}$ of risk
  minimizers is non-empty. Then:
  + $cal(M)$ is closed and convex in $H$, and there is exactly one $f_(P,H) in cal(M)$ with
    $norm(f_(P,H))_H = min_(f in cal(M)) norm(f)_H$.
  + If $lambda > 0$ and $f_(P,lambda)$ is a minimizer of $risk(L, P, lambda)$, then
    $norm(f_(P,lambda))_H <= norm(f_(P,H))_H$.
  + $A(lambda) <= lambda norm(f_(P,H))_H^2$ for all $lambda >= 0$.
] <prop:stab-min-norm>

#proof[
  (i) _$risk(L, P)$ is lower semicontinuous on $H$._ Let $f_n -> f$ in $H$. Then
  $f_n (x) -> f(x)$ for every $x$, because $abs(f_n (x) - f(x)) <= sqrt(K(x, x)) norm(f_n - f)_H$. Since $L$ is convex,
  $L(x, y, dot)$ is continuous, so $L(x, y, f_n (x)) -> L(x, y, f(x))$ for all $(x, y)$. Fatou's lemma
  (@thm:app-convergence) gives $risk(L, P)(f) <= liminf_n risk(L, P)(f_n)$. (Alternatively, use
  @prop:loss-lsc, since pointwise convergence implies convergence in probability.)

  Consequently, $cal(M) = {f in H : risk(L, P)(f) <= RH}$ is closed, being a sublevel set of a lower
  semicontinuous function. It is convex because $risk(L, P)$ is convex (@prop:loss-convex-risk).

  _Existence._ Define $N: H -> [0, oo]$ by $N(f) := norm(f)_H$ for $f in cal(M)$ and $N(f) := +oo$
  otherwise. $N$ is convex, because $cal(M)$ is convex and the norm is convex. $N$ is lower
  semicontinuous, because each sublevel set ${N <= c} = cal(M) inter {f : norm(f)_H <= c}$ is closed.
  For any $f_0 in cal(M)$, the sublevel set ${N <= norm(f_0)_H}$ is non-empty (it contains $f_0$) and
  bounded. Since Hilbert spaces are reflexive, @lem:app-existence-minimizer shows that $N$ attains its
  minimum at some $f_(P,H)$, necessarily in $cal(M)$.

  _Uniqueness._ Let $f_1 != f_2$ be two elements of $cal(M)$ with
  $norm(f_1)_H = norm(f_2)_H = mu := min_(cal(M)) norm(dot)_H$. By convexity,
  $(f_1 + f_2) \/ 2 in cal(M)$, and by the parallelogram identity
  $ norm((f_1 + f_2)/2)_H^2 = 1/2 norm(f_1)_H^2 + 1/2 norm(f_2)_H^2 - norm((f_1 - f_2)/2)_H^2 < mu^2, $
  which contradicts the minimality of $mu$.

  (ii) Comparing the regularized risk of $f_(P,lambda)$ with that of $f_(P,H)$ gives
  $ risk(L, P)(f_(P,lambda)) + lambda norm(f_(P,lambda))_H^2
    & <= risk(L, P)(f_(P,H)) + lambda norm(f_(P,H))_H^2 \
    & = RH + lambda norm(f_(P,H))_H^2 <= risk(L, P)(f_(P,lambda)) + lambda norm(f_(P,H))_H^2. $
  The first line shows in particular that $risk(L, P)(f_(P,lambda)) < oo$. Cancelling it gives
  $norm(f_(P,lambda))_H^2 <= norm(f_(P,H))_H^2$.

  (iii) Choosing $f = f_(P,H)$ in the definition of $A$ gives
  $ A(lambda) <= risk(L, P)(f_(P,H)) - RH + lambda norm(f_(P,H))_H^2 = lambda norm(f_(P,H))_H^2. $
]

#remark[
  Part (i) is just the projection theorem in disguise: $f_(P,H)$ is the point of the non-empty closed
  convex set $cal(M)$ closest to the origin (@thm:app-projection). We have given the variational proof
  because the same pattern (convex, lower semicontinuous, bounded sublevel set) recurs throughout the
  book.
]

The unique minimizer $f_(P,H)$ is distinguished among all minimizers of $risk(L, P, 0) = risk(L, P)$.
This motivates the following convention, which is justified by @thm:stab-lambda below:
$ f_(P,0) := f_(P,H) quad "whenever" cal(M) != emptyset. $

#context-note[
  The same phenomenon is classical in linear algebra and in the theory of inverse problems. For a linear
  system $T x = y$ with a bounded operator $T$ between Hilbert spaces and $y in Ran T$, the Tikhonov
  solutions $x_alpha = (T^* T + alpha)^(-1) T^* y$ minimize $norm(T x - y)^2 + alpha norm(x)^2$. As
  $alpha -> 0$ they converge to the solution of minimal norm, $T^dagger y$, where $T^dagger$ is the
  Moore–Penrose pseudoinverse @tikhonov1977. @prop:stab-min-norm and @thm:stab-lambda are the
  nonlinear, loss-based version of this fact.
]

#example(title: [Hard-margin SVM as a limit of soft-margin SVMs])[
  Let $Y = {-1, 1}$, let $L(y, t) = max{0, 1 - y t}$ be the hinge loss, and suppose there is $f in H$
  with $y f(x) >= 1$ for $P$-almost all $(x, y)$. (For an empirical measure $P = D$, this means that the
  data are separable with margin in feature space; for a universal kernel and distinct $x_i$ this always
  holds, see @sec:univ.) Then $RH = 0$ and
  $ cal(M) = {f in H : y f(x) >= 1 "for" P"-almost all" (x, y)}, $
  so $f_(P,H)$ is the solution of $min norm(f)_H$ subject to $y f(x) >= 1$ $P$-almost surely. For
  $P = D$, this is exactly the _hard-margin support vector machine_ @cortes1995. The hinge loss satisfies
  (S) for every $P$ whenever $K$ is bounded: it is convex and $L(y, t) <= 1 + abs(t)$. Hence
  @cor:stab-equivalences below, applied with $P = D$, shows that the soft-margin SVM solutions $f_(D,lambda)$ converge in $H$ to the hard-margin solution as
  $lambda -> 0$.
] <ex:stab-hard-margin>

== Dependence on the regularization parameter <sec:stab-lambda>

We now answer Q4. Throughout this section we assume (S), so that $f_(P,lambda)$ exists and is unique for
every $lambda > 0$. We abbreviate $f_lambda := f_(P,lambda)$ when $P$ is fixed.

=== Monotonicity

Increasing $lambda$ puts more weight on the norm and less on the risk. The first lemma confirms that the
solution reacts accordingly. It also shows that each $f_lambda$ is optimal in a second, constrained sense.

#lemma(title: [Monotonicity along the regularization path])[
  Assume (S) and let $0 < lambda < theta$. Then
  + $norm(f_theta)_H <= norm(f_lambda)_H$;
  + $risk(L, P)(f_lambda) <= risk(L, P)(f_theta)$;
  + $f_lambda$ minimizes the risk over the ball of its own radius: $risk(L, P)(f) >= risk(L, P)(f_lambda)$
    for every $f in H$ with $norm(f)_H <= norm(f_lambda)_H$.
] <lem:stab-monotone>

#proof[
  By optimality of $f_lambda$ for $risk(L, P, lambda)$ and of $f_theta$ for $risk(L, P, theta)$,
  $ risk(L, P)(f_lambda) + lambda norm(f_lambda)_H^2 & <= risk(L, P)(f_theta) + lambda norm(f_theta)_H^2, \
    risk(L, P)(f_theta) + theta norm(f_theta)_H^2 & <= risk(L, P)(f_lambda) + theta norm(f_lambda)_H^2. $
  All risks are finite by @lem:stab-risk-continuity. Adding the two inequalities and cancelling the risks
  gives $(theta - lambda)(norm(f_theta)_H^2 - norm(f_lambda)_H^2) <= 0$, which is (i). The first
  inequality and (i) then give
  $ risk(L, P)(f_lambda) <= risk(L, P)(f_theta) + lambda (norm(f_theta)_H^2 - norm(f_lambda)_H^2) <= risk(L, P)(f_theta), $
  which is (ii). For (iii), let $norm(f)_H <= norm(f_lambda)_H$. Then
  $ risk(L, P)(f_lambda) + lambda norm(f_lambda)_H^2 <= risk(L, P)(f) + lambda norm(f)_H^2 <= risk(L, P)(f) + lambda norm(f_lambda)_H^2, $
  and cancelling $lambda norm(f_lambda)_H^2$ gives the claim.
]

Part (iii) means that no function in $H$ is better than $f_lambda$ in both respects, smaller norm and
smaller risk. As $lambda$ runs through $(0, oo)$, the pairs
$(risk(L, P)(f_lambda), norm(f_lambda)_H)$ trace out the _Pareto frontier_ of the two competing
objectives. Along it, the risk increases and the norm decreases (@ex:stab-ivanov-morozov).

=== Continuity in $lambda$

#theorem(title: [Continuity in the regularization parameter])[
  Let $L$ be a convex, $P$-integrable Nemitski loss and $H$ an RKHS with bounded measurable kernel $K$.
  Let $lambda in [0, oo)$ and let $(lambda_n)_(n in NN) subset (0, oo)$ with $lambda_n -> lambda$. If the
  sequence $(f_(P,lambda_n))_(n in NN)$ is bounded in $H$, then:
  - if $lambda = 0$, the risk $risk(L, P)$ has a minimizer in $H$, so $f_(P,0) = f_(P,H)$ is defined;
  - $norm(f_(P,lambda_n) - f_(P,lambda))_H -> 0$ as $n -> oo$.
] <thm:stab-lambda>

For $lambda > 0$ the boundedness hypothesis is automatic, since
$norm(f_(P,lambda_n))_H^2 <= risk(L, P)(0) \/ lambda_n$ and $lambda_n >= lambda \/ 2$ for large $n$. The
theorem is really about $lambda = 0$. There it says: as soon as the regularized solutions stay bounded,
a risk minimizer exists and they converge to the one of minimal norm.

#proof[
  _Idea:_ extract a weakly convergent subsequence, show that its limit minimizes the limiting problem
  and is therefore $f_lambda$, upgrade weak to norm convergence via convergence of the norms, and
  conclude with the subsequence principle. Write $f_n := f_(P,lambda_n)$ and $C := sup_n norm(f_n)_H < oo$.

  _Step 1: a weak limit._ Let $(f_(n_k))_k$ be an arbitrary subsequence. By @thm:app-weak-compactness (i) it
  has a further subsequence, which we again denote by $(f_(n_k))_k$, that converges weakly to some
  $f^* in H$. By fact (i) of the setting, $f_(n_k) -> f^*$ pointwise on $X$. Since
  $norm(f_(n_k))_H <= C$, @lem:stab-risk-continuity gives
  $ risk(L, P)(f_(n_k)) -> risk(L, P)(f^*). $ <eq:stab-risk-conv>
  By weak lower semicontinuity of the norm (@thm:app-weak-compactness (iii)),
  $norm(f^*)_H <= liminf_k norm(f_(n_k))_H$.

  _Step 2: $f^*$ minimizes $risk(L, P, lambda)$._ By @eq:stab-A-at-minimizer and continuity of $A$
  (@prop:stab-approx-error (iv)),
  $ risk(L, P)(f_(n_k)) + lambda_(n_k) norm(f_(n_k))_H^2 = RH + A(lambda_(n_k)) -> RH + A(lambda) = inf_(f in H) risk(L, P, lambda)(f). $ <eq:stab-value-conv>
  Since $abs(lambda_(n_k) - lambda) norm(f_(n_k))_H^2 <= abs(lambda_(n_k) - lambda) C^2 -> 0$, Step 1 gives
  $ liminf_(k -> oo) lambda_(n_k) norm(f_(n_k))_H^2 = lambda liminf_(k -> oo) norm(f_(n_k))_H^2 >= lambda norm(f^*)_H^2. $
  Together with @eq:stab-risk-conv,
  $ risk(L, P, lambda)(f^*) = risk(L, P)(f^*) + lambda norm(f^*)_H^2
    <= liminf_(k -> oo) (risk(L, P)(f_(n_k)) + lambda_(n_k) norm(f_(n_k))_H^2) = inf_(f in H) risk(L, P, lambda)(f). $
  So $f^*$ minimizes $risk(L, P, lambda)$ over $H$.

  _Step 3: identification of the limit._ If $lambda > 0$, then $f^* = f_(P,lambda)$ by uniqueness
  (@prop:reg-uniqueness). If $lambda = 0$, Step 2 says $risk(L, P)(f^*) = RH$, so $f^* in cal(M)$. In
  particular $cal(M) != emptyset$, and $f_(P,H)$ exists by @prop:stab-min-norm. By
  @prop:stab-min-norm (ii), $norm(f_n)_H <= norm(f_(P,H))_H$ for all $n$, hence
  $ norm(f^*)_H <= liminf_k norm(f_(n_k))_H <= limsup_k norm(f_(n_k))_H <= norm(f_(P,H))_H. $ <eq:stab-norm-sandwich>
  So $f^*$ is an element of $cal(M)$ of minimal norm, and $f^* = f_(P,H) = f_(P,0)$ by the uniqueness
  part of @prop:stab-min-norm. In both cases $f^* = f_(P,lambda)$.

  _Step 4: convergence of the norms._ If $lambda = 0$, @eq:stab-norm-sandwich with
  $f^* = f_(P,H)$ shows $norm(f_(n_k))_H -> norm(f^*)_H$. If $lambda > 0$, the limit in
  @eq:stab-value-conv equals $risk(L, P)(f^*) + lambda norm(f^*)_H^2$, because $f^*$ is the minimizer.
  Subtracting @eq:stab-risk-conv gives $lambda_(n_k) norm(f_(n_k))_H^2 -> lambda norm(f^*)_H^2$. Dividing
  by $lambda_(n_k) -> lambda > 0$ gives $norm(f_(n_k))_H -> norm(f^*)_H$.

  _Step 5: norm convergence of the whole sequence._ Weak convergence together with convergence of the
  norms implies norm convergence (@thm:app-radon-riesz; in a Hilbert space this is simply
  $norm(f_(n_k) - f^*)_H^2 = norm(f_(n_k))_H^2 - 2 ip(f_(n_k), f^*)_H + norm(f^*)_H^2 -> 0$). So every
  subsequence of $(f_n)$ has a further subsequence converging in norm to the _same_ element
  $f_(P,lambda)$. This forces $f_n -> f_(P,lambda)$. Otherwise there would be $epsilon > 0$ and a
  subsequence with $norm(f_(n_k) - f_(P,lambda))_H >= epsilon$ for all $k$, and this subsequence
  could have no subsequence converging to $f_(P,lambda)$.
]

#corollary(title: [When does a risk minimizer exist?])[
  Let $L$ be a convex, $P$-integrable Nemitski loss and $H$ an RKHS with bounded measurable kernel. The
  following statements are equivalent:
  + $risk(L, P)$ has a minimizer in $H$, that is, $cal(M) != emptyset$;
  + $sup_(lambda > 0) norm(f_(P,lambda))_H < oo$;
  + there is $c >= 0$ with $A(lambda) <= c lambda$ for all $lambda >= 0$.
  If they hold, then $norm(f_(P,lambda))_H <= norm(f_(P,H))_H$ and $A(lambda) <= lambda norm(f_(P,H))_H^2$
  for all $lambda > 0$, and as $lambda -> 0^+$
  $ norm(f_(P,lambda) - f_(P,H))_H -> 0 quad "and" quad A(lambda) / lambda -> norm(f_(P,H))_H^2. $
  In particular, the smallest constant $c$ in (iii) is $norm(f_(P,H))_H^2$. If they fail, then
  $norm(f_(P,lambda))_H -> oo$ and $A(lambda) \/ lambda -> oo$ as $lambda -> 0^+$.
] <cor:stab-equivalences>

#proof[
  (i) $==>$ (iii): By @prop:stab-min-norm (iii), $A(lambda) <= lambda norm(f_(P,H))_H^2$.

  (iii) $==>$ (ii): By @eq:stab-two-bounds, $norm(f_(P,lambda))_H^2 <= A(lambda) \/ lambda <= c$ for all $lambda > 0$.

  (ii) $==>$ (i): Apply @thm:stab-lambda with $lambda_n := 1\/n -> 0$. Its first conclusion is (i).

  Now assume (i)–(iii). The bounds on $norm(f_(P,lambda))_H$ and $A(lambda)$ are
  @prop:stab-min-norm (ii) and (iii). For every sequence $(lambda_n) subset (0, oo)$ with $lambda_n -> 0$, the
  sequence $(f_(P,lambda_n))$ is bounded by $norm(f_(P,H))_H$, so @thm:stab-lambda gives
  $f_(P,lambda_n) -> f_(P,H)$. Since the sequence was arbitrary, $f_(P,lambda) -> f_(P,H)$ as
  $lambda -> 0^+$. Moreover,
  $ norm(f_(P,lambda))_H^2 <= A(lambda) / lambda <= norm(f_(P,H))_H^2, $
  and the left-hand side tends to $norm(f_(P,H))_H^2$. This proves $A(lambda) \/ lambda -> norm(f_(P,H))_H^2$.
  Since $lambda |-> A(lambda) \/ lambda$ is non-increasing (@prop:stab-approx-error (iii)), its supremum is
  this limit, which is therefore the smallest admissible $c$.

  If (ii) fails, recall that $lambda |-> norm(f_(P,lambda))_H$ is non-increasing
  (@lem:stab-monotone (i)). Its limit as $lambda -> 0^+$ equals its supremum, which is $oo$. By
  @eq:stab-two-bounds, $A(lambda) \/ lambda >= norm(f_(P,lambda))_H^2 -> oo$ as well.
]

In @ex:stab-explicit both alternatives occur. In case (ii), $A(lambda) \/ lambda -> pi^2 \/ 6$. In case (i),
$norm(f_(P,lambda))_H^2 = sum_j (1 + lambda j^2)^(-2) -> oo$ and $A(lambda) \/ lambda tilde (pi \/ 2) lambda^(-1\/2) -> oo$.
Even then, $f_(P,lambda)$ converges to $f_P$ in $L^2(P_X)$ (@ex:stab-no-minimizer). The regularized
solutions still approach the best risk, but they do so by leaving every bounded subset of $H$.

The quantity $norm(f_(P,lambda))_H^2$ also has a neat interpretation: it is the slope of $A$.

#proposition(title: [The derivative of $A$])[
  Let $L$ be a convex, $P$-integrable Nemitski loss and $H$ an RKHS with bounded measurable kernel. Then
  $A$ is continuously differentiable on $(0, oo)$ with
  $ A'(lambda) = norm(f_(P,lambda))_H^2. $
  At $0$, the right derivative exists in $[0, oo]$. It equals $norm(f_(P,H))_H^2$ if $cal(M) != emptyset$
  and $+oo$ otherwise.
] <prop:stab-derivative>

#proof[
  Let $lambda, theta > 0$. Since $A(theta) + RH <= risk(L, P, theta)(f_lambda)$ and
  $A(lambda) + RH = risk(L, P, lambda)(f_lambda)$,
  $ A(theta) - A(lambda) <= risk(L, P, theta)(f_lambda) - risk(L, P, lambda)(f_lambda) = (theta - lambda) norm(f_lambda)_H^2, $
  and exchanging the roles of $lambda$ and $theta$ gives
  $A(theta) - A(lambda) >= (theta - lambda) norm(f_theta)_H^2$. Hence $(A(theta) - A(lambda)) \/ (theta - lambda)$
  lies between $norm(f_theta)_H^2$ and $norm(f_lambda)_H^2$, for $theta > lambda$ as well as for
  $theta < lambda$. By @thm:stab-lambda (the boundedness hypothesis is automatic for $lambda > 0$),
  $theta |-> f_theta$ is continuous at $lambda$, so $norm(f_theta)_H^2 -> norm(f_lambda)_H^2$ as
  $theta -> lambda$. This proves the formula for $A'$ and the continuity of $A'$. At $0$,
  $(A(lambda) - A(0)) \/ lambda = A(lambda) \/ lambda$ converges to the claimed limit by
  @cor:stab-equivalences.
]

In @ex:stab-spectral one verifies directly that
$ dif / (dif lambda) sum_(j in J) (lambda beta_j^2) / (w_j + lambda) = sum_(j in J) (w_j beta_j^2) / (w_j + lambda)^2 = norm(f_(P,lambda))_H^2. $
The proposition also explains concavity once more: $A'$ is non-increasing by @lem:stab-monotone (i).

Finally, we collect the behaviour along the whole regularization path, including $lambda -> oo$. Here
the intuition is simple: a huge penalty forces the solution to $0$.

#corollary(title: [The regularization path])[
  Let $L$ be a convex, $P$-integrable Nemitski loss and $H$ an RKHS with bounded measurable kernel. Put
  $f_(P,oo) := 0$ and equip $(0, oo]$ with its usual topology. Then:
  + the map $(0, oo] -> H$, $lambda |-> f_(P,lambda)$, is continuous;
  + the map $(0, oo] -> [0, oo)$, $lambda |-> risk(L, P)(f_(P,lambda))$, is continuous and
    non-decreasing, with $risk(L, P)(f_(P,lambda)) -> risk(L, P)(0)$ as $lambda -> oo$ and
    $risk(L, P)(f_(P,lambda)) -> RH$ as $lambda -> 0^+$;
  + $lambda |-> norm(f_(P,lambda))_H$ is continuous and non-increasing on $(0, oo]$. As $lambda -> 0^+$
    it tends to $norm(f_(P,H))_H$ if $cal(M) != emptyset$ and to $oo$ otherwise;
  + if $cal(M) != emptyset$, then with $f_(P,0) = f_(P,H)$ the map in (i) is continuous on all of $[0, oo]$.
] <cor:stab-path>

#proof[
  (i) Let $lambda_n -> lambda$ in $(0, oo]$. If $lambda < oo$, then for large $n$ we have
  $lambda \/ 2 <= lambda_n < oo$, hence $norm(f_(P,lambda_n))_H^2 <= 2 risk(L, P)(0) \/ lambda$
  (fact (ii) of the setting), and @thm:stab-lambda gives $f_(P,lambda_n) -> f_(P,lambda)$. If $lambda = oo$,
  then $norm(f_(P,lambda_n))_H^2 <= risk(L, P)(0) \/ lambda_n -> 0$ (with $f_(P,lambda_n) = 0$ if $lambda_n = oo$),
  so $f_(P,lambda_n) -> 0 = f_(P,oo)$.

  (ii) Continuity follows from (i) and the continuity of $risk(L, P)$ on $H$ (@lem:stab-risk-continuity).
  Monotonicity on $(0, oo)$ is @lem:stab-monotone (ii), and the value at $oo$ is the limit. As
  $lambda -> 0^+$, $RH <= risk(L, P)(f_(P,lambda)) <= RH + A(lambda) -> RH$ by @eq:stab-two-bounds and the
  continuity of $A$ at $0$.

  (iii) Continuity follows from (i), monotonicity from @lem:stab-monotone (i), and the behaviour at
  $0$ from @cor:stab-equivalences. (iv) is @cor:stab-equivalences.
]

Note the difference between (ii) and (iii). The _risk_ of $f_(P,lambda)$ always converges to the best
value $RH$ as $lambda -> 0$. The _functions_ $f_(P,lambda)$ converge only if a risk minimizer exists.

=== Choosing $lambda$ in practice: the L-curve <sec:stab-parameter-choice>

Everything so far concerns the population solution $f_(P,lambda)$. Its risk is non-decreasing in
$lambda$ (@cor:stab-path), so at the population level smaller $lambda$ is always better. In practice we
only have the empirical solution $f_(D,lambda)$, and then the picture changes. For small $lambda$ the
solution fits the noise in the data (overfitting, @sec:learn-overfitting). For large $lambda$ it is
pushed towards $0$ (underfitting). Its true error as a function of $lambda$ is typically U-shaped, with an
optimal value $lambda^*$ in between. The outlook (@sec:stab-outlook) makes this quantitative: the excess
risk of $f_(D,lambda)$ is bounded by the non-decreasing term $A(lambda)$ plus a term of order
$1 \/ (lambda sqrt(N))$, which decreases in $lambda$.

Since $P$ is unknown, $lambda^*$ must be estimated from the data. The standard statistical method is
cross-validation @hastie2009 @shalev2014. A second, more geometric heuristic comes from the numerical
analysis of ill-posed problems. By @lem:stab-monotone (applied to $P = D$), the empirical risk
$risk(L, D)(f_(D,lambda))$ is non-decreasing and the norm $norm(f_(D,lambda))_H$ is non-increasing in $lambda$.
Plotting the curve $lambda |-> (log "residual", log "norm")$ often produces an "L": a steep branch where
the norm explodes (small $lambda$, noise is being fitted) and a flat branch where the residual grows
(large $lambda$, signal is being suppressed). The _L-curve criterion_ of Hansen @hansen1992 picks
$lambda$ at the corner. For kernel ridge regression both coordinates are explicit.

#remark(title: [Kernel ridge regression in eigen-coordinates])[
  Let $L$ be the least squares loss, $D = ((x_1, y_1), ..., (x_N, y_N))$, and
  $bold(K) = (K(x_i, x_j))_(i,j=1)^N$ the Gram matrix. By @ex:reg-krr,
  $f_(D,lambda) = sum_i a_i K_(x_i)$, where $bold(a) = (a_1, ..., a_N)^top$ solves $(bold(K) + lambda N I) bold(a) = bold(y)$
  with $bold(y) = (y_1, ..., y_N)^top$. Diagonalize
  $1/N bold(K) = U "diag"(w_1, ..., w_N) U^top$ with $U$ orthogonal and $w_j >= 0$, and put
  $c := N^(-1\/2) U^top bold(y)$. The vector of fitted values is
  $(f_(D,lambda) (x_i))_i = bold(K) bold(a) = U "diag"(w_j \/ (w_j + lambda)) U^top bold(y)$. Hence
  $ 1/N sum_(i=1)^N (y_i - f_(D,lambda) (x_i))^2 = sum_(j=1)^N (lambda / (w_j + lambda))^2 c_j^2, quad
    norm(f_(D,lambda))_H^2 = bold(a)^top bold(K) bold(a) = sum_(j=1)^N (w_j c_j^2) / (w_j + lambda)^2, $
  exactly the formulas of @ex:stab-spectral with $beta_j$ replaced by $c_j$. Noise in the labels shows up as
  coefficients $c_j$ that do not decay, and then the norm blows up as $lambda -> 0$.
] <rem:stab-krr-spectral>

#figure(
  grid(
    columns: 2,
    gutter: 1.2em,
    cetz.canvas({
      import cetz.draw: *
      plot.plot(
        size: (5.6, 4.6),
        x-tick-step: 2,
        y-tick-step: 1,
        x-label: $log_10 lambda$,
        y-label: [$log_10$ error],
        y-min: -3.2, y-max: 0,
        {
          plot.add(stab-lams.zip(stab-pts).map(((l, p)) => (calc.log(l), calc.log(p.at(2)))))
          plot.add(
            ((calc.log(stab-lams.at(stab-best)), calc.log(stab-pts.at(stab-best).at(2))),),
            mark: "o", mark-size: 0.15, style: (stroke: none),
          )
        },
      )
      content((2.9, -1.3), [(a)])
    }),
    cetz.canvas({
      import cetz.draw: *
      plot.plot(
        size: (5.6, 4.6),
        x-tick-step: 0.5,
        y-tick-step: 0.5,
        x-label: [$log_10$ residual],
        y-label: [$log_10$ norm],
        {
          plot.add(stab-pts.map(p => (0.5 * calc.log(p.at(0)), 0.5 * calc.log(p.at(1)))))
          plot.add(
            ((0.5 * calc.log(stab-pts.at(stab-best).at(0)), 0.5 * calc.log(stab-pts.at(stab-best).at(1))),),
            mark: "o", mark-size: 0.15, style: (stroke: none),
          )
        },
      )
      content((2.9, -1.3), [(b)])
    }),
  ),
  caption: [Parameter choice for kernel ridge regression in the eigen-coordinates of
    @rem:stab-krr-spectral, with $w_j = j^(-3)$ and $c_j = s_j + 0.01 (-1)^j$ ($j <= 100$): a smooth
    signal $s_j = j^(-2)$ plus a small non-decaying perturbation. (a) The error
    $sum_j (w_j c_j \/ (w_j + lambda) - s_j)^2$ with respect to the noise-free signal, as a function of
    $lambda$ (log-log). It is U-shaped, and the dot marks the optimal $lambda^*$. (b) The L-curve
    $lambda |-> (log_10 "residual", log_10 norm(f_lambda)_H)$ for $lambda in [10^(-6), 10]$. $lambda$ grows
    from the top left to the bottom right, and the optimal $lambda^*$ from (a) lies near the corner.],
) <fig:stab-lcurve>

#context-note[
  The lecture illustrated this discussion by a sketch of the U-shaped error curve with the optimal
  parameter $lambda^*$ at its bottom (@fig:stab-lcurve (a)). It called the sketch an "L-curve". In the
  literature, the name L-curve refers to the log-log plot of residual norm against solution norm
  (@fig:stab-lcurve (b)), introduced for discrete ill-posed problems by Hansen @hansen1992. Other classical
  parameter choice rules are the discrepancy principle (choose $lambda$ such that the residual matches
  the known noise level) and generalized cross-validation @wahba1990. None of them is optimal in all
  situations. The theory of this chapter guarantees that whichever $lambda$ is chosen, the solution
  depends continuously on it (@cor:stab-path), so small errors in the choice of $lambda$ cause only small
  changes of $f_(P,lambda)$.
]

== Dependence on the distribution <sec:stab-measure>

We turn to Q8. How much does $f_(P,lambda)$ change if $P$ is replaced by another distribution $Pb$?
There are two reasons to care.

- _Learning._ We can only compute $f_(D,lambda)$, where $D$ is the empirical measure of a sample from $P$.
  If $norm(f_(P,lambda) - f_(D,lambda))_H$ can be bounded by some distance between $P$ and $D$ that
  becomes small as $N -> oo$, we have a handle on the sample error. This is carried out in
  @sec:stab-outlook.
- _Robustness._ Real data are contaminated: a small fraction of the observations may come from a
  completely different distribution (outliers, recording errors). A good method should react to a
  contamination of size $epsilon$ by a change of order $epsilon$ only.

The result is a Lipschitz estimate. Its proof combines three ingredients: the representation of
$f_(P,lambda)$ via a subgradient $h$ (@thm:reg-general-representer), the subgradient inequality for $h$
integrated against $Pb$, and the strong convexity of $lambda norm(dot)_H^2$.

=== Kernel means

We recall the $H$-valued integrals of the canonical feature map $Phi(x) = K_x$ from
@def:reg-kernel-mean. Let $Q$ be a distribution on $X times Y$, $K$ a bounded measurable kernel with RKHS
$H$, and $g in cal(L)^1(Q)$. The _kernel mean_ $EE_Q [g Phi] in H$ is the unique element of $H$ with
$ ip(u, EE_Q [g Phi])_H = integral_(X times Y) g(x, y) u(x) dif Q(x, y) quad "for all" u in H, $ <eq:stab-kernel-mean>
which exists by the Riesz representation theorem. By @lem:reg-kernel-mean, $EE_Q [g Phi]$ is the function
$x' |-> integral g(x, y) K(x', x) dif Q(x, y)$, it satisfies
$norm(EE_Q [g Phi])_H <= abs(K)_oo norm(g)_(L^1(Q))$, for an empirical measure it is
$EE_D [g Phi] = 1/N sum_(i=1)^N g(x_i, y_i) K(dot, x_i)$, and for separable $H$ it is the Bochner
integral $integral g(x, y) Phi(x) dif Q(x, y)$ (see also @thm:app-bochner-properties (iv)). We shall only
use @eq:stab-kernel-mean, which avoids all measurability questions for $H$-valued maps.

=== The stability theorem

#theorem(title: [Lipschitz dependence on the distribution])[
  Let $p in [1, oo)$ and let $p' in (1, oo]$ be its dual exponent, $1\/p + 1\/p' = 1$. Let $P$ be a
  distribution on $X times Y$, $L$ a convex, $P$-integrable Nemitski loss of order $p$, and $H$ an RKHS
  with bounded measurable kernel $K$. Let $lambda > 0$ and $B := norm(f_(P,lambda))_oo$. Then:
  + There is a measurable $h: X times Y -> RR$ with $h in cal(L)^(p')(P)$,
    $ h(x, y) in partial L(x, y, f_(P,lambda) (x)) quad "for all" (x, y) in X times Y, $
    and $f_(P,lambda) = -1/(2 lambda) EE_P [h Phi]$. Here $partial L(x, y, t)$ is the subdifferential of the
    convex function $L(x, y, dot)$ at $t$.
  + Every $h$ as in (i) satisfies, for all $(x, y) in X times Y$,
    $ abs(h(x, y)) <= 2 / (B + 1) sup_(abs(t) <= 2B + 2) L(x, y, t). $
    Consequently, $h in cal(L)^1(Pb)$ for every distribution $Pb$ on $X times Y$ for which $L$ is a
    $Pb$-integrable Nemitski loss.
  + For every such $Pb$ and every $h$ as in (i),
    $ norm(f_(P,lambda) - f_(Pb,lambda))_H <= 1/lambda norm(EE_P [h Phi] - EE_(Pb) [h Phi])_H. $
] <thm:stab-measure>

The crucial point of (iii) is that the _same_ function $h$ appears in both kernel means. It is determined
by $P$ and $lambda$ alone. The difference $f_(P,lambda) - f_(Pb,lambda)$ between two solutions of
nonlinear optimization problems is controlled by how differently $P$ and $Pb$ integrate one fixed
function $h Phi$.

#proof[
  Write $f := f_(P,lambda)$ and $overline(f) := f_(Pb,lambda)$. Recall that $s in partial phi(t)$ for a
  convex $phi: RR -> RR$ means $phi(u) >= phi(t) + s (u - t)$ for all $u in RR$. Note that
  $B <= abs(K)_oo norm(f)_H < oo$.

  (i) This is @thm:reg-general-representer (i). We stress that the subgradient inclusion holds for
  _all_ $(x, y)$, not only for $P$-almost all. This is essential, because in (iii) we shall integrate the
  subgradient inequality against $Pb$, for which a $P$-null set need not be negligible. (The subdifferential
  calculus only yields the inclusion $P$-almost everywhere; Step 5 of the proof of
  @thm:reg-general-representer repairs this on a $P$-null set without changing $EE_P [h Phi]$.)

  (ii) Fix $(x, y)$, let $phi := L(x, y, dot)$, $t := f(x)$ (so $abs(t) <= B$) and $s := h(x, y) in partial phi(t)$.
  The points $t plus.minus 1$ lie in $[-(B + 1), B + 1]$. The subgradient inequality with $u = t + 1$ and
  $u = t - 1$ gives $s <= phi(t + 1) - phi(t)$ and $-s <= phi(t - 1) - phi(t)$, so
  $abs(s) <= abs(phi|_([-(B+1), B+1]))_1$ (this is @lem:app-convex-lipschitz (iii)). By
  @lem:app-convex-lipschitz (i) with $t = B + 1$,
  $ abs(h(x, y)) <= abs(phi|_([-(B+1), B+1]))_1 <= 2 / (B + 1) sup_(abs(u) <= 2 B + 2) phi(u). $
  The supremum on the right is a measurable function of $(x, y)$, since by continuity it may be taken over
  rational $u$. If $L$ is a $Pb$-integrable Nemitski loss, say $L(x, y, u) <= overline(b)(x, y) + overline(rho)(abs(u))$
  with $overline(b) in cal(L)^1(Pb)$ and $overline(rho)$ increasing, then
  $abs(h) <= 2 (overline(b) + overline(rho)(2B + 2)) \/ (B + 1)$, which is $Pb$-integrable.

  (iii) Let $Pb$ be as in (ii). Then $overline(f)$ exists and is unique (@thm:reg-existence,
  @prop:reg-uniqueness). The subgradient inequality at $t = f(x)$ and $u = overline(f)(x)$ reads
  $ h(x, y) (overline(f)(x) - f(x)) <= L(x, y, overline(f)(x)) - L(x, y, f(x)) quad "for all" (x, y). $
  All three functions of $(x, y)$ are $Pb$-integrable. The two losses are dominated by
  $overline(b) + overline(rho)(norm(overline(f))_oo)$ and $overline(b) + overline(rho)(norm(f)_oo)$, and
  $abs(h (overline(f) - f)) <= abs(h) (norm(overline(f))_oo + norm(f)_oo)$ with $h in cal(L)^1(Pb)$.
  Integrating against $Pb$ and using @eq:stab-kernel-mean with $u = overline(f) - f in H$ gives
  $ ip(overline(f) - f, EE_(Pb) [h Phi])_H <= risk(L, Pb)(overline(f)) - risk(L, Pb)(f). $ <eq:stab-integrated-subgradient>
  Next we use that $overline(f)$ minimizes $risk(L, Pb, lambda)$, so
  $risk(L, Pb)(overline(f)) - risk(L, Pb)(f) <= lambda (norm(f)_H^2 - norm(overline(f))_H^2)$. We expand
  the norms around $f$:
  $ norm(overline(f))_H^2 - norm(f)_H^2 = 2 ip(overline(f) - f, f)_H + norm(overline(f) - f)_H^2. $
  Combining these with @eq:stab-integrated-subgradient,
  $ ip(overline(f) - f, EE_(Pb) [h Phi])_H <= -2 lambda ip(overline(f) - f, f)_H - lambda norm(overline(f) - f)_H^2. $
  By (i), $-2 lambda f = EE_P [h Phi]$, so the first term on the right equals
  $ip(overline(f) - f, EE_P [h Phi])_H$. Rearranging and applying the Cauchy–Schwarz inequality,
  $ lambda norm(overline(f) - f)_H^2 <= ip(overline(f) - f, EE_P [h Phi] - EE_(Pb) [h Phi])_H
    <= norm(overline(f) - f)_H norm(EE_P [h Phi] - EE_(Pb) [h Phi])_H. $
  If $overline(f) = f$ there is nothing to prove. Otherwise we divide by $lambda norm(overline(f) - f)_H$.
]

#intuition[
  The objective $risk(L, Pb, lambda)$ is the sum of a convex function and $lambda norm(dot)_H^2$, so it
  is _strongly_ convex: it grows at least like $lambda norm(g - overline(f))_H^2$ away from its minimizer
  (compare @thm:reg-general-representer (iii)). By @eq:stab-integrated-subgradient, the vector
  $EE_(Pb) [h Phi] + 2 lambda f = EE_(Pb) [h Phi] - EE_P [h Phi]$ is a subgradient of
  $risk(L, Pb, lambda)$ at $f$. It measures how far $f$ is from satisfying the optimality condition
  $0 in partial risk(L, Pb, lambda)(f)$. For a strongly convex function, "almost satisfying the optimality
  condition" implies "being close to the minimizer", with a factor proportional to $1 \/ lambda$. This also
  shows the price of small $lambda$: the weaker the regularization, the less stable the solution.
]

#remark(title: [A sharper constant])[
  The proof used the minimality of $overline(f)$ but not the quadratic growth of $risk(L, Pb, lambda)$
  around it, and one can gain a factor $2$. Put $Delta := overline(f) - f$ and let $theta in (0, 1)$. By
  minimality of $overline(f)$, convexity of $risk(L, Pb)$ and the identity
  $ norm((1 - theta) overline(f) + theta f)_H^2 = (1 - theta) norm(overline(f))_H^2 + theta norm(f)_H^2 - theta (1 - theta) norm(Delta)_H^2, $
  we get
  $ risk(L, Pb, lambda)(overline(f)) <= risk(L, Pb, lambda)((1 - theta) overline(f) + theta f)
    <= (1 - theta) risk(L, Pb, lambda)(overline(f)) + theta risk(L, Pb, lambda)(f) - lambda theta (1 - theta) norm(Delta)_H^2 . $
  Dividing by $theta$ and letting $theta -> 0$, then using @eq:stab-integrated-subgradient and expanding
  the norms as in the proof,
  $ lambda norm(Delta)_H^2 <= risk(L, Pb)(f) - risk(L, Pb)(overline(f)) + lambda (norm(f)_H^2 - norm(overline(f))_H^2)
    <= ip(Delta, EE_P [h Phi] - EE_(Pb) [h Phi])_H - lambda norm(Delta)_H^2 . $
  Hence $norm(f_(P,lambda) - f_(Pb,lambda))_H <= (2 lambda)^(-1) norm(EE_P [h Phi] - EE_(Pb) [h Phi])_H$.
  In the language of convex analysis, this is the strong monotonicity of the subdifferential of the
  $2 lambda$-strongly convex function $risk(L, Pb, lambda)$. All constants derived from @thm:stab-measure
  below could be halved accordingly; we keep the simpler form of (iii).
] <rem:stab-sharper-constant>

=== Lipschitz losses and robustness

For Lipschitz continuous losses the bound becomes completely explicit. Recall
(@def:loss-lipschitz) that $L$ is Lipschitz continuous with constant $abs(L)_1 < oo$ if
$abs(L(x, y, t) - L(x, y, t')) <= abs(L)_1 abs(t - t')$ for all $x, y, t, t'$. Examples are the hinge,
logistic, absolute value, Huber, $epsilon$-insensitive and pinball losses (@ex:loss-catalogue), but not the
least squares loss. As a distance between distributions we use
$ norm(P - Pb) := sup {abs(integral g dif P - integral g dif Pb) : g: X times Y -> [-1, 1] "measurable"}, $
the total variation norm of the signed measure $P - Pb$. By scaling,
$abs(integral g dif P - integral g dif Pb) <= norm(g)_oo norm(P - Pb)$ for every bounded measurable
function $g$.

#corollary(title: [Stability for Lipschitz losses])[
  Let $L$ be a convex, Lipschitz continuous loss, $H$ an RKHS with bounded measurable kernel $K$, and
  $P, Pb$ distributions on $X times Y$ with $risk(L, P)(0) < oo$ and $risk(L, Pb)(0) < oo$. Then for all
  $lambda > 0$
  $ norm(f_(P,lambda) - f_(Pb,lambda))_H <= (abs(L)_1 abs(K)_oo) / lambda norm(P - Pb)
    quad "and" quad norm(f_(P,lambda) - f_(Pb,lambda))_oo <= (abs(L)_1 abs(K)_oo^2) / lambda norm(P - Pb). $
] <cor:stab-lipschitz>

#proof[
  Since $L(x, y, t) <= L(x, y, 0) + abs(L)_1 abs(t)$, $L$ is a $P$- and $Pb$-integrable Nemitski loss of
  order $1$. Let $h$ be as in @thm:stab-measure (i) with $p = 1$. Every subgradient of the
  $abs(L)_1$-Lipschitz function $L(x, y, dot)$ has absolute value at most $abs(L)_1$
  (@lem:app-convex-lipschitz (iii)), so $abs(h) <= abs(L)_1$
  everywhere. For $u in H$ with $norm(u)_H <= 1$, the function $h u$ is bounded by $abs(L)_1 abs(K)_oo$, hence
  $ ip(u, EE_P [h Phi] - EE_(Pb) [h Phi])_H = integral h u dif P - integral h u dif Pb <= abs(L)_1 abs(K)_oo norm(P - Pb). $
  Taking the supremum over such $u$ bounds $norm(EE_P [h Phi] - EE_(Pb) [h Phi])_H$, and
  @thm:stab-measure (iii) gives the first inequality. The second follows from
  $norm(dot)_oo <= abs(K)_oo norm(dot)_H$.
]

#example(title: [Contamination])[
  Let $Pb := (1 - epsilon) P + epsilon Q$ with $epsilon in [0, 1]$ and an arbitrary distribution $Q$ with
  $risk(L, Q)(0) < oo$. This models a fraction $epsilon$ of the data coming from a contaminating source
  $Q$, for example gross outliers. Then $P - Pb = epsilon (P - Q)$ and $norm(P - Pb) <= 2 epsilon$. For
  a convex Lipschitz loss, @cor:stab-lipschitz gives
  $ norm(f_(P,lambda) - f_(Pb,lambda))_oo <= (2 epsilon abs(L)_1 abs(K)_oo^2) / lambda, $
  _independently of $Q$_. No matter how wild the outliers are (for instance, labels $y$ of enormous
  size in regression with the absolute value or Huber loss), their influence on the prediction is of
  order $epsilon \/ lambda$. For the least squares loss this is false: a single far-away point mass can
  move the solution arbitrarily far (@ex:stab-least-squares-outlier). This is the functional-analytic
  core of the robustness of SVMs with Lipschitz losses and bounded kernels
  @steinwart2008[Ch. 10]. It parallels Huber's classical robust estimation of a location parameter
  @huber1964.
] <ex:stab-contamination>

== Outlook: from stability to consistency <sec:stab-outlook>

This final section goes beyond the lecture. We show how the results of this chapter, combined with an
elementary law of large numbers in $H$, lead to a consistency theorem for regularized kernel methods.
This closes the loop that was opened in @sec:learn: we set out to find a learning method whose risk
approaches the best possible risk as the sample size grows. Every result stated below is proved in
full; references to sharper or related results are given as context.

=== The error decomposition

Let $D$ be the empirical measure of a sample $(x_1, y_1), ..., (x_N, y_N)$ drawn i.i.d. from $P$. We
view $D$ as a point of $(X times Y)^N$, distributed according to the product measure $P^N$. The
quantity of interest is the excess risk of the learned function. As in @sec:learn-roadmap, it splits into
three parts:
$ risk(L, P)(f_(D,lambda)) - bayes(L, P)
  = & underbrace(risk(L, P)(f_(D,lambda)) - risk(L, P)(f_(P,lambda)), "sample error")
    + underbrace(risk(L, P)(f_(P,lambda)) - RH, "regularization error" <= A(lambda)) \
    & + underbrace(RH - bayes(L, P), "richness of" H). $ <eq:stab-excess-decomposition>
Compared with the decomposition @eq:learn-error-decomposition for a fixed hypothesis class
(@sec:learn-remedies), the estimation error within $H$ is split into the sample error and the
regularization error, and the last term is the approximation error of the class $H$. The regularization
error is controlled by the approximation error function (@eq:stab-two-bounds) and tends to $0$ as
$lambda -> 0$ (@prop:stab-approx-error (iv)). The richness term depends only on $H$ and $P$, and it
vanishes for universal kernels (@thm:univ-bayes). The sample error is random and needs a probabilistic
argument. This is where @thm:stab-measure enters. With $Pb = D$ it gives
$ norm(f_(D,lambda) - f_(P,lambda))_H <= 1/lambda norm(EE_D [h Phi] - EE_P [h Phi])_H
  = 1/lambda norm(1/N sum_(i=1)^N h(x_i, y_i) K_(x_i) - EE_P [h Phi])_H. $
Recall from @sec:learn-overfitting that the law of large numbers holds for each _fixed_ function but not
uniformly over large classes. The learned function $f_(D,lambda)$ depends on the data, so the law of
large numbers cannot be applied to it directly. The function $h$, however, depends only on $P$ and
$lambda$. The stability theorem has thus reduced the problem to a law of large numbers for the i.i.d.
$H$-valued random variables $h(x_i, y_i) K_(x_i)$.

=== A law of large numbers in $H$

#lemma(title: [Variance of kernel means])[
  Let $K$ be a bounded measurable kernel with RKHS $H$ and $h: X times Y -> RR$ measurable with
  $integral h^2 dif P < oo$. Put $m := EE_P [h Phi]$. For $D in (X times Y)^N$ the function
  $D |-> norm(EE_D [h Phi] - m)_H^2$ is measurable, and
  $ integral norm(EE_D [h Phi] - m)_H^2 dif P^N (D)
    = 1/N (integral h(x, y)^2 K(x, x) dif P(x, y) - norm(m)_H^2) <= (abs(K)_oo^2 norm(h)_(L^2(P))^2) / N. $
] <lem:stab-variance>

#proof[
  Write $D = ((x_1, y_1), ..., (x_N, y_N))$ and $h_i := h(x_i, y_i)$. By the reproducing property, $ip(K_(x_i), K_(x_j))_H = K(x_i, x_j)$ and
  $ip(K_(x_i), m)_H = m(x_i)$. Expanding the square,
  $ Z(D) := norm(1/N sum_(i=1)^N h_i K_(x_i) - m)_H^2
    = 1/N^2 sum_(i,j=1)^N (h_i h_j K(x_i, x_j) - h_i m(x_i) - h_j m(x_j) + norm(m)_H^2). $
  This is a finite sum of measurable functions of $D$, because $h$, $K$ and $m in H$ are measurable. All
  terms are integrable: $abs(h_i h_j K(x_i, x_j)) <= abs(K)_oo^2 abs(h_i) abs(h_j)$, and
  $h in cal(L)^2(P) subset cal(L)^1(P)$.

  We compute the expectations. First, by @eq:stab-kernel-mean with $u = m$,
  $integral h(x, y) m(x) dif P(x, y) = norm(m)_H^2$. Second, for $i != j$ the pairs $(x_i, y_i)$ and
  $(x_j, y_j)$ are independent, so by Fubini's theorem
  $ integral h_i h_j K(x_i, x_j) dif P^N (D)
    & = integral h(x, y) (integral h(x', y') K(x, x') dif P(x', y')) dif P(x, y) \
    & = integral h(x, y) m(x) dif P(x, y) = norm(m)_H^2, $
  where the inner integral equals $ip(K_x, m)_H = m(x)$ by @eq:stab-kernel-mean with $u = K_x$ (and
  $K(x, x') = K_x (x')$). Hence the $N(N - 1)$ off-diagonal terms have expectation
  $norm(m)^2 - norm(m)^2 - norm(m)^2 + norm(m)^2 = 0$. The $N$ diagonal terms have expectation
  $integral h^2 K(x, x) dif P - 2 norm(m)_H^2 + norm(m)_H^2$. Dividing by $N^2$ gives the identity. The
  inequality follows from $K(x, x) <= abs(K)_oo^2$.
]

This is the familiar fact that the variance of a mean of $N$ i.i.d. variables is $1\/N$ times the
variance of one of them, now for $H$-valued variables: the cross terms vanish because the centred summands
are uncorrelated.

=== Consistency

#theorem(title: [Consistency of regularized kernel methods])[
  Let $L$ be a convex, Lipschitz continuous loss, $H$ an RKHS with bounded measurable kernel $K$, and $P$
  a distribution on $X times Y$ with $risk(L, P)(0) < oo$. Put $c_L := abs(L)_1 abs(K)_oo$.
  + For all $lambda > 0$, $N in NN$ and $delta in (0, 1)$, there is a measurable set
    $E subset (X times Y)^N$ with $P^N (E) >= 1 - delta$ such that for every $D in E$
    $ norm(f_(D,lambda) - f_(P,lambda))_H <= c_L / (lambda sqrt(N delta)) quad "and" quad
      risk(L, P)(f_(D,lambda)) - RH <= A(lambda) + c_L^2 / (lambda sqrt(N delta)). $
  + Let $(lambda_N)_(N in NN) subset (0, oo)$ satisfy $lambda_N -> 0$ and $lambda_N^2 N -> oo$. Then
    $risk(L, P)(f_(D,lambda_N)) -> RH$ in probability. More precisely, for all $epsilon > 0$ and
    $delta in (0, 1)$ there is $N_0$ such that for every $N >= N_0$ there is a measurable
    $E_N subset (X times Y)^N$ with $P^N (E_N) >= 1 - delta$ and
    $ RH <= risk(L, P)(f_(D,lambda_N)) <= RH + epsilon quad "for all" D in E_N. $
] <thm:stab-consistency>

#proof[
  (i) We may assume $c_L > 0$. Otherwise $H = {0}$ or every $L(x, y, dot)$ is constant, and in both cases
  $f_(D,lambda) = f_(P,lambda) = 0$ and $A equiv 0$, so everything is trivial. As in the proof of
  @cor:stab-lipschitz, $L$ is a $P$-integrable Nemitski loss of order $1$, and
  $abs(h) <= abs(L)_1$ for the function $h$ of @thm:stab-measure (i). In particular
  $norm(h)_(L^2(P)) <= abs(L)_1$. Let $m := EE_P [h Phi]$ and
  $E := {D : norm(EE_D [h Phi] - m)_H^2 <= c_L^2 \/ (N delta)}$. This set is measurable by
  @lem:stab-variance, and by Markov's inequality and the same lemma
  $ P^N ((X times Y)^N without E) <= (N delta) / c_L^2 integral norm(EE_D [h Phi] - m)_H^2 dif P^N (D)
    <= (N delta) / c_L^2 dot (abs(K)_oo^2 abs(L)_1^2) / N = delta. $
  Every empirical measure $D$ is a distribution for which $L$ is a $D$-integrable Nemitski loss, since
  $integral L(x, y, 0) dif D = 1/N sum_i L(x_i, y_i, 0) < oo$. So @thm:stab-measure (iii) applies with
  $Pb = D$. For $D in E$ it yields
  $ norm(f_(D,lambda) - f_(P,lambda))_H <= 1/lambda norm(EE_D [h Phi] - m)_H <= c_L / (lambda sqrt(N delta)). $
  For the risk we use the Lipschitz property and $norm(dot)_oo <= abs(K)_oo norm(dot)_H$:
  $ risk(L, P)(f_(D,lambda)) - risk(L, P)(f_(P,lambda))
    & <= integral abs(L(x, y, f_(D,lambda) (x)) - L(x, y, f_(P,lambda) (x))) dif P(x, y) \
    & <= abs(L)_1 abs(K)_oo norm(f_(D,lambda) - f_(P,lambda))_H. $
  Adding $risk(L, P)(f_(P,lambda)) - RH <= A(lambda)$ (@eq:stab-two-bounds) proves (i).

  (ii) The lower bound $RH <= risk(L, P)(f_(D,lambda_N))$ holds because $f_(D,lambda_N) in H$. Let
  $epsilon > 0$ and $delta in (0, 1)$. Since $A$ is continuous at $0$ with $A(0) = 0$
  (@prop:stab-approx-error (iv)) and $lambda_N sqrt(N) -> oo$, there is $N_0$ with
  $A(lambda_N) <= epsilon \/ 2$ and $c_L^2 \/ (lambda_N sqrt(N delta)) <= epsilon \/ 2$ for all
  $N >= N_0$. Now apply (i) with $lambda = lambda_N$.
]

Part (ii) is a consistency statement in the sense of @def:learn-consistency, with the best risk $RH$ in
$H$ in place of the Bayes risk. @def:learn-consistency presupposes that $D |-> risk(L, P)(f_(D,lambda_N))$ is
measurable. This holds, for instance, for separable $H$ (see @steinwart2008[Ch. 6]), and then (ii) says
exactly that $P^N ({D : risk(L, P)(f_(D,lambda_N)) > RH + epsilon}) -> 0$. Our formulation with the
events $E_N$ sidesteps the measurability question.

Two features of this theorem deserve emphasis. First, the hypotheses on $P$ are very weak: apart from
$risk(L, P)(0) < oo$, no smoothness of the target, no noise assumptions and no boundedness of $Y$ are
needed. Second, part (ii) uses only one property of the approximation error function: its continuity at
$0$, a fact that required a separate argument in @prop:stab-approx-error. If more is known, say $A(lambda) <= c lambda^gamma$ for some
$gamma in (0, 1]$, then (i) gives the explicit bound $c lambda^gamma + c_L^2 \/ (lambda sqrt(N delta))$.
The two terms are balanced by $lambda_N tilde N^(-1\/(2(1 + gamma)))$, which gives a rate of order
$N^(-gamma \/ (2(1 + gamma)))$. This is the U-shaped trade-off of @fig:stab-lcurve (a) in quantitative form.

These rates are far from optimal. Replacing Markov's inequality by exponential concentration
inequalities for Hilbert-space-valued random variables improves the dependence on $delta$ to
$log(1\/delta)$. Exploiting variance bounds and the eigenvalue decay of $T_K$ (@sec:mercer) leads to much
faster rates. This is the subject of the oracle inequalities in @steinwart2008[Chs. 6–7] and of the
approximation-theoretic analysis in @cucker2007. Without assumptions on $P$, however, no rate at all can
hold uniformly over all distributions @devroye1996[Ch. 7]. Consistency is the best that can be said in
full generality.

=== Algorithmic stability

@thm:stab-measure also applies when both measures are empirical. This yields a classical notion of
stability of learning algorithms.

#corollary(title: [Uniform stability])[
  Let $L$ be a convex, Lipschitz continuous loss and $H$ an RKHS with bounded measurable kernel $K$. Let
  $D$ and $D'$ be data sets of size $N$ that differ in exactly one data point. Then for all $lambda > 0$
  $ norm(f_(D,lambda) - f_(D',lambda))_H <= (2 abs(L)_1 abs(K)_oo) / (lambda N) $
  and
  $ sup_(x in X, y in Y) abs(L(x, y, f_(D,lambda) (x)) - L(x, y, f_(D',lambda) (x))) <= (2 abs(L)_1^2 abs(K)_oo^2) / (lambda N). $
] <cor:stab-uniform-stability>

#proof[
  Apply @thm:stab-measure with $P := D$ and $Pb := D'$. Both are empirical measures, and $L$ is an integrable
  Nemitski loss of order $1$ for both. Let $h$ be as in @thm:stab-measure (i) for $D$, so
  $abs(h) <= abs(L)_1$. If $D$ and $D'$ differ in the $i$-th point, $(x_i, y_i)$ versus $(x'_i, y'_i)$, then
  $ EE_D [h Phi] - EE_(D') [h Phi] = 1/N (h(x_i, y_i) K_(x_i) - h(x'_i, y'_i) K_(x'_i)), $
  whose norm is at most $2 abs(L)_1 abs(K)_oo \/ N$ because $norm(K_x)_H = sqrt(K(x, x)) <= abs(K)_oo$.
  The second estimate follows from the Lipschitz property and $norm(dot)_oo <= abs(K)_oo norm(dot)_H$.
]

Bousquet and Elisseeff @bousquet2002 showed that such _uniform stability_ of order $1 \/ N$, together
with a bound on the loss, implies that the empirical risk $risk(L, D)(f_(D,lambda))$ is, with high probability, a good estimate of
the true risk $risk(L, P)(f_(D,lambda))$. This gives an alternative route to generalization bounds that
bypasses complexity measures of the hypothesis class altogether. See also @shalev2014[Ch. 13].

=== Universal kernels and the Bayes risk

It remains to deal with the third term of @eq:stab-excess-decomposition. Here the universal kernels of
@sec:univ come in: by @thm:univ-bayes, a universal kernel on a compact metric space satisfies
$RH = bayes(L, P)$ for every continuous $P$-integrable Nemitski loss, in particular for every Lipschitz
continuous loss with $risk(L, P)(0) < oo$.

#corollary(title: [Universal consistency])[
  Let $X$ be a compact metric space with its Borel $sigma$-algebra, $K$ a universal kernel on $X$
  (@def:univ-universal) with RKHS $H$, $L$ a convex, Lipschitz continuous loss, and
  $(lambda_N) subset (0, oo)$ with $lambda_N -> 0$ and $lambda_N^2 N -> oo$. Then for _every_
  distribution $P$ on $X times Y$ with $risk(L, P)(0) < oo$, $risk(L, P)(f_(D,lambda_N)) -> bayes(L, P)$
  in probability, in the sense of @thm:stab-consistency (ii).
] <cor:stab-universal-consistency>

#proof[
  A universal kernel is continuous on the compact space $X times X$, hence bounded, and Borel measurable;
  since $X$ is separable, $borel(X times X) = borel(X) times.o borel(X)$, so $K$ is measurable in our sense.
  Thus @thm:stab-consistency (ii) applies and gives $risk(L, P)(f_(D,lambda_N)) -> RH$ in probability,
  and $RH = bayes(L, P)$ by @thm:univ-bayes (ii), since $L$ is Lipschitz continuous with
  $risk(L, P)(0) < oo$.
]

Whenever $D |-> risk(L, P)(f_(D,lambda_N))$ is measurable, the corollary says that the learning method
$D |-> f_(D,lambda_N)$ is consistent in the sense of @def:learn-consistency for every distribution $P$ with
$risk(L, P)(0) < oo$. For losses with $sup_(x, y) L(x, y, 0) < oo$, such as the hinge and the logistic
loss on $Y = {-1, 1}$, this is every distribution, so the method is universally consistent.

For the hinge loss, this says that the soft-margin SVM with a universal kernel, for example the Gaussian
kernel on a compact subset of $RR^d$ (@ex:univ-taylor), is universally consistent with respect to the hinge
risk. Since the hinge loss is _classification calibrated_, consistency for the hinge risk implies
consistency for the classification risk: the classification risk of the SVM classifier
$sign f_(D,lambda_N)$ converges in probability to the Bayes classification risk of @ex:learn-classification
@steinwart2001 @zhang2004 @bartlett2006. Proving this last step requires the theory of surrogate losses,
see @steinwart2008[Ch. 3], which is beyond the scope of these notes.

=== The guiding questions revisited

We have reached the end of the story that began in @sec:learn-roadmap. @fig:stab-questions summarizes
where each of the guiding questions was answered.

#figure(
  {
  set par(justify: false)
  table(
    columns: (1fr, 1.5fr, 1fr),
    align: (left, left, left),
    stroke: (x, y) => if y == 0 { (bottom: 0.6pt) } else { none },
    inset: (x: 5pt, y: 4pt),
    [*Question*], [*Answer*], [*Where*],
    [Q1 existence of $f_(P,lambda)$], [yes, for convex integrable Nemitski $L$ and bounded $K$], [@thm:reg-existence],
    [Q2 uniqueness], [yes, by strict convexity of $norm(dot)_H^2$], [@prop:reg-uniqueness],
    [Q3 representation], [$f_(P,lambda) = -1/(2 lambda) EE_P [h Phi]$ with $h in partial L$], [@thm:reg-general-representer],
    [Q4 dependence on $lambda$], [continuous path; converges to $f_(P,H)$ as $lambda -> 0$ if a risk minimizer exists], [@thm:stab-lambda, @cor:stab-equivalences],
    [Q5 error analysis], [error decomposition, consistency, universality], [@eq:stab-excess-decomposition, @thm:stab-consistency, @thm:univ-bayes],
    [Q6 existence of $f_(D,lambda)$], [yes, for every convex $L$], [@thm:reg-representer],
    [Q7 representation of $f_(D,lambda)$], [$f_(D,lambda) = sum_i a_i K(dot, x_i)$, with $-2 lambda N a_i in partial L$], [@thm:reg-representer, @thm:reg-general-representer],
    [Q8 relation of $f_(P,lambda)$ and $f_(D,lambda)$], [Lipschitz dependence on the distribution with constant $1 \/ lambda$], [@thm:stab-measure, @thm:stab-consistency],
  )
  },
  caption: [The guiding questions of @sec:learn-roadmap and where they are answered.],
) <fig:stab-questions>

The logic of the whole book can now be read off the error decomposition @eq:stab-excess-decomposition.
The choice of loss (@sec:loss) makes the risk a well-behaved convex functional. The RKHS (@sec:rkhs,
@sec:mercer) supplies a hypothesis space in which point evaluations are continuous and norms are
computable. Universality (@sec:univ) ensures that $H$ is rich enough for the third term to vanish.
Regularization (@sec:reg) makes the problem well posed. Stability (this chapter) controls the first two
terms: the approximation error function bounds the deterministic regularization error, and the Lipschitz
dependence on the distribution turns the random sample error into a simple law of large numbers.

== Summary

- The approximation error function $A(lambda) = inf_(f in H) risk(L, P, lambda)(f) - RH$ bounds both the
  excess risk $risk(L, P)(f_(P,lambda)) - RH$ and $lambda norm(f_(P,lambda))_H^2$. It is non-decreasing,
  concave, continuous (at $0$ by a separate argument) and subadditive. $A(lambda) \/ lambda$ is
  non-increasing, so $A$ cannot decay faster than linearly unless $A equiv 0$, which happens only if $0$
  minimizes the risk. Under (S), $A'(lambda) = norm(f_(P,lambda))_H^2$.
- If the set of risk minimizers in $H$ is non-empty, it contains a unique element $f_(P,H)$ of minimal
  norm, and $norm(f_(P,lambda))_H <= norm(f_(P,H))_H$. We set $f_(P,0) := f_(P,H)$.
- The regularization path $lambda |-> f_(P,lambda)$ is continuous on $(0, oo]$ with $f_(P,oo) = 0$. The
  norm decreases and the risk increases in $lambda$. As $lambda -> 0$ the risk tends to $RH$, and the
  functions converge to $f_(P,H)$ if a risk minimizer exists. Otherwise the norms blow up. A minimizer
  exists if and only if the norms stay bounded, if and only if $A(lambda) = O(lambda)$.
- Parameter choice balances the regularization error against the sample error. The L-curve, cross-validation
  and related rules estimate the balance point from data.
- $f_(P,lambda)$ depends Lipschitz continuously on $P$:
  $norm(f_(P,lambda) - f_(Pb,lambda))_H <= lambda^(-1) norm(EE_P [h Phi] - EE_(Pb) [h Phi])_H$ with a
  single subgradient function $h$ determined by $P$. For Lipschitz losses this gives robustness against
  contamination and uniform algorithmic stability of order $1 \/ (lambda N)$.
- With $Pb = D$ and a variance bound in $H$, this yields consistency of $f_(D,lambda_N)$ for
  $lambda_N -> 0$, $lambda_N^2 N -> oo$. For universal kernels the limit is the Bayes risk.

== Notes and further reading

The approximation error function, the minimal-norm minimizer and the continuity of the regularization
path follow Steinwart and Christmann @steinwart2008[Ch. 5], where the infinite-sample versions of SVMs
are studied in detail. Their Chapter 6 contains a basic statistical analysis of SVMs, including
consistency results that combine stability arguments of the kind presented here with concentration
inequalities. Their Chapter 10 develops the robustness theory
(influence functions, bounded kernels and Lipschitz losses) that @cor:stab-lipschitz hints at; for
classification this goes back to Christmann and Steinwart @christmann2004. The
approximation-theoretic viewpoint, including rates for $A(lambda)$ in terms of interpolation spaces
between $H$ and $L^2(P_X)$, is developed by Cucker and Zhou @cucker2007.

Tikhonov regularization and its convergence to the minimum-norm solution are classical in the theory of
ill-posed problems @tikhonov1977. The spectral formula $f_(P,lambda) = (T_K + lambda)^(-1) T_K f_P$ shows
that kernel ridge regression is a special case, and it suggests other _spectral filters_ in place of
$w \/ (w + lambda)$. The L-curve is due to Hansen @hansen1992. Generalized cross-validation for spline
smoothing is discussed by Wahba @wahba1990, and cross-validation in general by Hastie, Tibshirani and
Friedman @hastie2009.

Algorithmic stability as a route to generalization was systematized by Bousquet and Elisseeff
@bousquet2002. An accessible textbook treatment, including the connection between regularization and
stability, is Shalev-Shwartz and Ben-David @shalev2014[Ch. 13]. The consistency of SVMs with universal
kernels goes back to Steinwart @steinwart2001. The passage from surrogate risks such as the hinge risk to
the classification risk is governed by classification calibration @zhang2004 @bartlett2006. Limits on uniform
convergence rates are discussed by Devroye, Györfi and Lugosi @devroye1996.

== Exercises

#exercise(title: [Concavity does not give continuity at the boundary])[
  Show that $g: [0, oo) -> [0, oo)$ with $g(0) = 0$ and $g(lambda) = 1$ for $lambda > 0$ is concave and
  non-decreasing and satisfies @prop:stab-approx-error (iii), but is not continuous at $0$. Show that $g$
  is not upper semicontinuous at $0$, and conclude that $g + c$ is not an infimum of affine functions for
  any constant $c$ (compare @lem:app-sup-affine).
] <ex:stab-concave-jump>

#exercise(title: [Source conditions])[
  In the setting of @ex:stab-spectral, let $s in (0, 1\/2]$ and assume
  $S := sum_j beta_j^2 w_j^(-2 s) < oo$. Show that $A(lambda) <= lambda^(2 s) S$ for all $lambda > 0$.
  Conversely, show that $A(lambda) <= c lambda$ for all $lambda > 0$ implies $sum_j beta_j^2 \/ w_j <= c$.
  _Hint:_ $lambda \/ (w + lambda) <= (lambda \/ (w + lambda))^(2 s) <= (lambda \/ w)^(2 s)$. For the
  converse, apply monotone convergence to $A(lambda) \/ lambda = sum_j beta_j^2 \/ (w_j + lambda)$.
] <ex:stab-source>

#exercise(title: [Ivanov and Morozov regularization])[
  Assume (S) and let $lambda > 0$, $r := norm(f_(P,lambda))_H$ and $e := risk(L, P)(f_(P,lambda))$. Show that
  $f_(P,lambda)$ solves both constrained problems
  $ min {risk(L, P)(f) : f in H, norm(f)_H <= r} quad "and" quad min {norm(f)_H : f in H, risk(L, P)(f) <= e}. $
  Show moreover that $f_(P,lambda)$ is the unique solution of the second problem.
  _Hint:_ If $norm(f)_H < r$ and $risk(L, P)(f) <= e$, compare $risk(L, P, lambda)(f)$ with
  $risk(L, P, lambda)(f_(P,lambda))$. For uniqueness, argue as in @prop:stab-min-norm.
] <ex:stab-ivanov-morozov>

#exercise(title: [Convergence without a minimizer])[
  In @ex:stab-explicit (i), show that $f_(P,lambda) -> f_P$ in $L^2(P_X)$ as $lambda -> 0$, although
  $norm(f_(P,lambda))_H -> oo$ and $(f_(P,lambda))$ has no limit in $H$.
  _Hint:_ In @ex:stab-spectral with $delta = 0$, one has $norm(f - f_P)_(L^2(P_X))^2 = risk(L, P)(f) - RH$
  for all $f in H$. Now use @cor:stab-path (ii).
] <ex:stab-no-minimizer>

#exercise(title: [Least squares is not robust])[
  Let $L$ be the least squares loss, $K$ bounded with $K(x_0, x_0) > 0$ for some $x_0 in X$, $P$ a
  distribution with $integral y^2 dif P < oo$, $epsilon in (0, 1)$, and
  $P_(y_0) := (1 - epsilon) P + epsilon delta_((x_0, y_0))$ for $y_0 in RR$. Show that
  $sup_(y_0 in RR) norm(f_(P_(y_0), lambda))_H = oo$.
  _Hint:_ Use the integral equation
  $lambda f_(Q,lambda) = integral (y - f_(Q,lambda) (x)) K_x dif Q(x, y)$ from @eq:reg-integral-equation with
  $Q = P_(y_0)$. If the norms stayed bounded, the right-hand side would contain the term
  $epsilon y_0 K_(x_0)$, whose norm is unbounded, while all other terms stay bounded.
] <ex:stab-least-squares-outlier>

#exercise(title: [Stability for least squares with bounded labels])[
  Let $L$ be the least squares loss, $Y = [-M, M]$ for some $M > 0$, and let $P$, $Pb$ be distributions on
  $X times Y$. Show that
  the function $h$ of @thm:stab-measure can be taken as $h(x, y) = -2 (y - f_(P,lambda) (x))$ and that
  $ norm(f_(P,lambda) - f_(Pb,lambda))_H <= (2 abs(K)_oo) / lambda (M + (abs(K)_oo M) / sqrt(lambda)) norm(P - Pb). $
  _Hint:_ $risk(L, P)(0) <= M^2$ and @prop:reg-norm-bound.
] <ex:stab-least-squares>

#exercise(title: [Leave-one-out stability])[
  Let $L$ be convex and Lipschitz, $K$ bounded, $D$ a data set of size $N >= 2$, and $D^(without i)$ the
  data set with the $i$-th point removed. Show that
  $norm(f_(D,lambda) - f_(D^(without i), lambda))_H <= 2 abs(L)_1 abs(K)_oo \/ (lambda N)$.
  _Hint:_ Write $EE_D [h Phi] - EE_(D^(without i)) [h Phi]$ as $1/N h_i K_(x_i)$ plus
  $(1/N - 1/(N - 1)) sum_(j != i) h_j K_(x_j)$.
] <ex:stab-loo>
