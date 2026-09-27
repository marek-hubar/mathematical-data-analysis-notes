#import "/template.typ": *

// Chapter-local notation
#let TT = math.bb("T")
#let setdist = math.op("dist")

= Universal Kernels <sec:univ>

In @sec:rkhs we learned how a positive definite kernel $K$ determines a Hilbert space $H_K$ of
functions, and in @sec:mercer we described $H_K$ from the inside: as a subspace of $L^2(mu)$ whose
elements have rapidly decaying coefficients with respect to the eigenfunctions of an integral
operator, that is, as a space of "smooth" functions. Both chapters tell us _which_ functions belong to
$H_K$. The present chapter asks the complementary question: how _large_ is $H_K$? More precisely,
we ask when every continuous function can be approximated, uniformly and to arbitrary accuracy, by
functions from $H_K$. Kernels with this property are called _universal_.

The motivation comes directly from learning. Every kernel method we study produces a decision
function in $H_K$, for instance the regularized minimizer $f_(D, lambda)$ of @sec:reg. If the best
possible decision function (the Bayes decision function of @def:learn-bayes) is far away from
$H_K$, then no amount of data and no clever choice of the regularization parameter can make up for
it. Universality is exactly the property of the kernel that removes this obstruction simultaneously
for _all_ data-generating distributions: we will prove in @thm:univ-bayes that for a universal
kernel the smallest risk achievable in $H_K$ equals the Bayes risk. This is the part of question Q5
(@sec:learn-roadmap) that concerns the approximation error, and it is the reason why universal
kernels appear in the consistency results for support vector machines (see @sec:stab-outlook).

The main results are the following. Universal kernels separate disjoint compact sets
(@prop:univ-separation); geometrically, _every_ labelling of finitely many points becomes linearly
separable in feature space. Universal kernels have strictly positive definite Gram matrices and
injective feature maps, and universality survives restriction and normalization
(@prop:univ-properties). A Stone--Weierstrass argument (@thm:univ-criterion) yields a practical
sufficient criterion, from which we derive that the exponential, the Gaussian, and the binomial
kernels are universal (@ex:univ-taylor), and that a translation-invariant kernel on the torus is
universal if and only if all its Fourier weights are positive (@ex:univ-fourier). Linear and
polynomial kernels, by contrast, are never universal on infinite sets.

== Why ask for rich hypothesis spaces? <sec:univ-motivation>

Let $L$ be a loss, $P$ a distribution on $X times Y$, and $H$ a set of measurable functions on $X$,
our hypothesis space. As in @eq:learn-error-decomposition (@sec:learn-remedies), the excess risk of
any $f in H$ splits into two parts, provided $cal(R)^*_(L, P, H) < oo$:
$
  risk(L, P)(f) - bayes(L, P)
  = underbrace(risk(L, P)(f) - cal(R)^*_(L, P, H), "estimation error")
  + underbrace(cal(R)^*_(L, P, H) - bayes(L, P), "approximation error"),
$
where $cal(R)^*_(L, P, H) = inf_(f in H) risk(L, P)(f)$. The first part measures how well a
particular $f$, typically computed from data, performs _within_ $H$; controlling it is the business
of @sec:reg and @sec:stab. The second part is deterministic: it depends only on $P$ and $H$, and no
procedure that outputs functions in $H$ can beat it.

#example[A hypothesis space that is too small][
  Let $L$ be the least squares loss, let $P_X$ be the uniform distribution on $X = [-1, 1]$, and let
  $y = x^2 + epsilon$ with noise $epsilon$ that is independent of $x$, centred, and has finite
  variance. The Bayes decision function is the conditional mean $f_P (x) = x^2$
  (@ex:learn-least-squares). Take for $H$ the RKHS of the linear kernel $K(x, x') = x x'$, i.e.
  $H = {x |-> w x : w in RR}$. By @eq:learn-ls-decomposition,
  $
    risk(L, P)(f) - bayes(L, P) = norm(f - f_P)_(L^2 (P_X))^2
    = 1 / 2 integral_(-1)^1 (w x - x^2)^2 dif x = 1 / 5 + w^2 / 3 quad "for" f(x) = w x,
  $
  because $integral_(-1)^1 x^3 dif x = 0$. Hence $cal(R)^*_(L, P, H) - bayes(L, P) = 1 \/ 5$: whatever
  data we see, a linear model has excess risk at least $1 \/ 5$.
] <ex:univ-too-small>

Since $P$ is unknown, we would like to choose $H$ such that the approximation error vanishes for
every $P$, or at least for a very large class of distributions. What property of $H$ achieves this?
The Bayes decision function can be an essentially arbitrary measurable function, so $H$ must be able
to approximate measurable functions, in a sense strong enough that the risks converge. Two facts
from earlier chapters point the way. First, by @prop:loss-risk-continuity the risk of a continuous
$P$-integrable Nemitski loss is continuous under uniformly bounded, almost surely convergent sequences, in
particular under uniform convergence. Second, continuous functions approximate measurable ones with
respect to _every_ finite Borel measure (@lem:univ-continuous-dense below). This suggests the
requirement

#align(center)[_every continuous function on $X$ is a uniform limit of functions in $H$._]

Its great advantage is that it does not refer to $P$ at all: the supremum norm dominates every
$L^p (P_X)$-norm. For this to make sense, the functions in $H$ should themselves be continuous and
the uniform norm should be finite on continuous functions; both are guaranteed if $X$ is a compact
metric space and $K$ is continuous. Compactness also gives us the two classical tools of this
chapter, the Stone--Weierstrass theorem (@thm:app-stone-weierstrass) and the Tietze extension
theorem (@thm:app-tietze). Non-compact input spaces are discussed in the notes at the end of the
chapter.

*The price of richness.* One might object that a rich hypothesis space invites overfitting, and
this objection is correct. We will see in @cor:univ-hyperplane and @rem:univ-interpolation that
for a universal kernel every finite data set with distinct inputs can be fitted _exactly_ by some
$f in H_K$. So the
minimizer of the empirical risk over $H_K$ has zero empirical risk, exactly like the pathological
interpolant of @sec:learn-overfitting, and it typically generalizes badly. If, on the other hand,
$H_K$ is small, for instance finite-dimensional, then the approximation error is positive for many
$P$ (as in @ex:univ-too-small) and the learned functions are too simple: the method underfits.
Regularized kernel methods resolve this tension by combining a universal kernel, which makes the
approximation error vanish, with the penalty $lambda norm(f)_(H_K)^2$, which prevents overfitting.
@prop:univ-thin below makes the interplay precise: approximating a continuous function that is not
in $H_K$ necessarily requires functions of unbounded norm, and these are exactly the functions the
penalty discourages.

#intuition[
  A universal kernel is one whose feature space is rich enough to "linearize" every classification
  problem: every continuous decision boundary in $X$ becomes, up to an arbitrarily small error, a
  hyperplane in feature space. The regularizer $lambda norm(f)_(H_K)^2$ then decides how much of this
  flexibility we are willing to pay for.
]

== Definition and first examples <sec:univ-definition>

Throughout this chapter, $(X, d)$ is a nonempty compact metric space and $KK in {RR, CC}$. We write
$C(X) = C(X, KK)$ for the space of continuous functions $g: X -> KK$ with the norm
$norm(g)_oo = max_(x in X) abs(g(x))$; it is a Banach space. If $K: X times X -> KK$ is a continuous
positive definite kernel, then $K$ is bounded (as a continuous function on the compact space
$X times X$) and in particular separately continuous, so by @prop:rkhs-continuous and
@prop:rkhs-bounded,
$
  H_K subset.eq C(X) quad "and" quad norm(f)_oo <= abs(K)_oo norm(f)_(H_K) quad "for all" f in H_K.
$ <eq:univ-embedding>
It therefore makes sense to ask whether $H_K$ is a dense subspace of $C(X)$.

#definition[Universal kernel, separation][
  Let $(X, d)$ be a compact metric space and let $K: X times X -> KK$ be a continuous positive definite
  kernel with RKHS $H_K$.
  + $K$ is called *universal* if $H_K$ is dense in $(C(X), norm(dot)_oo)$, that is, if for every
    $g in C(X)$ and every $epsilon > 0$ there is an $f in H_K$ with $norm(f - g)_oo < epsilon$.
  + Let $KK = RR$. The kernel $K$ *separates* two disjoint subsets $A, B subset.eq X$ if there are
    $f in H_K$ and $a in RR$ such that
    $
      f(x) > a quad "for all" x in A quad "and" quad f(x) < a quad "for all" x in B.
    $
    We say that $K$ *separates finite sets* (respectively *compact sets*) if it separates every pair
    of disjoint finite (respectively compact) subsets of $X$.
] <def:univ-universal>

Some comments on the definition.

- Universality is a property of the pair $(K, X)$, and it only involves the topology of $X$, not the
  particular metric. The same formula can define a universal kernel on one set and a non-universal
  one on another (@ex:univ-cosh).
- Since $H_(K,0) = spn{K_x : x in X}$ is dense in $H_K$ with respect to $norm(dot)_(H_K)$
  (@thm:rkhs-moore-aronszajn) and $norm(dot)_(H_K)$ dominates $norm(dot)_oo$ up to the factor
  $abs(K)_oo$ by @eq:univ-embedding, $K$ is universal if and only if every continuous function is a
  uniform limit of finite kernel expansions $sum_(i=1)^n a_i K(dot, x_i)$. These are exactly the
  functions that kernel methods output (@thm:reg-representer).
- In the complex case, $C(X)$ consists of complex-valued functions. For real-valued kernels we always
  work with the real RKHS and real-valued $C(X)$; @ex:univ-ex-complexification shows that
  nothing changes if one passes to complex scalars.

Uniform approximation is stronger than approximation in any $L^p$-norm. To exploit this we need the
following standard fact from measure theory.

#lemma[Continuous functions are dense in $L^p$][
  Let $(X, d)$ be a metric space, $mu$ a finite measure on its Borel $sigma$-algebra, and
  $p in [1, oo)$.
  + The bounded continuous functions $C_b (X)$ are dense in $L^p (mu)$.
  + If $g: X -> RR$ is measurable with $abs(g) <= M$, then there are real-valued $g_n in C_b (X)$ with
    $abs(g_n) <= M$ and $g_n -> g$ $mu$-almost everywhere.
] <lem:univ-continuous-dense>

#proof[
  (i) Every finite Borel measure on a metric space is _closed regular_: for every Borel set $A$ and
  every $epsilon > 0$ there is a closed set $F subset.eq A$ with $mu(A without F) < epsilon$ (see
  @dudley2002[Sect. 7.1]). Given such an $F$, put $phi_n (x) := max{0, 1 - n setdist(x, F)}$ (and
  $phi_n := 0$ if $F = emptyset$). Each $phi_n$ is continuous with values in $[0, 1]$, equals $1$ on
  $F$, and $phi_n (x) -> 0$ for $x in.not F$ because $setdist(x, F) > 0$ for such $x$ ($F$ is closed).
  By dominated convergence (@thm:app-convergence), $norm(ind_F - phi_n)_(L^p (mu)) -> 0$, and
  $norm(ind_A - ind_F)_(L^p (mu))^p = mu(A without F) < epsilon$. So every indicator function
  $ind_A$ lies in the $L^p$-closure of $C_b (X)$. Since simple functions are dense in $L^p (mu)$
  @rudin1987[Thm. 3.13] and the closure of a subspace is a subspace, $C_b (X)$ is dense. In the complex case
  apply this to real and imaginary parts.

  (ii) By (i) with $p = 1$ (in the real case) there are real-valued $h_n in C_b (X)$ with $norm(h_n - g)_(L^1 (mu)) -> 0$. Passing
  to a subsequence we may assume $h_n -> g$ $mu$-almost everywhere (@thm:app-convergence). The
  clipping map $c_M (t) := max{-M, min{M, t}}$ is continuous with $c_M (g) = g$, so
  $g_n := c_M compose h_n$ is continuous, satisfies $abs(g_n) <= M$, and
  $g_n = c_M (h_n) -> c_M (g) = g$ almost everywhere.
]

#corollary[
  Let $K$ be a universal kernel on the compact metric space $X$, let $mu$ be a finite Borel measure on
  $X$ and $p in [1, oo)$. Then $H_K$ is dense in $L^p (mu)$.
] <cor:univ-lp-dense>

#proof[
  Let $g in L^p (mu)$ and $epsilon > 0$. By @lem:univ-continuous-dense there is $h in C(X)$ with
  $norm(g - h)_(L^p (mu)) < epsilon$, and by universality there is $f in H_K$ with
  $norm(h - f)_oo < epsilon$. Then
  $norm(g - f)_(L^p (mu)) <= epsilon + mu(X)^(1\/p) norm(h - f)_oo < (1 + mu(X)^(1\/p)) epsilon$.
]

=== Non-examples: finite-dimensional feature spaces

The simplest obstruction to universality is finite dimension.

#proposition[
  Let $(X, d)$ be an infinite compact metric space and $K$ a continuous positive definite kernel on
  $X$ that admits a feature map $Phi: X -> H_0$ into a finite-dimensional Hilbert space $H_0$. Then
  $dim H_K <= dim H_0 < oo$, and $K$ is not universal.
] <prop:univ-finite-dim>

#proof[
  By @prop:rkhs-feature-representation, $H_K$ is the image of the linear map
  $H_0 -> KK^X$, $w |-> ip(w, Phi(dot))_(H_0)$, so $dim H_K <= dim H_0$. On the other hand, $C(X)$ is
  infinite-dimensional: given $n$ distinct points $x_1, ..., x_n in X$, let
  $delta := 1 / 2 min_(i != j) d(x_i, x_j)$ and $g_i (x) := max{0, 1 - d(x, x_i) \/ delta}$. These
  functions are continuous and $g_i (x_j) = 1$ if $i = j$ and $0$ otherwise, so they are linearly
  independent; as $X$ is infinite, $n$ is arbitrary. A finite-dimensional subspace of a normed space
  is complete, hence closed. If $H_K$ were dense in $C(X)$, it would therefore be equal to $C(X)$,
  which is impossible for dimensional reasons.
]

#example[Linear and polynomial kernels][
  Let $X subset.eq RR^d$ be compact and infinite, $c >= 0$ and $m in NN$. The polynomial kernel
  $K(x, x') = (ip(x, x') + c)^m$ (for $m = 1$, $c = 0$ the linear kernel) is not universal on $X$. Indeed,
  by the multinomial theorem it has a feature map into $RR^M$ with $M = binom(m + d, d)$, whose
  components are multiples of the monomials of degree at most $m$ (@ex:rkhs-kernels). So
  @prop:univ-finite-dim applies; concretely, $H_K$ consists of polynomials of degree at most $m$.

  The simplest case already shows what goes wrong: for the linear kernel $K(x, x') = x x'$ on
  $X = [0, 1]$ every $f in H_K$ has the form $f(x) = w x$, so $f(0) = 0$ and
  $norm(f - 1)_oo >= abs(f(0) - 1) = 1$. The constant function $1$ cannot be approximated at all.
] <ex:univ-polynomial>

Finite dimension is not the only obstruction. The next example is a kernel with an
infinite-dimensional RKHS which nevertheless fails to be universal, together with a small
modification that repairs it.

#example[The Brownian motion kernel][
  Let $X = [0, 1]$ and $K(x, x') = min{x, x'}$. By @prop:rkhs-sobolev, $H_K$ is the space of
  absolutely continuous $f$ on $[0, 1]$ with $f(0) = 0$ and $f' in L^2 [0, 1]$, with
  $norm(f)_(H_K) = norm(f')_(L^2)$.

  - $H_K$ is dense in $L^2 [0, 1]$: it contains every polynomial $p$ with $p(0) = 0$, and these are
    dense in $L^2 [0, 1]$. (Given $g in L^2$, first approximate $g$ by some $h in C[0, 1]$
    (@lem:univ-continuous-dense), then modify $h$ on a short interval $[0, eta]$ to achieve $h(0) = 0$
    at small $L^2$-cost, and finally approximate uniformly by a polynomial $q$ (Weierstrass) and
    replace $q$ by $q - q(0)$.)
  - $K$ is not universal: $K_0 = K(dot, 0) = 0$, so $f(0) = ip(f, K_0)_(H_K) = 0$ for every
    $f in H_K$, and as in @ex:univ-polynomial the constant function $1$ has distance at least $1$
    from $H_K$.
  - The kernel $K + 1$, i.e. $(x, x') |-> min{x, x'} + 1$, is universal. Indeed, the constant kernel
    $1$ has the RKHS of constant functions, so by @prop:rkhs-sum-restriction (ii)
    $H_(K + 1) = H_K + spn{1}$, which contains all polynomials. These are dense in $C[0, 1]$ by the
    Weierstrass approximation theorem (the special case of @thm:app-stone-weierstrass for
    $X = [0, 1]$).

  So density in $L^2(mu)$ for one particular measure $mu$ is strictly weaker than universality, in
  line with @cor:univ-lp-dense.
] <ex:univ-brownian>

When $X$ is finite, universality reduces to a familiar matrix condition.

#example[Finite input spaces][
  Let $X = {x_1, ..., x_n}$ consist of $n$ distinct points. Every metric induces the discrete topology,
  every function on $X$ is continuous, and $C(X) = KK^X$ has dimension $n$. The pre-RKHS
  $H_(K,0) = spn{K_(x_1), ..., K_(x_n)}$ is finite-dimensional, hence complete, so $H_K = H_(K,0)$. A
  subspace of a finite-dimensional space is dense only if it is the whole space, so $K$ is universal
  if and only if $K_(x_1), ..., K_(x_n)$ are linearly independent. Since
  $
    norm(sum_(j=1)^n c_j K_(x_j))_(H_K)^2 = sum_(i,j=1)^n overline(c_i) c_j ip(K_(x_j), K_(x_i))_(H_K)
    = sum_(i,j=1)^n overline(c_i) c_j K(x_i, x_j),
  $
  linear independence means exactly that the Gram matrix $(K(x_i, x_j))_(i,j)$ is positive definite.
  Hence _on a finite set, a kernel is universal if and only if it is strictly positive definite._
  Universality can thus be seen as the infinite-dimensional analogue of strict positive definiteness;
  @prop:univ-properties (iii) shows that a universal kernel is always strictly positive definite.
] <ex:univ-finite>

=== Dense, but thin

A universal kernel produces a dense subspace $H_K$ of $C(X)$. It is worth stressing that $H_K$ is
nevertheless a very _small_ subspace, and that this smallness is what makes it useful for learning.

#proposition[Dense but thin][
  Let $(X, d)$ be a compact metric space and $K$ a continuous positive definite kernel on $X$.
  + If $X$ is infinite, then $H_K != C(X)$.
  + If $g in C(X) without H_K$ and $(f_n) subset.eq H_K$ satisfies $norm(f_n - g)_oo -> 0$, then
    $norm(f_n)_(H_K) -> oo$.
] <prop:univ-thin>

#proof[
  (i) Suppose $H_K = C(X)$ as sets. The inclusion $iota: H_K -> C(X)$ is then a bounded
  (@eq:univ-embedding) linear bijection between Banach spaces, so its inverse is bounded by the
  bounded inverse theorem, a consequence of the open mapping theorem @brezis2011. Moreover, $iota$
  is compact: the canonical feature map $Phi_K$ is continuous by
  @prop:rkhs-continuity-equivalences, so $Phi_K (X)$ is compact, and @prop:rkhs-compact-embedding
  shows that $iota$ maps bounded sets to relatively compact subsets of $ell^oo (X)$, hence of its
  closed subspace $C(X)$. Consequently $id_(C(X)) = iota compose iota^(-1)$ is compact, i.e. the
  closed unit ball of $C(X)$ is compact. By Riesz's lemma @brezis2011 this forces
  $dim C(X) < oo$, which contradicts the infinitude of $X$ (see the proof of
  @prop:univ-finite-dim).

  (ii) Suppose not. Then some subsequence, again denoted $(f_n)$, satisfies
  $norm(f_n)_(H_K) <= C$ for all $n$. This subsequence is bounded in $H_K$ and converges pointwise
  (even uniformly) to $g$, so @prop:rkhs-norm-convergence (iii) gives $g in H_K$, contradicting
  $g in.not H_K$. (The argument behind that result is weak compactness, @thm:app-weak-compactness.)
]

#intuition[
  $H_K$ sits inside $C(X)$ like the polynomials inside $C[0, 1]$: dense, but "thin". The unit ball of
  $H_K$ is even a relatively compact subset of $C(X)$ (@prop:rkhs-compact-embedding). A function $g$ outside
  $H_K$ can be approximated, but only by functions whose $H_K$-norm explodes as the accuracy
  improves. The regularized risk $risk(L, P)(f) + lambda norm(f)_(H_K)^2$ therefore trades accuracy of
  approximation against size of the norm. How fast the achievable accuracy improves as we allow
  larger norms is measured by the approximation error function $A(lambda)$ of @def:stab-approx-error.
]

== Separating sets <sec:univ-separation>

In binary classification we predict a label in ${-1, 1}$ by the sign of a real-valued function $f$.
Suppose the inputs of class $+1$ lie in a region $A subset.eq X$ and those of class $-1$ in a region
$B$, with $A inter B = emptyset$. A perfect classifier then needs a function that is positive on $A$
and negative on $B$. For a universal kernel such a function always exists in $H_K$, as long as $A$
and $B$ are compact, and it even keeps a safety margin.

#proposition[Separation of compact sets][
  Let $(X, d)$ be a compact metric space and $K: X times X -> RR$ a universal kernel. Then for all
  disjoint compact sets $A, B subset.eq X$ there is an $f in H_K$ with
  $
    f(x) > 1 / 2 quad "for all" x in A quad "and" quad f(x) < -1 / 2 quad "for all" x in B.
  $
  In particular, $K$ separates compact sets and hence finite sets (@def:univ-universal (ii), with
  threshold $a = 0$).
] <prop:univ-separation>

#proof[
  If $B = emptyset$, approximate the constant function $1$ within $1 \/ 2$; if $A = emptyset$,
  approximate $-1$. So let $A$ and $B$ be nonempty. For nonempty $M subset.eq X$ the function
  $x |-> setdist(x, M) = inf_(y in M) d(x, y)$ is $1$-Lipschitz, hence continuous, and it vanishes
  exactly on the closure of $M$. Define
  $
    g(x) := (setdist(x, B) - setdist(x, A)) / (setdist(x, B) + setdist(x, A)), quad x in X.
  $
  The denominator never vanishes: $setdist(x, A) = setdist(x, B) = 0$ would mean $x in A inter B$,
  since compact sets are closed. Hence $g$ is continuous, $abs(g) <= 1$, $g = 1$ on $A$ and $g = -1$
  on $B$. By universality there is $f in H_K$ with $norm(f - g)_oo < 1 \/ 2$, and then
  $f(x) > 1 - 1 \/ 2 = 1 \/ 2$ for $x in A$ and $f(x) < -1 + 1 \/ 2 = -1 \/ 2$ for $x in B$.
]

The function $g$ in the proof is a continuous "soft indicator" that jumps from $-1$ to $1$ between
$B$ and $A$. The universality of $K$ is used only once, with the fixed accuracy $1 \/ 2$. The zero
level set ${f = 0}$ of the resulting $f$ is a decision boundary between $A$ and $B$ that can be very
curved (@fig:univ-separation), although, as we show next, it is a hyperplane when viewed in feature
space.

#figure(
  cetz.canvas(length: 0.85cm, {
    import cetz.draw: *
    let blue = rgb("#3b5b92")
    let red = rgb("#a83a3a")
    let bluefill = rgb("#c9d6ee")
    let redfill = rgb("#f0cccc")
    // ---- left panel: the input space X ----
    rect((-3.3, -3.1), (3.3, 3.1), stroke: 0.5pt + luma(150), radius: 0.15)
    content((-2.85, 2.65), $X$)
    // B: an annulus
    circle((0, 0), radius: 2.6, fill: redfill, stroke: 0.8pt + red)
    circle((0, 0), radius: 1.85, fill: white, stroke: 0.8pt + red)
    // A: a blob in the middle
    hobby((-1.2, 0.3), (-0.5, 1.0), (0.3, 0.5), (1.0, 0.9), (1.1, -0.3), (0.2, -1.0), (-0.8, -0.8), close: true,
      fill: bluefill, stroke: 0.8pt + blue)
    // zero level set of f
    hobby((-1.55, 0.35), (-0.6, 1.4), (0.3, 0.95), (1.1, 1.35), (1.5, -0.3), (0.3, -1.45), (-1.15, -1.2),
      close: true, stroke: (paint: black, thickness: 1pt, dash: "dashed"))
    content((0, 0), text(fill: blue)[$A$])
    content((0, -2.25), text(fill: red)[$B$])
    line((1.1, 1.35), (2.45, 2.45), stroke: 0.4pt)
    content((2.75, 2.65), text(size: 9pt)[$f = 0$])
    content((0, 3.5), text(size: 9pt)[input space $X$])
    // ---- arrow ----
    line((3.7, 0), (5.3, 0), mark: (end: ">"), stroke: 0.8pt)
    content((4.5, 0.4), $Phi$)
    // ---- right panel: feature space ----
    let ox = 9.3
    rect((ox - 3.6, -3.1), (ox + 3.6, 3.1), stroke: 0.5pt + luma(150), radius: 0.15)
    content((ox - 3.1, 2.65), $H_0$)
    // hyperplane <w, v> = 0
    line((ox - 1.9, -2.9), (ox + 1.3, 2.9), stroke: (paint: black, thickness: 1pt, dash: "dashed"))
    // normal vector w
    line((ox - 0.3, 0), (ox + 0.75, -0.58), mark: (end: ">"), stroke: 0.8pt)
    content((ox + 0.95, -0.3), $w$)
    // Phi(A) points (on the side of w)
    for p in ((1.6, -0.3), (2.3, 0.6), (1.2, -1.6), (2.6, -1.0), (0.9, -2.4), (2.0, -2.3), (1.9, 1.7), (2.8, 1.9)) {
      circle((ox + p.at(0), p.at(1)), radius: 0.09, fill: blue, stroke: none)
    }
    // Phi(B) points
    for p in ((-1.6, 0.3), (-2.4, -0.6), (-1.3, 1.6), (-2.7, 1.2), (-0.9, 2.5), (-2.2, 2.4), (-2.2, -2.0), (-3.0, -1.6)) {
      circle((ox + p.at(0), p.at(1)), radius: 0.09, fill: red, stroke: none)
    }
    content((ox + 2.5, -2.75), text(fill: blue, size: 9pt)[$Phi(A)$])
    content((ox - 2.9, -2.75), text(fill: red, size: 9pt)[$Phi(B)$])
    content((ox + 2.35, 2.72), text(size: 9pt)[$ip(w, v) = 0$])
    content((ox, 3.5), text(size: 9pt)[feature space $H_0$])
  }),
  caption: [Separation by a universal kernel. Left: two disjoint compact sets $A$ (inside) and $B$
    (the ring around it) cannot be separated by a straight line, but the level set ${f = 0}$ of a
    suitable $f in H_K$ separates them. Right: since $f = ip(w, Phi(dot))_(H_0)$, the same boundary is
    the hyperplane ${v : ip(w, v)_(H_0) = 0}$ in feature space.],
) <fig:univ-separation>

For finite data sets, @prop:univ-separation has a striking geometric reformulation in feature space.

#corollary[Linear separability in feature space][
  Let $(X, d)$ be a compact metric space, $K: X times X -> RR$ a universal kernel, and
  $Phi: X -> H_0$ any feature map of $K$ into a real Hilbert space $H_0$. Let
  $x_1, ..., x_N in X$ and $y_1, ..., y_N in {-1, 1}$ be such that $x_i = x_j$ implies $y_i = y_j$.
  Then there is $w in H_0$ with
  $
    y_i ip(w, Phi(x_i))_(H_0) >= 1 quad "for all" i = 1, ..., N.
  $
  In words: the points $Phi(x_i)$ with label $+1$ and those with label $-1$ lie strictly on
  opposite sides of the hyperplane ${v in H_0 : ip(w, v)_(H_0) = 0}$, at distance at least
  $1 \/ norm(w)_(H_0)$ from it.
] <cor:univ-hyperplane>

#proof[
  The sets $A := {x_i : y_i = 1}$ and $B := {x_i : y_i = -1}$ are finite, hence compact, and disjoint by
  the consistency assumption on the labels. @prop:univ-separation gives $f in H_K$ with
  $y_i f(x_i) > 1 \/ 2$ for all $i$. By @prop:rkhs-feature-representation there is $w_0 in H_0$ with
  $f = ip(w_0, Phi(dot))_(H_0)$. Then $w := 2 w_0$ satisfies $y_i ip(w, Phi(x_i))_(H_0) > 1$. The
  distance of $Phi(x_i)$ to the hyperplane is $abs(ip(w, Phi(x_i))_(H_0)) \/ norm(w)_(H_0) >= 1 \/ norm(w)_(H_0)$.
]

The consistency assumption is necessary: if the same input occurs with both labels, no function
whatsoever can separate the data. @cor:univ-hyperplane says that the class of linear classifiers
$x |-> sign ip(w, Phi(x))_(H_0)$ in feature space can realize _every_ labelling of _every_ finite set
of distinct points; in the language of learning theory it shatters every finite subset of $X$, so
its VC dimension is infinite as soon as $X$ is infinite @vapnik1998 @shalev2014. This is the geometric form of the overfitting danger discussed
in @sec:univ-motivation. What saves the day is that the corollary says nothing about $norm(w)_(H_0)$.
Separating complicated labellings typically requires a large $norm(w)_(H_0)$, that is, a small
margin $1 \/ norm(w)_(H_0)$. The support vector machine of @sec:reg looks for a separating hyperplane
with a small $norm(w)_(H_0)$, i.e. a large margin, and the regularization term
$lambda norm(f)_(H_K)^2$ is exactly this preference.

== Properties of universal kernels <sec:univ-properties>

We collect the basic structural properties of universal kernels. The first is a simple lemma about
multiplying a kernel by a function, which also appeared among the construction rules of
@prop:rkhs-kernel-operations (iv).

#lemma[
  Let $X$ be a set, $K$ a positive definite kernel on $X$ with feature map $Phi: X -> H_0$, and
  $h: X -> KK$ any function. Then
  $
    K_h (x, x') := h(x) K(x, x') overline(h(x')), quad x, x' in X,
  $
  is a positive definite kernel with feature map $x |-> overline(h(x)) Phi(x)$, and
  $H_(K_h) = {h f : f in H_K}$. If $(X, d)$ is a compact metric space and $K$ and $h$ are continuous,
  with $h(x) != 0$ for all $x in X$, then $K_h$ is universal if and only if $K$ is universal.
] <lem:univ-multiplication>

#proof[
  Put $Psi(x) := overline(h(x)) Phi(x)$. Since the inner product is linear in the first and
  conjugate-linear in the second argument,
  $
    ip(Psi(x'), Psi(x))_(H_0) = overline(h(x')) h(x) ip(Phi(x'), Phi(x))_(H_0) = K_h (x, x'),
  $
  so $Psi$ is a feature map for $K_h$, and $K_h$ is positive definite (this is also
  @prop:rkhs-kernel-operations (iv)). By @prop:rkhs-feature-representation, applied to $Psi$ and to $Phi$,
  $
    H_(K_h) = {ip(w, Psi(dot))_(H_0) : w in H_0} = {h(dot) ip(w, Phi(dot))_(H_0) : w in H_0}
    = {h f : f in H_K}.
  $
  Now let $X$ be compact and $K$, $h$ continuous with $h$ nowhere zero; then $K_h$ is continuous. If
  $K$ is universal, let $g in C(X)$ and $epsilon > 0$. The function $g \/ h$ is continuous, so there
  is $f in H_K$ with $norm(f - g \/ h)_oo < epsilon \/ norm(h)_oo$, and then
  $norm(h f - g)_oo <= norm(h)_oo norm(f - g \/ h)_oo < epsilon$ with $h f in H_(K_h)$. Conversely,
  $K = (K_h)_(1 \/ h)$ with $1 \/ h$ continuous and nowhere zero, so the same argument applies.
]

#proposition[Properties of universal kernels][
  Let $(X, d)$ be a compact metric space and $K: X times X -> KK$ a universal kernel. Then:
  + every feature map $Phi: X -> H_0$ of $K$ is injective;
  + $K(x, x) > 0$ for every $x in X$;
  + $K$ is strictly positive definite: for pairwise distinct $x_1, ..., x_n in X$ the Gram matrix
    $(K(x_i, x_j))_(i,j=1)^n$ is positive definite;
  + for every nonempty closed (equivalently, compact) subset $X_0 subset.eq X$, the restriction
    $K|_(X_0 times X_0)$ is a universal kernel on $(X_0, d)$;
  + the normalized kernel
    $
      K^* (x, x') := K(x, x') / sqrt(K(x, x) K(x', x')), quad x, x' in X,
    $
    is well defined and universal, and $K^* (x, x) = 1$ for all $x in X$.
] <prop:univ-properties>

#proof[
  We first prove (iii) and deduce (i) and (ii) from it. For any feature map $Phi: X -> H_0$, any points
  $x_1, ..., x_n$, and any $c in KK^n$,
  $
    sum_(i,j=1)^n overline(c_i) c_j K(x_i, x_j) = sum_(i,j=1)^n overline(c_i) c_j ip(Phi(x_j), Phi(x_i))_(H_0)
    = norm(sum_(j=1)^n c_j Phi(x_j))_(H_0)^2 .
  $ <eq:univ-gram-norm>

  (iii) Let $x_1, ..., x_n$ be pairwise distinct and suppose the quadratic form
  @eq:univ-gram-norm vanishes for some $c in KK^n$. Applied to the canonical feature map, this says
  $sum_j c_j K_(x_j) = 0$, so for every $f in H_K$
  $
    ell(f) := sum_(j=1)^n overline(c_j) f(x_j) = ip(f, sum_(j=1)^n c_j K_(x_j))_(H_K) = 0 .
  $
  The linear functional $ell(f) = sum_j overline(c_j) f(x_j)$ is also defined and continuous on all of
  $C(X)$, since $abs(ell(f)) <= (sum_j abs(c_j)) norm(f)_oo$. It vanishes on the dense subspace $H_K$,
  hence on $C(X)$. Choosing the continuous functions $g_i$ from the proof of @prop:univ-finite-dim
  with $g_i (x_j) = 1$ for $i = j$ and $0$ otherwise, we get $overline(c_i) = ell(g_i) = 0$ for all
  $i$. So the Gram matrix, which is positive semidefinite by @prop:rkhs-kernel-properties, is
  positive definite.

  (ii) This is (iii) with $n = 1$.

  (i) Let $x != x'$ and $Phi$ be a feature map. By (iii) and @eq:univ-gram-norm with $c = (1, -1)$,
  $norm(Phi(x) - Phi(x'))_(H_0)^2 > 0$, so $Phi(x) != Phi(x')$.

  (iv) $X_0$ is compact, and $K_0 := K|_(X_0 times X_0)$ is a continuous positive definite kernel on
  $X_0$ with $H_(K_0) = {f|_(X_0) : f in H_K}$ by @prop:rkhs-sum-restriction (iv). Let $g in C(X_0)$
  and $epsilon > 0$. By the Tietze extension theorem (@thm:app-tietze), $g$ has a continuous
  extension $G in C(X)$. By universality of $K$ there is $f in H_K$ with $norm(f - G)_oo < epsilon$,
  and then $f|_(X_0) in H_(K_0)$ satisfies
  $sup_(x in X_0) abs(f(x) - g(x)) <= norm(f - G)_oo < epsilon$.

  (v) By (ii) and continuity of $K$, the function $h(x) := K(x, x)^(-1\/2)$ is well defined,
  continuous, real, and strictly positive on $X$. Since
  $K^* (x, x') = h(x) K(x, x') h(x') = K_h (x, x')$ in the notation of @lem:univ-multiplication, the
  lemma shows that $K^*$ is universal. Finally $K^* (x, x) = K(x, x) \/ K(x, x) = 1$.
]

#remark[
  Properties (i)--(iii) are _necessary_ conditions for universality, which makes them convenient
  for proving that a kernel is _not_ universal. The Brownian motion kernel of @ex:univ-brownian
  violates (ii) at $x = 0$. A kernel with a feature map satisfying $Phi(x) = Phi(-x)$ on a symmetric
  set violates (i); see @ex:univ-cosh. The normalized kernel $K^*$ in (v) has the feature map
  $x |-> Phi(x) \/ norm(Phi(x))_(H_0)$, which places all features on the unit sphere of $H_0$; the
  Gaussian kernel will turn out to be of this form.
]

#remark[Exact interpolation][
  By (iii), for pairwise distinct $x_1, ..., x_N$ the Gram matrix
  $bold(K) := (K(x_i, x_j))_(i,j=1)^N$ is invertible. Hence for arbitrary
  $bold(y) = (y_1, ..., y_N) in KK^N$ the function $f := sum_(j=1)^N a_j K(dot, x_j)$ with
  $bold(a) := bold(K)^(-1) bold(y)$ satisfies $f(x_i) = sum_j K(x_i, x_j) a_j = y_i$ for all $i$
  (compare the characterization of strict positive definiteness by interpolation in
  @prop:rkhs-strict-pd). So a universal kernel can fit every data set with distinct inputs exactly, and
  the minimum of the empirical risk over $H_K$ is zero for every loss with $L(x, y, y) = 0$. This is
  the precise sense in which unregularized empirical risk minimization over $H_K$ overfits. Kernel
  ridge regression (@ex:reg-krr) solves $(bold(K) + lambda N I) bold(a) = bold(y)$ instead; since
  $bold(K)$ is invertible, its solution $(bold(K) + lambda N I)^(-1) bold(y)$ converges to the
  interpolating coefficients $bold(K)^(-1) bold(y)$ as $lambda -> 0$.
] <rem:univ-interpolation>

== A Stone--Weierstrass criterion <sec:univ-criterion>

The definition of universality is hard to verify directly: we would have to approximate _every_
continuous function. The classical tool for such density statements is the Stone--Weierstrass theorem
(@thm:app-stone-weierstrass). In the form we use it, it says that a subalgebra of $C(X, RR)$ (a linear
subspace closed under pointwise multiplication) is dense as soon as it _separates points_ (for
$x != x'$ it contains some $a$ with $a(x) != a(x')$) and _vanishes nowhere_ (for every $x$ it contains
some $a$ with $a(x) != 0$). Both conditions are necessary: if all $a$ in the algebra satisfy
$a(x) = a(x')$ (or $a(x) = 0$), then so do their uniform limits, whereas $C(X, RR)$ contains functions
that separate $x$ from $x'$ and functions that do not vanish at $x$.
It is important for us that the algebra need not contain the constant functions: the constant $1$
need not lie in $H_K$, and for the Gaussian kernel on a set with nonempty interior it does not.

The theorem applies to _algebras_ of functions, and $H_K$ is usually not an algebra. The idea of this
section is to look at a feature map with values in $ell^2$ and to require that the span of its
_component functions_ is an algebra. Feature maps into $ell^2$ always exist for continuous kernels on
compact metric spaces. Indeed, $H_K$ is then separable (@prop:rkhs-separable), and if $(u_n)_(n in I)$
is an orthonormal basis of $H_K$ with countable $I$, then $Phi(x) := (overline(u_n (x)))_(n in I)$ is a
feature map into $ell^2 (I)$, since $K(x, x') = sum_n u_n (x) overline(u_n (x'))$, with uniform
convergence on $X times X$, by @cor:rkhs-onb-expansion. For the orthonormal basis $(sqrt(lambda_j) e_j)$ built from the
eigenpairs of the integral operator $T_K$ with respect to a finite Borel measure $mu$ with
$supp mu = X$ (@prop:mercer-rkhs-spectral), this is Mercer's expansion (@thm:mercer). Such canonical
feature maps are not very useful for our purpose, because the span of an orthonormal basis is rarely an
algebra. The strength of the following criterion is that it allows _any_ feature map into $ell^2$.

#theorem[Stone--Weierstrass criterion for universality][
  Let $(X, d)$ be a compact metric space, $I$ a countable index set, and $K: X times X -> RR$ a
  continuous kernel with a feature map $Phi: X -> ell^2 (I)$ (real sequences), i.e.
  $
    K(x, x') = ip(Phi(x'), Phi(x))_(ell^2 (I)) = sum_(n in I) Phi_n (x) Phi_n (x'), quad
    Phi(x) = (Phi_n (x))_(n in I).
  $
  Assume that
  + $Phi$ is injective,
  + $K(x, x) > 0$ for all $x in X$, and
  + the linear span $cal(A) := spn{Phi_n : n in I}$ of the component functions is an algebra.
  Then $K$ is universal.
] <thm:univ-criterion>

#proof[
  _Step 1: $cal(A) subset.eq C(X, RR)$._ Since $K$ is continuous, so is $Phi$
  (@prop:rkhs-continuity-equivalences), and hence so is each component
  $Phi_n = ip(Phi(dot), delta_n)_(ell^2 (I))$, where $delta_n$ is the $n$-th unit sequence.

  _Step 2: $cal(A) subset.eq H_K$._ An element of $cal(A)$ has the form $a = sum_(n in F) c_n Phi_n$
  with a finite set $F subset.eq I$ and $c_n in RR$. With $w := sum_(n in F) c_n delta_n in ell^2 (I)$
  we have $a(x) = ip(w, Phi(x))_(ell^2 (I))$, so $a in H_K$ by @prop:rkhs-feature-representation.

  _Step 3: $cal(A)$ is dense in $C(X, RR)$._ By assumption (iii), $cal(A)$ is a subalgebra of
  $C(X, RR)$. It separates points: if $x != x'$, then $Phi(x) != Phi(x')$ by (i), so
  $Phi_n (x) != Phi_n (x')$ for some $n in I$. It vanishes nowhere: $sum_n Phi_n (x)^2 = K(x, x) > 0$
  by (ii), so $Phi_n (x) != 0$ for some $n$. By the Stone--Weierstrass theorem
  (@thm:app-stone-weierstrass (i)), $cal(A)$ is dense.

  Since $cal(A) subset.eq H_K subset.eq C(X, RR)$, the space $H_K$ is dense as well.
]

#remark[On the hypotheses][
  + Hypotheses (i) and (ii) are necessary for universality by @prop:univ-properties. Hypothesis
    (iii) is not: the Gaussian kernel (@ex:univ-taylor) is universal, but on a set $X$ with nonempty
    interior its natural feature map has components $e^(-norm(x)^2 \/ sigma^2) x^j$ (up to positive
    constants), whose span is not closed under multiplication: the square of the component with
    $j = 0$ is a multiple of $e^(-2 norm(x)^2 \/ sigma^2)$, which is not of the form
    $e^(-norm(x)^2 \/ sigma^2) p(x)$ with a polynomial $p$ on any open set. We will obtain its universality from the criterion by way of the normalization
    property @prop:univ-properties (v).
  + Note that we do not need $H_K$ itself to be an algebra; only the span of the components, which is
    a (usually non-closed) subspace of $H_K$.
  + _Complex version._ Let $KK = CC$ and $Phi: X -> ell^2 (I)$ with complex components. Now
    @prop:rkhs-feature-representation gives $ip(w, Phi(x))_(ell^2) = sum_n w_n overline(Phi_n (x))$,
    so $H_K$ contains the conjugates $overline(a)$ of all $a in cal(A)$. If $cal(A)$ is an algebra that
    is in addition closed under complex conjugation, separates points, and vanishes nowhere, then
    $cal(A) = overline(cal(A)) subset.eq H_K$ and $cal(A)$ is dense in $C(X, CC)$ by the complex
    Stone--Weierstrass theorem (@thm:app-stone-weierstrass (ii)). Closure under conjugation cannot be dropped; see @rem:univ-complex-taylor.
]

== Taylor kernels <sec:univ-taylor>

We now apply the criterion to kernels of the form $K(x, x') = f(ip(x, x'))$ on subsets of $RR^d$,
where $f$ is given by a power series with nonnegative coefficients. For finitely many nonzero
coefficients these are the polynomial kernels of @ex:univ-polynomial, which are not universal. The
point of the next result is that _infinitely_ many positive coefficients, in fact all of them, make
the kernel universal.

For $0 < r <= oo$ let $B_(sqrt(r)) := {x in RR^d : norm(x) < sqrt(r)}$ denote the open ball of
radius $sqrt(r)$ (with $B_oo = RR^d$). We use multi-index notation: for $j = (j_1, ..., j_d) in NN_0^d$
let $abs(j) := j_1 + dots.c + j_d$, $x^j := x_1^(j_1) dots.c x_d^(j_d)$, and
$c_j := abs(j)! \/ (j_1 ! dots.c j_d !)$. The multinomial theorem then reads
$
  ip(x, x')^n = (sum_(i=1)^d x_i x'_i)^n = sum_(abs(j) = n) c_j x^j x'^j, quad n in NN_0 .
$ <eq:univ-multinomial>
That $K$ below is positive definite also follows from the power-series rule
@prop:rkhs-kernel-operations (vi); what we need here in addition is an explicit feature map.

#proposition[Taylor kernels][
  Let $0 < r <= oo$ and let $f(t) = sum_(n=0)^oo a_n t^n$ be a power series with $a_n >= 0$ for all
  $n$ that converges for $abs(t) < r$. Then
  $
    K(x, x') := f(ip(x, x')) = sum_(n=0)^oo a_n ip(x, x')^n, quad x, x' in B_(sqrt(r)),
  $
  is a continuous positive definite kernel on $B_(sqrt(r))$ with the feature map
  $
    Phi: B_(sqrt(r)) -> ell^2 (NN_0^d), quad Phi(x) := (sqrt(a_(abs(j)) c_j) x^j)_(j in NN_0^d).
  $
  If $a_n > 0$ for all $n in NN_0$, then the restriction of $K$ to $X times X$ is universal for every
  nonempty compact set $X subset B_(sqrt(r))$.
] <prop:univ-taylor>

#proof[
  _Convergence and feature map._ Let $x, x' in B_(sqrt(r))$. By the Cauchy--Schwarz inequality,
  $abs(ip(x, x')) <= norm(x) norm(x') < r$, so $K(x, x')$ is well defined. The family $(a_(abs(j)) c_j x^j x'^j)_(j in NN_0^d)$
  is absolutely summable, since, by @eq:univ-multinomial (applied to the vectors
  $(abs(x_i))_i$, $(abs(x'_i))_i$) and Cauchy--Schwarz,
  $
    sum_(j in NN_0^d) a_(abs(j)) c_j abs(x^j x'^j) = sum_(n=0)^oo a_n (sum_(i=1)^d abs(x_i x'_i))^n
    <= sum_(n=0)^oo a_n (norm(x) norm(x'))^n < oo,
  $
  where the last series converges because $0 <= norm(x) norm(x') < r$ and $a_n >= 0$. Absolutely
  summable families may be summed in any order, so, using @eq:univ-multinomial again,
  $
    K(x, x') = sum_(n=0)^oo a_n sum_(abs(j) = n) c_j x^j x'^j = sum_(j in NN_0^d) a_(abs(j)) c_j x^j x'^j
    = sum_(j in NN_0^d) Phi_j (x) Phi_j (x').
  $
  With $x' = x$ this shows $norm(Phi(x))_(ell^2)^2 = K(x, x) = f(norm(x)^2) < oo$, so $Phi(x) in
  ell^2 (NN_0^d)$, and the identity says $K(x, x') = ip(Phi(x'), Phi(x))_(ell^2)$. Hence $K$ is a
  positive definite kernel with feature map $Phi$. It is continuous as the composition of the
  continuous maps $(x, x') |-> ip(x, x')$ and $f$ (a power series is continuous inside its interval of
  convergence).

  _Universality._ Let $a_n > 0$ for all $n$ and let $X subset B_(sqrt(r))$ be nonempty and compact.
  The restriction $Phi|_X$ is a feature map of $K|_(X times X)$ with values in $ell^2 (NN_0^d)$; we
  check the hypotheses of @thm:univ-criterion.
  (i) For the unit multi-indices $delta_i in NN_0^d$ we have $c_(delta_i) = 1$, so
  $Phi_(delta_i) (x) = sqrt(a_1) x_i$. Since
  $a_1 > 0$, $Phi(x) = Phi(x')$ implies $x_i = x'_i$ for all $i$, i.e. $x = x'$.
  (ii) $K(x, x) = sum_n a_n norm(x)^(2n) >= a_0 > 0$.
  (iii) Since $a_(abs(j)) c_j > 0$ for every $j$, the span of the components $Phi_j|_X$ is the span of
  all monomials $x^j|_X$, i.e. the space of (restrictions to $X$ of) polynomials in $d$ variables.
  It is an algebra.
  By @thm:univ-criterion, $K|_(X times X)$ is universal.
]

#example[Exponential, Gaussian, and binomial kernels][
  Let $X subset.eq RR^d$ be nonempty and compact.
  + The *exponential kernel* $K(x, x') = exp(gamma ip(x, x'))$ with $gamma > 0$ is universal on $X$.
    Here $f(t) = e^(gamma t) = sum_n gamma^n t^n \/ n!$ has positive coefficients and $r = oo$.
  + The *Gaussian kernel*
    $
      K_sigma (x, x') = exp(- norm(x - x')^2 / sigma^2), quad sigma > 0,
    $
    is universal on $X$, for every width $sigma > 0$. Indeed, let $K$ be the exponential kernel with
    $gamma = 2 \/ sigma^2$, which is universal by (i). Then $K(x, x) = exp(2 norm(x)^2 \/ sigma^2)$, and
    its normalization is
    $
      K(x, x') / sqrt(K(x, x) K(x', x'))
      = exp((2 ip(x, x') - norm(x)^2 - norm(x')^2) / sigma^2) = exp(- norm(x - x')^2 / sigma^2) .
    $
    So $K_sigma = K^*$ is universal by @prop:univ-properties (v). (This is the same factorization
    that proved positive definiteness in @ex:rkhs-gaussian.)
  + The *binomial kernel* $K(x, x') = (1 - ip(x, x'))^(-alpha)$ with $alpha > 0$ is universal on every
    compact $X$ contained in the _open_ unit ball $B_1$. Here
    $
      f(t) = (1 - t)^(-alpha) = sum_(n=0)^oo (alpha (alpha + 1) dots.c (alpha + n - 1)) / (n!) t^n,
      quad abs(t) < 1,
    $
    by the binomial series; all coefficients are positive (the coefficient for $n = 0$ is $1$), and
    $r = 1$. For $alpha = 1$ this is $K(x, x') = 1 \/ (1 - ip(x, x'))$. The restriction to the open
    ball is essential: on the unit sphere, $K(x, x) = (1 - norm(x)^2)^(-alpha)$ is not even defined.
] <ex:univ-taylor>

The Gaussian kernel illustrates @prop:univ-thin well. Its RKHS consists of very smooth functions (they
extend to entire functions on $CC^d$, and the RKHS does not even contain the nonzero constant
functions when $X$ has nonempty interior; see @steinwart2008[Sect. 4.4]). Nevertheless it is dense
in $C(X)$ for every width $sigma$.

When some coefficients vanish, the criterion may fail, and universality may be lost.

#example[A non-universal Taylor kernel][
  Consider the kernel $K(x, x') = cosh(ip(x, x'))$ on $RR^d$. Since
  $cosh t = sum_(n=0)^oo t^(2n) \/ (2n)!$, it is a Taylor kernel with $a_n = 0$ for odd $n$. The feature map of @prop:univ-taylor has only the components with $abs(j)$ even, all
  of which are even functions, so $Phi(-x) = Phi(x)$. If $X$ is compact with $X = -X$ and $X != {0}$
  (for instance a closed ball), $Phi$ is not injective on $X$, so $K$ is not universal on $X$ by
  @prop:univ-properties (i); concretely, every $f in H_K$ satisfies $f(-x) = f(x)$. On the other hand,
  the same kernel is universal on $X = [0, 1] subset RR$ (@ex:univ-ex-cosh). Universality
  really is a property of the kernel _together with_ the input space.
] <ex:univ-cosh>

#remark[Why we work over $RR^d$][
  One may be tempted to define Taylor kernels on complex balls, $K(z, zeta) := sum_n a_n
  ip(z, zeta)_(CC^d)^n$ with $ip(z, zeta)_(CC^d) = sum_i z_i overline(zeta_i)$. This is indeed a positive
  definite kernel, with feature map $Phi(zeta) = (sqrt(a_(abs(j)) c_j) overline(zeta)^j)_j$. But it is
  _not_ universal in the complex sense on any compact set $X subset.eq CC^d$ with nonempty interior:
  every $f in H_K$ is of the form $f(z) = sum_j w_j sqrt(a_(abs(j)) c_j) z^j$, a power series that is
  holomorphic on the ball, and uniform limits of holomorphic functions are holomorphic in the interior
  of $X$. So a function like $z |-> overline(z_1)$ cannot be approximated. In the language of the
  complex version of @thm:univ-criterion, the polynomials in $z$ form an algebra that separates points
  and vanishes nowhere, but they are not closed under conjugation. The simplest instance is the Szegő
  kernel $1 \/ (1 - z overline(zeta))$ on the unit disc ($d = 1$, $a_n = 1$), whose RKHS is the Hardy
  space $H^2$ of holomorphic functions (@ex:rkhs-kernels).
] <rem:univ-complex-taylor>

== Fourier kernels on the torus <sec:univ-fourier>

Our second family of examples are the translation-invariant kernels on the torus from
@ex:mercer-torus. As there, $TT^d := RR^d \/ (2 pi ZZ)^d$ carries the metric
$d(x, y) := min_(m in ZZ^d) abs(x - y - 2 pi m)$, which makes it a compact metric space. (Any other
metric inducing the same topology, such as the one inherited from the embedding
$x |-> (e^(i x_1), ..., e^(i x_d)) in CC^d$, would do equally well, since universality depends only on
the topology.) Functions on $TT^d$ are the same as functions on $RR^d$ that are $2 pi$-periodic in each
coordinate, and $C(TT^d)$ corresponds to the continuous periodic functions. For $k in ZZ^d$ let
$e_k (x) := e^(i k dot x)$ with $k dot x = sum_(l=1)^d k_l x_l$. With respect to the normalized measure
$dif mu := (2 pi)^(-d) dif x$ on $[0, 2 pi)^d$, the functions $(e_k)_(k in ZZ^d)$ are orthonormal in
$L^2 (mu)$; we write $hat(g)(k) := ip(g, e_k)_(L^2 (mu)) = integral g overline(e_k) dif mu$ for the
Fourier coefficients.

#example[Fourier kernels on the torus][
  Let $(w_k)_(k in ZZ^d)$ satisfy $w_k >= 0$ for all $k$ and $sum_(k in ZZ^d) w_k < oo$, and put
  $
    K(x, y) := sum_(k in ZZ^d) w_k e^(i k dot (x - y)), quad x, y in TT^d.
  $
  + $K$ is a continuous positive definite kernel on $TT^d$, and $K$ is universal (in the complex
    sense) if and only if $w_k > 0$ for all $k in ZZ^d$.
  + If moreover $w_k = w_(-k)$ for all $k$, then $K(x, y) = sum_k w_k cos(k dot (x - y))$ is
    real-valued, and $K$ is universal as a real kernel if and only if $w_k > 0$ for all $k in ZZ^d$.
] <ex:univ-fourier>

#proof[
  (i) _Kernel and feature map._ Define $Phi: TT^d -> ell^2 (ZZ^d)$, $Phi(x) := (Phi_k (x))_(k in ZZ^d)$, by
  $
    Phi_k (x) := sqrt(w_k) overline(e_k (x)) = sqrt(w_k) e^(-i k dot x) .
  $
  Then $norm(Phi(x))_(ell^2)^2 = sum_k w_k < oo$ and
  $
    ip(Phi(y), Phi(x))_(ell^2) = sum_(k in ZZ^d) Phi_k (y) overline(Phi_k (x))
    = sum_(k in ZZ^d) w_k e^(-i k dot y) e^(i k dot x) = K(x, y),
  $
  so $K$ is a positive definite kernel with feature map $Phi$. The series defining $K$ converges
  absolutely and uniformly on $TT^d times TT^d$ by the Weierstrass M-test (its terms are bounded by
  $w_k$), so $K$ is continuous. By @prop:rkhs-feature-representation,
  $
    H_K = {f_v := sum_(k in ZZ^d) v_k sqrt(w_k) e_k : v in ell^2 (ZZ^d)},
  $ <eq:univ-torus-rkhs>
  where the series converges absolutely and uniformly, since
  $sum_k abs(v_k) sqrt(w_k) <= norm(v)_(ell^2) (sum_k w_k)^(1\/2)$ by Cauchy--Schwarz.

  _Sufficiency._ Let $w_k > 0$ for all $k$. Choosing $v := w_k^(-1\/2) delta_k$ in
  @eq:univ-torus-rkhs shows $e_k in H_K$ for every $k$, so $H_K$ contains the space $cal(T)$ of
  trigonometric polynomials $sum_(k in F) b_k e_k$ ($F subset ZZ^d$ finite, $b_k in CC$). Now
  $cal(T)$ is an algebra ($e_k e_l = e_(k+l)$), contains the constants ($e_0 = 1$), is closed under
  conjugation ($overline(e_k) = e_(-k)$), and separates points: if $x != y$ in $TT^d$, then
  $x_l - y_l in.not 2 pi ZZ$ for some $l$, so $e_(delta_l) (x) = e^(i x_l) != e^(i y_l) = e_(delta_l) (y)$,
  where $delta_l in ZZ^d$ is the $l$-th unit vector. By the complex Stone--Weierstrass theorem
  (@thm:app-stone-weierstrass), $cal(T)$ is dense in $C(TT^d, CC)$, and so is $H_K supset.eq cal(T)$.

  _Necessity._ Let $w_(k_0) = 0$ for some $k_0$. For $f = f_v in H_K$, uniform convergence of
  @eq:univ-torus-rkhs allows termwise integration, so by orthonormality
  $hat(f)(k_0) = v_(k_0) sqrt(w_(k_0)) = 0$. Hence for every $f in H_K$
  $
    norm(e_(k_0) - f)_oo >= integral abs(e_(k_0) - f) dif mu >= abs(hat(e_(k_0))(k_0) - hat(f)(k_0)) = 1,
  $
  and $e_(k_0)$ cannot be approximated. So $K$ is not universal.

  (ii) If $w_k = w_(-k)$, replacing $k$ by $-k$ in the sum shows $overline(K(x, y)) = K(x, y)$, and
  pairing the terms for $k$ and $-k$ gives the cosine form. For the real statement we use
  @thm:univ-criterion with a _real_ feature map. Let $Z_+$ be the set of $k in ZZ^d without {0}$ whose
  first nonzero coordinate is positive, so that $ZZ^d$ is the disjoint union of ${0}$, $Z_+$ and
  $-Z_+$. Define the real components
  $
    Psi_0 := sqrt(w_0), quad Psi_(k, "c") (x) := sqrt(2 w_k) cos(k dot x), quad
    Psi_(k, "s") (x) := sqrt(2 w_k) sin(k dot x), quad k in Z_+ .
  $
  Using $cos(a) cos(b) + sin(a) sin(b) = cos(a - b)$ and $w_k = w_(-k)$,
  $
    Psi_0^2 + sum_(k in Z_+) (Psi_(k,"c") (x) Psi_(k,"c") (y) + Psi_(k,"s") (x) Psi_(k,"s") (y))
    = w_0 + sum_(k in Z_+) 2 w_k cos(k dot (x - y)) = K(x, y),
  $
  and the left-hand side is $sum_n Psi_n (x) Psi_n (y)$ with $sum_n Psi_n (x)^2 = sum_k w_k < oo$. So
  $Psi$ is a feature map of $K$ into (real) $ell^2$ over the countable index set
  ${0} union (Z_+ times {"c", "s"})$. We check the hypotheses of @thm:univ-criterion, assuming
  $w_k > 0$ for all $k$. (i) If $Psi(x) = Psi(y)$, then for each unit vector $delta_l in Z_+$ we get
  $cos x_l = cos y_l$ and $sin x_l = sin y_l$, so $x_l - y_l in 2 pi ZZ$; hence $x = y$ in $TT^d$.
  (ii) $K(x, x) = sum_k w_k >= w_0 > 0$. (iii) The span of the components is
  $spn{1, cos(k dot x), sin(k dot x) : k in Z_+}$, the space of real-valued trigonometric
  polynomials. It is an algebra by the product formulas
  $2 cos a cos b = cos(a - b) + cos(a + b)$, $2 sin a sin b = cos(a - b) - cos(a + b)$,
  $2 sin a cos b = sin(a + b) + sin(a - b)$, since $cos$ is even, $sin$ is odd, and every
  $k in ZZ^d without {0}$ lies in $Z_+$ or in $-Z_+$. So $K$ is universal as a real kernel.

  Conversely, let $w_(k_0) = 0$ for some $k_0$; then also $w_(-k_0) = 0$. By
  @prop:rkhs-feature-representation, every $f$ in the real RKHS $H_K$ has the form
  $f = u_0 Psi_0 + sum_(k in Z_+) (u_(k,"c") Psi_(k,"c") + u_(k,"s") Psi_(k,"s"))$ with a real
  square-summable coefficient family $u$, and the series converges uniformly on $TT^d$ by the
  Cauchy--Schwarz inequality, because $sum_n Psi_n (x)^2 = sum_k w_k$. The term with index $k$ is a
  linear combination of $e_k$ and $e_(-k)$, and it vanishes identically if $w_k = 0$. Integrating
  termwise, every term has vanishing $k_0$-th Fourier coefficient: for $k in.not {k_0, -k_0}$ by
  orthonormality, and for $k in {k_0, -k_0}$ because the term is zero. Hence $hat(f)(k_0) = 0$. The
  real function $g(x) := cos(k_0 dot x)$ has $hat(g)(k_0) = 1 \/ 2$ if $k_0 != 0$ and $hat(g)(0) = 1$, so
  $norm(g - f)_oo >= integral abs(g - f) dif mu >= abs(hat(g)(k_0) - hat(f)(k_0)) >= 1 \/ 2$ for every
  $f in H_K$, and $K$ is not universal as a real kernel.
]

In the language of @sec:mercer, the numbers $w_k$ are the eigenvalues of the integral operator
$T_K$ on $L^2 (mu)$, with eigenfunctions $e_k$ (@ex:mercer-torus). @ex:univ-fourier thus says that a
translation-invariant kernel on the torus is universal exactly when no frequency is "switched off".
The weights may decay arbitrarily fast: with $w_k = e^(-abs(k))$ (compare the Poisson kernel of
@ex:univ-ex-poisson) or even $w_k = e^(-abs(k)^2)$, the RKHS consists of extremely smooth functions and
is nonetheless dense in $C(TT^d)$. The latter choice gives the periodic analogue of the Gaussian
kernel (the heat kernel of the torus). By contrast,
the Sobolev kernels with $w_k tilde (1 + abs(k)^2)^(-s)$, $s > d \/ 2$, from @ex:mercer-torus are
universal with the much larger RKHS $H^s (TT^d)$.

== Universality and learning <sec:univ-learning>

We now return to the question that motivated this chapter and show that a universal kernel makes
the approximation error vanish for every distribution. In this section all functions are
real-valued, as in @sec:loss.

#theorem[Universal kernels achieve the Bayes risk][
  Let $(X, d)$ be a compact metric space equipped with its Borel $sigma$-algebra, $Y subset.eq RR$
  closed, $P$ a distribution on $X times Y$, and $K: X times X -> RR$ a universal kernel with RKHS
  $H_K$. Let $L: X times Y times RR -> [0, oo)$ be a loss (@def:learn-loss).
  + If $L$ is a continuous $P$-integrable Nemitski loss (@def:loss-convex-continuous,
    @def:loss-nemitski), i.e. $t |-> L(x, y, t)$ is continuous for all $(x, y)$ and
    $L(x, y, t) <= b(x, y) + h(abs(t))$ with a measurable $b: X times Y -> [0, oo)$ satisfying
    $integral b dif P < oo$ and a non-decreasing $h: [0, oo) -> [0, oo)$, then
    $
      cal(R)^*_(L, P, H_K) = inf_(f in H_K) risk(L, P)(f) = bayes(L, P).
    $
    More precisely, for every measurable $f: X -> RR$ and every $epsilon > 0$ there is $g in H_K$ with
    $risk(L, P)(g) <= risk(L, P)(f) + epsilon$.
  + In particular, $cal(R)^*_(L, P, H_K) = bayes(L, P)$ holds for every Lipschitz continuous loss $L$
    (@def:loss-lipschitz) with $risk(L, P)(0) < oo$.
] <thm:univ-bayes>

#proof[
  (i) Since $H_K subset.eq C(X)$ consists of measurable functions, $bayes(L, P) <= cal(R)^*_(L, P, H_K)$,
  and the identity follows from the more precise statement. To prove the latter, let $f$ be measurable
  and $epsilon > 0$; we may assume $risk(L, P)(f) < oo$, since otherwise every $g in H_K$ will do. We
  approximate $f$ in three steps: by a bounded function, by a continuous function, and by a function in
  $H_K$. The key tool in the last two steps is @prop:loss-risk-continuity (i), a consequence of
  dominated convergence with the majorant $b + h(M)$:

  $(*)$ _If $g_n, g: X -> RR$ are measurable, $abs(g_n) <= M$ for all $n$, and $g_n -> g$
  $P_X$-almost surely, then $risk(L, P)(g_n) -> risk(L, P)(g)$._

  _Step 1: truncation._ For $M in NN$ let $f_M := f ind_({abs(f) <= M})$, which is measurable and
  bounded by $M$. Then
  $
    risk(L, P)(f_M) = integral ind_({abs(f(x)) <= M}) L(x, y, f(x)) dif P(x, y)
    + integral ind_({abs(f(x)) > M}) L(x, y, 0) dif P(x, y).
  $
  As $M -> oo$, the first integral increases to $risk(L, P)(f)$ by monotone convergence
  (@thm:app-convergence), because $ind_({abs(f) <= M}) arrow.t 1$ pointwise. The second integrand is
  bounded by $b(x, y) + h(0)$, which is $P$-integrable, and tends to $0$ pointwise, so the second
  integral tends to $0$ by dominated convergence. Choose $M$ with
  $risk(L, P)(f_M) <= risk(L, P)(f) + epsilon \/ 3$.

  _Step 2: continuous approximation._ By @lem:univ-continuous-dense (ii), applied to the finite
  measure $P_X$, there are continuous $g_n: X -> RR$ with $abs(g_n) <= M$ and $g_n -> f_M$
  $P_X$-almost surely. By $(*)$, $risk(L, P)(g_n) -> risk(L, P)(f_M)$, so there is a continuous $g_0$
  with $abs(g_0) <= M$ and $risk(L, P)(g_0) <= risk(L, P)(f_M) + epsilon \/ 3$.

  _Step 3: approximation in $H_K$._ By universality there are $u_n in H_K$ with
  $norm(u_n - g_0)_oo -> 0$; for large $n$ they satisfy $abs(u_n) <= M + 1$, and $u_n -> g_0$
  everywhere. By $(*)$ (with $M + 1$ in place of $M$), $risk(L, P)(u_n) -> risk(L, P)(g_0)$, so some
  $g := u_n in H_K$ satisfies
  $risk(L, P)(g) <= risk(L, P)(g_0) + epsilon \/ 3 <= risk(L, P)(f) + epsilon$.

  (ii) A Lipschitz continuous loss is continuous, and
  $L(x, y, t) <= L(x, y, 0) + abs(L)_1 abs(t)$. So $L$ is a Nemitski loss with the measurable function
  $b(x, y) := L(x, y, 0)$ and $h(s) := abs(L)_1 s$, and it is $P$-integrable because
  $integral b dif P = risk(L, P)(0) < oo$. Now apply (i).
]

#remark[
  Part (ii) covers the hinge loss and the logistic loss for classification ($Y = {-1, 1}$) for
  _every_ $P$, since there $L(y, 0)$ is bounded. Part (i) also covers non-Lipschitz losses, for
  instance the least squares loss whenever $integral y^2 dif P < oo$ (with $b(x, y) = 2 y^2$ and
  $h(s) = 2 s^2$). No convexity is needed. Note that the Bayes decision function itself need not lie in
  $H_K$, and in general it need not even exist; the theorem only concerns infima.
]

*From approximation to consistency.* @thm:univ-bayes removes the approximation error from the
decomposition of @sec:univ-motivation. Combined with the stability analysis of @sec:stab, this yields
consistency of regularized kernel methods. In @sec:stab-outlook it is shown, for a convex Lipschitz
continuous loss $L$, a bounded measurable kernel $K$, and every distribution $P$ with
$risk(L, P)(0) < oo$, that for all $lambda > 0$, $N in NN$ and $delta in (0, 1)$, with probability
at least $1 - delta$ over the sample of size $N$,
$
  risk(L, P)(f_(D, lambda)) - cal(R)^*_(L, P, H_K) <= A(lambda) + c / (lambda sqrt(N delta)),
$
with the constant $c = abs(L)_1^2 abs(K)_oo^2$, where $A$ is the approximation error function
(@def:stab-approx-error), which satisfies $A(lambda) -> 0$ as $lambda -> 0$. Choosing
$lambda = lambda_N -> 0$ with $lambda_N^2 N -> oo$ gives $risk(L, P)(f_(D, lambda_N)) -> cal(R)^*_(L, P, H_K)$
in probability. A universal kernel on a compact metric space is continuous, hence bounded and
measurable, and by @thm:univ-bayes (ii) the limit $cal(R)^*_(L, P, H_K)$ equals $bayes(L, P)$. The
resulting statement, that the risks of the learned decision functions approach the Bayes risk for
_every_ distribution $P$, is called _universal consistency_. That support vector machines with
universal kernels are universally consistent was first proved in @steinwart2001; see @steinwart2008
for the general theory. Two caveats are in order. First, universal consistency says nothing about the
_speed_ of convergence, and it is known that no learning method can converge at a uniform rate for all
distributions @devroye1996. Rates require assumptions on $P$, typically on how fast $A(lambda)$
decays, which by @prop:univ-thin is related to how well the Bayes decision function can be
approximated with functions of moderate $H_K$-norm. Second, the compactness of $X$ is a real
restriction; see the notes below.

#remark[Universality and Mercer's theorem][
  Let $K$ be universal on $X$ and let $mu$ be a finite Borel measure on $X$. By @cor:univ-lp-dense,
  $H_K$ is dense in $L^2 (mu)$. The hypotheses of @thm:mercer-integral-operator are satisfied: $K$ is
  continuous, so every $K(dot, x)$ is Borel measurable; $H_K$ is separable by @prop:rkhs-separable (a
  compact metric space is separable); and $abs(K)_2^2 <= abs(K)_oo^2 mu(X) < oo$. Recall from that
  theorem that $S_K^*: H_K -> L^2 (mu)$ is the embedding and $T_K = S_K^* S_K$. By @prop:app-adjoint-kernel-range,
  $Ker S_K = (Ran S_K^*)^perp = {0}$, and since $ip(T_K g, g)_(L^2 (mu)) = norm(S_K g)_(H_K)^2$ we get
  $Ker T_K = Ker S_K = {0}$. Hence the eigenfunctions $(e_j)$ of $T_K$ form an orthonormal basis of
  $L^2 (mu)$ (not just of $(Ker T_K)^perp$), and if $L^2 (mu)$ is infinite-dimensional, then $T_K$
  has infinitely many positive eigenvalues (compare @prop:mercer-rkhs-spectral (v), where
  $supp mu = X$). The converse is
  false: the Brownian motion kernel of @ex:univ-brownian gives a dense embedding into
  $L^2 [0, 1]$ but is not universal.
]

#remark[Universal kernels are characteristic][
  Let $K$ be a universal real kernel on $X$ and let $P, Q$ be two Borel probability measures on $X$
  with $integral f dif P = integral f dif Q$ for all $f in H_K$. Then $P = Q$. Indeed, for $g in C(X)$
  and $f in H_K$,
  $abs(integral g dif P - integral g dif Q) <= 2 norm(g - f)_oo + abs(integral f dif P - integral f dif Q) = 2 norm(g - f)_oo$,
  which can be made arbitrarily small; so $integral g dif P = integral g dif Q$ for all continuous
  $g$. For a closed set $F$, the continuous functions $phi_n$ from the proof of
  @lem:univ-continuous-dense decrease to $ind_F$, so dominated convergence gives $P(F) = Q(F)$. Since
  the closed sets form an intersection-stable generator of $borel(X)$, the uniqueness theorem for
  measures gives $P = Q$. Kernels with this
  property are called _characteristic_: the "kernel mean" $integral K(dot, x) dif P(x) in H_K$
  determines the distribution $P$. This is the basis of the maximum mean discrepancy between
  distributions and of kernel two-sample tests @gretton2012; the relations between universal and
  characteristic kernels are surveyed in @sriperumbudur2011.
]

#context-note[
  *The Gaussian kernel in practice.* The Gaussian kernel is the default choice in kernel methods
  @schoelkopf2002 @hastie2009, and @ex:univ-taylor gives one theoretical reason: it is universal for
  _every_ width $sigma > 0$. The width does not influence the limit $cal(R)^*_(L, P, H_K) = bayes(L, P)$,
  but it strongly influences the finite-sample behaviour, and it is usually chosen by
  cross-validation. The two extremes illustrate the approximation--estimation trade-off. As
  $sigma -> 0$, the Gram matrix $(K_sigma (x_i, x_j))_(i,j)$ of distinct points tends to the identity, and the
  interpolant of @rem:univ-interpolation becomes a sum of narrow bumps centred at the data points,
  close in spirit to the pathological interpolant of @sec:learn-overfitting. As $sigma -> oo$,
  functions of moderate norm become very flat: by the kernel-metric estimate of @ex:rkhs-gaussian
  (based on @lem:rkhs-kernel-metric), every $f in H_(K_sigma)$ satisfies
  $
    abs(f(x) - f(x')) <= sqrt(2) norm(f)_(H_(K_sigma)) norm(x - x') / sigma,
  $
  so that with a fixed budget for $norm(f)_(H_K)$ only nearly constant functions are available, and the
  method underfits.
]

== Summary

- A continuous kernel $K$ on a compact metric space $X$ is _universal_ if $H_K$ is dense in
  $(C(X), norm(dot)_oo)$. This is a distribution-free richness condition: it implies density in every
  $L^p (mu)$ (@cor:univ-lp-dense) and makes the approximation error vanish for every distribution $P$
  and every continuous $P$-integrable Nemitski loss, in particular every Lipschitz loss with
  $risk(L, P)(0) < oo$ (@thm:univ-bayes). This is the key to universal
  consistency.
- Universal kernels separate disjoint compact sets with a margin (@prop:univ-separation). In feature
  space, every consistently labelled finite data set is linearly separable (@cor:univ-hyperplane). This
  is why regularization is indispensable.
- Universal kernels are strictly positive definite, have injective feature maps and $K(x, x) > 0$;
  universality is preserved under restriction to compact subsets and under normalization
  (@prop:univ-properties).
- $H_K$ is dense but thin: for infinite $X$, $H_K != C(X)$, and approximating $g in.not H_K$ forces
  the $H_K$-norm to infinity (@prop:univ-thin).
- A Stone--Weierstrass criterion (@thm:univ-criterion): an injective $ell^2$-valued feature map with
  $K(x, x) > 0$ whose components span an algebra gives a universal kernel.
- Examples: Taylor kernels $sum_n a_n ip(x, x')^n$ with all $a_n > 0$, in particular the exponential,
  Gaussian (every $sigma > 0$), and binomial kernels (@ex:univ-taylor); Fourier kernels on the torus
  with all weights positive, and only those (@ex:univ-fourier). Non-examples: linear and polynomial
  kernels (finite-dimensional $H_K$), the Brownian motion kernel $min{x, x'}$, and $cosh ip(x, x')$ on
  symmetric sets.

In the next chapter we turn from the hypothesis space to the optimization problem itself: we show
that the regularized risk has a unique minimizer $f_(P, lambda)$ in $H_K$ and describe it through
representer theorems.

== Notes and further reading

Universal kernels were introduced by #cite(<steinwart2001>, form: "prose"), who proved, among other
results, a version of the Stone--Weierstrass criterion (@thm:univ-criterion), the universality of
Taylor kernels and of the Gaussian kernel, and the universal consistency of support vector machines
with universal kernels. Our presentation follows @steinwart2008[Sect. 4.6], where one also finds
further examples, and whose Chapters 5 and 6 contain the full consistency theory, including versions of
@thm:univ-bayes for non-compact $X$ and unbounded $Y$. The RKHS of the Gaussian kernel is described
explicitly in @steinwart2008[Sect. 4.4]. The approximation-theoretic side of learning, in particular
quantitative bounds on the approximation error for RKHSs, is the subject of @cucker2007.

#cite(<micchelli2006>, form: "prose") call a kernel on an arbitrary (Hausdorff) input space universal
if its restriction to every compact subset is universal in our sense. By @prop:univ-properties (iv),
for compact $X$ this agrees with our definition. They characterize universality through feature maps
and, via Bochner's theorem, for translation-invariant kernels on $RR^d$ in terms of the spectral
measure of the kernel. This generalizes @ex:univ-fourier from the torus to $RR^d$: roughly speaking,
the spectral measure plays the role of the weights $(w_k)$ and must not be "too small". Other
variants of universality in the literature, which we only mention, require density of $H_K$ in
$C_0 (X)$ for locally compact $X$ ("$c_0$-universality"), or injectivity of the kernel mean embedding
$P |-> integral K(dot, x) dif P(x)$ ("characteristic kernels", used in kernel two-sample tests
@gretton2012); the remark on characteristic kernels above shows that universality implies the latter
on compact spaces. The relations between these notions are worked out in @sriperumbudur2011.
Universal kernels on "non-standard" compact input spaces that are not subsets of $RR^d$, for instance
sets of probability measures or of functions, are constructed in @christmann2010.

For the Stone--Weierstrass and Tietze theorems see Appendix A (@thm:app-stone-weierstrass,
@thm:app-tietze); regularity of measures on metric spaces is treated in @dudley2002. Concepts from
learning theory mentioned in this chapter, such as the VC dimension and the no-free-lunch phenomenon,
are covered in @shalev2014 and @devroye1996. For the practical use of Gaussian kernels see
@schoelkopf2002 and @hastie2009.

== Exercises

#exercise[Sums of kernels][
  Let $K$ be universal on the compact metric space $X$ and let $K'$ be any continuous positive
  definite kernel on $X$. Show that $K + K'$ and $c K$ for $c > 0$ are universal.

  _Hint:_ $H_K subset.eq H_(K + K')$ by @prop:rkhs-sum-restriction (iii), and $H_(c K) = H_K$ as sets.
] <ex:univ-ex-sum>

#exercise[The $cosh$ kernel][
  Let $K(x, x') = cosh(x x')$ for $x, x' in RR$.
  + Show that $K$ is not universal on $X = [-1, 1]$, and determine the closure of $H_K$ in $C[-1, 1]$.
  + Show that $K$ is universal on $X = [0, 1]$.

  _Hint:_ For (ii), apply @thm:univ-criterion. The span of the components is the space of polynomials
  in $x^2$. Is it an algebra, does it separate the points of $[0, 1]$, and does it vanish nowhere?
] <ex:univ-ex-cosh>

#exercise[Real versus complex universality][
  Let $K: X times X -> RR$ be a continuous positive definite kernel (real, hence symmetric) on a
  compact metric space. Denote by $H_K^RR$ its real RKHS and by $H_K^CC$ the RKHS of $K$ regarded as a
  complex kernel. Show that $H_K^CC = {f + i g : f, g in H_K^RR}$, and conclude that $H_K^RR$ is dense
  in $C(X, RR)$ if and only if $H_K^CC$ is dense in $C(X, CC)$.

  _Hint:_ Take a real feature map $Phi: X -> H_0$ and use the complexification $H_0 + i H_0$ of
  $H_0$ as a complex feature space; then apply @prop:rkhs-feature-representation. For the density
  statement, take real and imaginary parts.
] <ex:univ-ex-complexification>

#exercise[Change of variables][
  Let $K$ be universal on the compact metric space $X$, let $tilde(X)$ be another compact metric
  space, and let $phi: tilde(X) -> X$ be continuous and injective.
  + Show that $tilde(K)(u, v) := K(phi(u), phi(v))$ is universal on $tilde(X)$.
  + Deduce that $(s, t) |-> exp(cos(s - t))$ is a universal kernel on the circle $TT^1$.

  _Hint:_ A continuous bijection between compact metric spaces is a homeomorphism, so
  $g |-> g compose phi$ is an isometric isomorphism $C(phi(tilde(X))) -> C(tilde(X))$. Combine this with
  @prop:univ-properties (iv) and @prop:rkhs-sum-restriction (iv). For (ii), write
  $cos(s - t) = ip(phi(s), phi(t))$ with $phi(s) = (cos s, sin s)$, and use (i) and @ex:univ-taylor
  on the unit circle in $RR^2$.
] <ex:univ-ex-composition>

#exercise[The Poisson kernel][
  For $0 < rho < 1$ let $K_rho (x, y) := sum_(k in ZZ) rho^(abs(k)) e^(i k (x - y))$ on $TT^1$.
  + Show that $K_rho (x, y) = (1 - rho^2) \/ (1 - 2 rho cos(x - y) + rho^2)$.
  + Show that $K_rho$ is universal (as a real kernel), and describe $H_(K_rho)$ in terms of Fourier
    coefficients.
  + Show that every $f in H_(K_rho)$ extends to a holomorphic function on the annulus
    ${z in CC : rho^(1\/2) < abs(z) < rho^(-1\/2)}$ via $e^(i x) |-> z$. Compare with @prop:univ-thin.

  _Hint:_ (i) Sum two geometric series. (ii) Use @ex:univ-fourier and @eq:univ-torus-rkhs.
] <ex:univ-ex-poisson>
