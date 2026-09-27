#import "/template.typ": *

// Real and imaginary parts (the built-in symbols Re, Im are fraktur letters).
#let Re = math.op("Re")
#let Im = math.op("Im")

= Reproducing Kernel Hilbert Spaces <sec:rkhs>

In @sec:learn we saw that minimizing the empirical risk over _all_ functions leads to overfitting: a
function can reproduce the training data perfectly and still be useless on new inputs
(@sec:learn-overfitting). The remedy we settled on is to minimize a _regularized_ risk
$ risk(L, D)(f) + lambda norm(f)_H^2 $
over a Hilbert space $H$ of functions on the input space $X$. The empirical risk sees a function $f$ only
through its values $f(x_1), dots, f(x_N)$, the regularizer only through its norm. If the norm did not
control the values, a function of tiny norm could take arbitrary values at the data points, and the
regularizer would not prevent overfitting at all. We therefore want the point evaluations $f |-> f(x)$ to
be _continuous_ linear functionals on $H$. Hilbert spaces of functions with this property are called
_reproducing kernel Hilbert spaces_ (RKHSs); they are the hypothesis spaces of this book. The main results
of this chapter are:

- Every RKHS $H$ has a unique _reproducing kernel_, a function $K: X times X -> KK$ such that
  $f(x) = ip(f, K(dot, x))_H$ for all $f in H$ and $x in X$. It is _positive definite_: all matrices
  $(K(x_i, x_j))_(i,j)$ are positive semidefinite.
- Conversely, every positive definite kernel is the kernel of exactly one RKHS (_Moore–Aronszajn
  theorem_). Choosing a hypothesis space is the same as choosing a kernel, and kernels are much easier to
  write down than Hilbert spaces.
- Every kernel has the form $K(x, x') = ip(Phi(x'), Phi(x))$ for a _feature map_ $Phi$, and the RKHS
  consists exactly of the functions $x |-> ip(w, Phi(x))$: nonlinear functions on $X$ become linear
  functions of the features (the _kernel trick_).
- Measurability, boundedness and continuity of the functions in the RKHS can be read off from the kernel.

@sec:mercer describes $H_K$ through the eigenvalues of an integral operator, @sec:univ asks when $H_K$ is
rich enough to approximate every continuous function, and in @sec:reg the RKHS serves as the hypothesis
space of the regularized problem.

Throughout this chapter, $X$ is a nonempty set and $KK in {RR, CC}$. We write $KK^X$ for the vector space
of all functions $X -> KK$, with pointwise addition and scalar multiplication. Inner products are linear in
the first and conjugate-linear in the second argument. In the real case, complex conjugation is the
identity and can be ignored everywhere.

== A first example <sec:rkhs-warmup>

We begin with the space already met in @sec:learn, in which point evaluations are continuous, and compute
its "reproducing kernel" by hand. The example will accompany us through the chapter. Recall that
$f: [0, 1] -> KK$ is _absolutely continuous_ if and only if $f(x) = f(0) + integral_0^x g(t) dif t$ for
all $x$, for some $g in cal(L)^1 [0, 1]$; then $f' = g$ almost everywhere, and conversely
$x |-> integral_0^x g(t) dif t$ is absolutely continuous for every $g in cal(L)^1 [0, 1]$ (fundamental
theorem of calculus for the Lebesgue integral, @rudin1987[Ch. 7]).

#proposition(title: [A Sobolev space with kernel $min{x, y}$])[
  Let
  $ H := {f: [0, 1] -> KK : f "absolutely continuous", f(0) = 0, f' in L^2 [0, 1]}, quad
    ip(f, g)_H := integral_0^1 f'(t) overline(g'(t)) dif t. $
  Then
  + $(H, ip(dot, dot)_H)$ is a Hilbert space, and $D: H -> L^2 [0, 1]$, $f |-> f'$, is an isometric
    isomorphism;
  + for all $f in H$ and $x, y in [0, 1]$,
    $ abs(f(x)) <= sqrt(x) norm(f)_H quad "and" quad abs(f(x) - f(y)) <= sqrt(abs(x - y)) norm(f)_H ; $
  + for every $y in [0, 1]$, the function $K_y (x) := min{x, y}$ belongs to $H$ and
    $ f(y) = ip(f, K_y)_H quad "for all" f in H. $
] <prop:rkhs-sobolev>

#proof[
  (i) $H$ is a linear subspace of $KK^([0, 1])$ and $D$ is linear. $D$ is injective: if $f' = 0$ almost
  everywhere, then $f(x) = f(0) + integral_0^x f'(t) dif t = 0$ for all $x$. $D$ is surjective: for
  $g in L^2 [0, 1] subset.eq L^1 [0, 1]$, $f(x) := integral_0^x g(t) dif t$ lies in $H$ and $D f = g$.
  Since $ip(f, g)_H = ip(D f, D g)_(L^2)$, the form $ip(dot, dot)_H$ is sesquilinear, Hermitian and
  positive, and definite because $D$ is injective. So $D$ is a linear isometric bijection onto the Hilbert
  space $L^2 [0, 1]$, and completeness transfers: if $(f_n)$ is a Cauchy sequence in $H$, then $D f_n -> g$
  in $L^2$ for some $g$, and $f_n -> D^(-1) g$ in $H$.

  (ii) By symmetry we may assume $y <= x$. By the Cauchy–Schwarz inequality in $L^2 [0, 1]$,
  $ abs(f(x) - f(y)) = abs(integral_0^1 ind_([y, x]) (t) f'(t) dif t) <= norm(ind_([y, x]))_(L^2) norm(f')_(L^2) = sqrt(x - y) norm(f)_H . $
  Taking $y = 0$ and using $f(0) = 0$ gives the first inequality.

  (iii) We have $K_y (x) = integral_0^x ind_([0, y]) (t) dif t$, so $K_y$ is absolutely continuous with
  $K_y (0) = 0$ and $K'_y = ind_([0, y])$ almost everywhere; hence $K_y in H$. For $f in H$,
  $ ip(f, K_y)_H = integral_0^1 f'(t) ind_([0, y]) (t) dif t = f(y) - f(0) = f(y). #qedhere $
]

What does the example show? The functional $f |-> f(y)$ is continuous, so by the Riesz representation
theorem (@thm:app-riesz) it is the inner product with some element of $H$; part (iii) identifies this
element as $K_y = min{dot, y}$, and $K(x, y) := min{x, y}$ is the _reproducing kernel_ of $H$. The best
constant in $abs(f(x)) <= c_x norm(f)_H$ is $c_x = sqrt(x) = sqrt(K(x, x))$, attained at $f = K_x$; this
will be true in every RKHS. Finally, $norm(f)_H = norm(f')_(L^2)$ measures the "slope energy" of $f$: by
(ii), all functions in the unit ball of $H$ are Hölder continuous with exponent $1\/2$ and constant $1$, so
the regularizer $lambda norm(f)_H^2$ favours flat functions over wiggly ones. (Penalizing
$norm(f)_(L^2)^2 + norm(f')_(L^2)^2$ instead leads to another kernel, @ex:rkhs-exercise-h1.)

#context-note[
  $min{x, y}$ is the covariance function of Brownian motion, $EE[B_x B_y] = min{x, y}$. Every real-valued
  positive definite kernel is the covariance function of a Gaussian process, and its RKHS (the
  _Cameron–Martin space_ of the process) plays a central role in the analysis of the process
  @berlinet2004. The sample paths of Brownian motion are almost surely nowhere differentiable, so they do
  _not_ lie in $H$: the RKHS is a much smaller space than the one the random functions live in; it governs,
  for instance, the posterior mean in Gaussian process regression.

  The example is also the simplest instance of spline smoothing. Minimizing
  $1/N sum_i (y_i - f(x_i))^2 + lambda norm(f')_(L^2)^2$ over $H$ yields, by the representer theorem of
  @sec:reg, a function $sum_i a_i min{dot, x_i}$: continuous, piecewise linear with kinks only at the data
  points, a _linear spline_. Penalizing the second derivative leads to cubic smoothing splines
  @wahba1990 @kimeldorf1971.
]

#example(title: [$L^2$ norms do not control point values])[
  The elements of $L^2 [0, 1]$ are equivalence classes, so $f(x)$ is not defined. Passing to continuous
  representatives, i.e. to $C[0, 1]$ with the $L^2$ norm, does not help: $f_n (t) := max{0, 1 - n t}$ has
  $ f_n (0) = 1 quad "and" quad norm(f_n)_(L^2)^2 = integral_0^(1\/n) (1 - n t)^2 dif t = 1/(3 n) -> 0 , $
  so no constant $c$ satisfies $abs(f(0)) <= c norm(f)_(L^2)$ on $C[0, 1]$ (and the space is not complete
  either). Functions of arbitrarily small norm take arbitrary values at a point, which is exactly what makes
  regularization useless. @ex:rkhs-exercise-l2 shows that no choice of representatives turns
  $L^2 [0, 1]$ into an RKHS.
] <ex:rkhs-l2-nonexample>

== Reproducing kernel Hilbert spaces <sec:rkhs-definition>

The first definition makes precise what it means for a Hilbert space to consist of functions: its
elements are genuine functions on $X$ (not equivalence classes), with the pointwise vector space
operations.

#definition(title: [RKHS])[
  A _Hilbert space of functions_ on $X$ is a linear subspace $H subset.eq KK^X$ together with an inner
  product $ip(dot, dot)_H$ such that $(H, ip(dot, dot)_H)$ is a Hilbert space. For $x in X$, the
  _point evaluation_ at $x$ is the linear functional
  $ delta_x: H -> KK, quad delta_x (f) := f(x). $
  A Hilbert space of functions $H$ is a _reproducing kernel Hilbert space (RKHS)_ if every point evaluation
  is continuous, that is, if for every $x in X$ there is a constant $c_x >= 0$ with
  $ abs(f(x)) <= c_x norm(f)_H quad "for all" f in H. $
] <def:rkhs>

In a Hilbert space of functions, $f = 0$ means $f(x) = 0$ for _every_ $x in X$; this innocent remark is
used repeatedly below. If $H$ is an RKHS, the Riesz representation theorem (@thm:app-riesz) represents
each $delta_x$ by a unique element of $H$. Collecting these elements into one function of two variables
gives the central object of the theory.

#definition(title: [Reproducing kernel])[
  Let $H$ be a Hilbert space of functions on $X$. A function $K: X times X -> KK$ is a _reproducing kernel_
  of $H$ if its _kernel sections_
  $ K_x := K(dot, x): X -> KK, quad x in X, $
  belong to $H$ and satisfy the _reproducing property_
  $ f(x) = ip(f, K_x)_H quad "for all" f in H, x in X. $ <eq:rkhs-reproducing>
] <def:rkhs-kernel>

Applying the reproducing property to $f = K_(x')$ gives
$ K(x, x') = ip(K_(x'), K_x)_H = K_(x') (x) quad "for all" x, x' in X. $
The order of the arguments matters in the complex case; we always use $K_x = K(dot, x)$.

#proposition(title: [Basic properties of reproducing kernels])[
  Let $H$ be a Hilbert space of functions on $X$. In (ii)–(vii), assume moreover that $H$ is an RKHS with
  reproducing kernel $K$, and let $x, x' in X$.
  + $H$ is an RKHS if and only if it has a reproducing kernel. In this case the reproducing kernel $K$ is
    unique, and $K_x$ is the Riesz representative of $delta_x$.
  + $K(x, x') = ip(K_(x'), K_x)_H$.
  + $K$ is Hermitian: $K(x', x) = overline(K(x, x'))$. In particular, $K(x, x) in RR$.
  + $K(x, x) = norm(K_x)_H^2 = norm(delta_x)_(H')^2 >= 0$. Consequently,
    $ abs(f(x)) <= sqrt(K(x, x)) norm(f)_H quad "for all" f in H, $
    and $sqrt(K(x, x))$ is the smallest constant with this property.
  + $K(x, x) = 0$ if and only if $f(x) = 0$ for all $f in H$.
  + $abs(K(x, x'))^2 <= K(x, x) K(x', x')$.
  + For all $n in NN$, $c_1, dots, c_n in KK$ and $x_1, dots, x_n in X$,
    $ sum_(i,j=1)^n overline(c_i) c_j K(x_i, x_j) = norm(sum_(i=1)^n c_i K_(x_i))_H^2 >= 0. $
] <prop:rkhs-kernel-properties>

#proof[
  (i) If $H$ is an RKHS, the Riesz representation theorem (@thm:app-riesz) gives for each $x$ a unique
  $k_x in H$ with $delta_x = ip(dot, k_x)_H$, and $K(y, x) := k_x (y)$ is a reproducing kernel.
  Conversely, if $K$ is a reproducing kernel, then $abs(f(x)) = abs(ip(f, K_x)_H) <= norm(K_x)_H norm(f)_H$,
  so $H$ is an RKHS. If $K$ and $tilde(K)$ are reproducing kernels, then
  $ip(f, K_x - tilde(K)_x)_H = f(x) - f(x) = 0$ for all $f$; with $f = K_x - tilde(K)_x$ we get
  $K_x = tilde(K)_x$ for every $x$, so $K = tilde(K)$. The identity $delta_x = ip(dot, K_x)_H$ says that $K_x$
  is the Riesz representative of $delta_x$.

  (ii) was shown before the proposition, and (iii) follows from it:
  $K(x', x) = ip(K_x, K_(x'))_H = overline(ip(K_(x'), K_x)_H) = overline(K(x, x'))$.

  (iv) By (ii), $K(x, x) = norm(K_x)_H^2 >= 0$, and $norm(K_x)_H = norm(delta_x)_(H')$ because the Riesz map is
  isometric; explicitly, $abs(f(x)) <= norm(K_x)_H norm(f)_H$ with equality for $f = K_x$.

  (v) By (iv), $K(x, x) = 0$ if and only if $delta_x = 0$. (vi) By (ii) and the Cauchy–Schwarz
  inequality, $abs(K(x, x')) <= norm(K_(x'))_H norm(K_x)_H = sqrt(K(x', x') K(x, x))$.

  (vii) Using (ii) and sesquilinearity,
  $ sum_(i,j=1)^n overline(c_i) c_j K(x_i, x_j) = sum_(i,j=1)^n overline(c_i) c_j ip(K_(x_j), K_(x_i))_H
    = ip(sum_(j=1)^n c_j K_(x_j), sum_(i=1)^n c_i K_(x_i))_H = norm(sum_(i=1)^n c_i K_(x_i))_H^2 . #qedhere $
]

By @prop:rkhs-kernel-properties (i), an RKHS determines its kernel. We will write $H_K$ for an RKHS with
kernel $K$ once we know (@thm:rkhs-moore-aronszajn) that the kernel, in turn, determines the space.

#remark(title: [The diagonal of $K$])[
  The function $x |-> K(x, x) = norm(delta_x)_(H')^2$ measures how strongly the norm controls the values
  at $x$. It need not be bounded, and it need not belong to $H$: for the linear kernel $K(x, x') = x x'$ on
  $RR$, whose RKHS consists of the functions $x |-> a x$ with norm $abs(a)$ (@ex:rkhs-kernels), $K(x, x) = x^2$.
  Boundedness of the diagonal is exactly what makes all functions in $H$ bounded (@prop:rkhs-bounded).
] <rem:rkhs-diagonal>

The kernel sections are the building blocks of an RKHS:

#lemma(title: [Kernel sections span a dense subspace])[
  Let $H$ be an RKHS on $X$ with kernel $K$. Then $H_(K,0) := spn{K_x : x in X}$ is dense in $H$.
] <lem:rkhs-span-dense>

#proof[
  By the projection theorem (@thm:app-projection), the closure of $H_(K,0)$ is $(H_(K,0)^perp)^perp$, so it
  suffices to show $H_(K,0)^perp = {0}$. If $f perp K_x$ for all $x in X$, then
  $f(x) = ip(f, K_x)_H = 0$ for all $x$, so $f = 0$ as a function, hence as an element of $H$.
]

Phrased for sequences, the property we asked for in the introduction says that norm convergence implies
pointwise convergence.

#proposition(title: [Norm, weak and pointwise convergence])[
  Let $H$ be an RKHS on $X$ with kernel $K$, and let $f, f_1, f_2, dots in H$.
  + If $norm(f_n - f)_H -> 0$, then $f_n (x) -> f(x)$ for every $x in X$. More precisely,
    $ sup_(x in M) abs(f_n (x) - f(x)) <= (sup_(x in M) sqrt(K(x, x))) norm(f_n - f)_H $
    for every $M subset.eq X$, so the convergence is uniform on every set $M$ with
    $sup_(x in M) K(x, x) < oo$, and uniform on $X$ if $K$ is bounded.
  + If $f_n -> f$ weakly in $H$, then $f_n (x) -> f(x)$ for every $x in X$.
  + If $(f_n)$ is bounded in $H$ and converges pointwise to a function $g: X -> KK$, then $g in H$,
    $f_n -> g$ weakly in $H$, and $norm(g)_H <= liminf_(n -> oo) norm(f_n)_H$.
] <prop:rkhs-norm-convergence>

#proof[
  (i) For every $x in M$, @prop:rkhs-kernel-properties (iv) gives
  $abs(f_n (x) - f(x)) <= sqrt(K(x, x)) norm(f_n - f)_H$; take the supremum over $x in M$.

  (ii) Weak convergence means $ip(f_n, h)_H -> ip(f, h)_H$ for every $h in H$. Take $h = K_x$ and use the
  reproducing property.

  (iii) Every subsequence of $(f_n)$ is bounded, so it has a further subsequence converging weakly to some
  $h in H$ (@thm:app-weak-compactness); by (ii) it converges pointwise to $h$, hence $h = g$. So $g in H$, and
  every subsequence has a further subsequence converging weakly to $g$. This forces $f_n -> g$ weakly:
  otherwise some $h in H$, $epsilon > 0$ and subsequence satisfy $abs(ip(f_(n_k) - g, h)_H) >= epsilon$ for
  all $k$, and no further subsequence converges weakly to $g$. Finally, $norm(g)_H <= liminf_n norm(f_n)_H$
  by weak lower semicontinuity of the norm (@thm:app-weak-compactness).
]

#warning-block[
  The converse of (i) is false: pointwise convergence does not imply norm convergence, not even for bounded
  sequences. In the space $H$ of @prop:rkhs-sobolev, the functions $f_n (x) := sin(n pi x) \/ (n pi)$ have
  $norm(f_n)_H^2 = integral_0^1 cos^2(n pi t) dif t = 1\/2$ and converge to $0$ uniformly, but not in norm.
  By (iii) they converge weakly to $0$.
]

== Positive definite kernels <sec:rkhs-pd>

By @prop:rkhs-kernel-properties (iii) and (vii), the kernel of an RKHS is Hermitian and all quadratic
forms $sum overline(c_i) c_j K(x_i, x_j)$ are nonnegative. These properties refer to the function $K$
alone. We give them a name; the next two sections show that they _characterize_ reproducing kernels.

#definition(title: [Positive definite kernel])[
  A function $K: X times X -> KK$ is called _positive definite_ if it is Hermitian,
  $K(x', x) = overline(K(x, x'))$ for all $x, x' in X$, and
  $ sum_(i,j=1)^n overline(c_i) c_j K(x_i, x_j) >= 0 quad "for all" n in NN, c = (c_1, dots, c_n) in KK^n, x_1, dots, x_n in X. $
  Equivalently: for all $x_1, dots, x_n in X$, the _Gram matrix_ $G := (K(x_i, x_j))_(i,j=1)^n$ is
  Hermitian and positive #emph[semi]definite, $c^* G c >= 0$ for all $c in KK^n$.

  $K$ is called _strictly positive definite_ if, in addition, $sum_(i,j=1)^n overline(c_i) c_j K(x_i, x_j) > 0$
  for all $n in NN$, all _pairwise distinct_ $x_1, dots, x_n in X$ and all $c in KK^n without {0}$, that
  is, if the Gram matrices of pairwise distinct points are positive definite (hence invertible).

  A positive definite function $K: X times X -> KK$ is also simply called a _kernel_ on $X$.
] <def:rkhs-pd>

#warning-block[
  The terminology clashes with linear algebra: a _positive definite kernel_ is one whose Gram matrices are
  positive _semidefinite_. The kernel $K(x, x') = 0$ is positive definite in this sense. What linear
  algebra calls positive definite corresponds to _strictly_ positive definite kernels. We follow the
  terminology of the kernel literature (e.g. @steinwart2008 @aronszajn1950), but we will always say
  "strictly" when we mean it.
]

#remark(title: [Why "Hermitian" is part of the definition])[
  For $KK = CC$ the Hermitian property follows from the nonnegativity of the quadratic forms: with $n = 2$
  and $c = (1, t)$, $t in CC$,
  $ q(t) := K(x, x) + t K(x, x') + overline(t) K(x', x) + abs(t)^2 K(x', x') >= 0 , $
  and $K(x, x), K(x', x') >= 0$ (case $n = 1$). For $a := K(x, x')$, $b := K(x', x)$, $q(1) in RR$ gives
  $Im a = - Im b$ and $q(i) in RR$ gives $Re a = Re b$, so $b = overline(a)$. Over $RR$ this fails: on
  $X = {1, 2}$ the function with Gram matrix $mat(0, 1; -1, 0)$ has all quadratic forms equal to $0$, but
  it is not symmetric and hence no reproducing kernel.
]

Taking $n <= 2$ in the definition, every positive definite $K$ has $K(x, x) >= 0$ and a $2 times 2$ Gram
matrix with nonnegative determinant:
$ abs(K(x, x'))^2 <= K(x, x) K(x', x') quad "for all" x, x' in X. $ <eq:rkhs-cs-kernel>
In particular, $sup_(x, x' in X) abs(K(x, x')) = sup_(x in X) K(x, x)$.

For kernels of RKHSs, strict positive definiteness means that the space can interpolate arbitrary values
at finitely many points.

#proposition(title: [Invertible Gram matrices and interpolation])[
  Let $H$ be an RKHS on $X$ with kernel $K$, and let $x_1, dots, x_n in X$ be pairwise distinct, with Gram
  matrix $G = (K(x_i, x_j))_(i,j=1)^n$. The following are equivalent:
  + $G$ is invertible (equivalently, positive definite);
  + $K_(x_1), dots, K_(x_n)$ are linearly independent in $H$;
  + $delta_(x_1), dots, delta_(x_n)$ are linearly independent in the dual space $H'$;
  + for every $v in KK^n$ there is $f in H$ with $f(x_i) = v_i$ for $i = 1, dots, n$.
  In particular, $K$ is strictly positive definite if and only if $H$ can interpolate arbitrary values at
  any finite set of distinct points.
] <prop:rkhs-strict-pd>

#proof[
  (i) $<=>$ (ii). The Hermitian positive semidefinite matrix $G$ is invertible if and only if all its
  eigenvalues are positive, i.e. $c^* G c > 0$ for $c != 0$. Since
  $c^* G c = norm(sum_i c_i K_(x_i))_H^2$ (@prop:rkhs-kernel-properties (vii)), this is (ii).

  (ii) $<=>$ (iii). For $c in KK^n$, $sum_i overline(c_i) delta_(x_i) = ip(dot, sum_i c_i K_(x_i))_H$, and
  this functional vanishes if and only if $sum_i c_i K_(x_i) = 0$.

  (iii) $<=>$ (iv). The map $E: H -> KK^n$, $E f := (f(x_1), dots, f(x_n))$, is surjective if and only if
  $(Ran E)^perp = {0}$ in $KK^n$. But $c perp Ran E$ means $sum_i overline(c_i) f(x_i) = 0$ for all $f$, i.e.
  $sum_i overline(c_i) delta_(x_i) = 0$.

  The final statement follows by applying (i) $<=>$ (iv) to all finite sets of distinct points.
]

#example[
  For the kernel $K(x, y) = min{x, y}$ of @prop:rkhs-sobolev and $0 < x_1 < dots < x_n <= 1$, the
  derivatives $K'_(x_i) = ind_([0, x_i])$ are linearly independent in $L^2 [0, 1]$, so the $K_(x_i)$ are
  linearly independent and the Gram matrix $(min{x_i, x_j})_(i,j)$ is invertible. Thus $min$ is strictly
  positive definite on $(0, 1]$. On $[0, 1]$ it is not, because $K_0 = 0$: every $f in H$ vanishes at $0$,
  so the value at $0$ cannot be interpolated. The linear kernel $K(x, x') = x x'$ on $RR$ is not strictly
  positive definite either: all its Gram matrices have rank at most one.
]

=== Checking positive definiteness, and why it is a robust property

Deciding whether a given $K$ is positive definite is in general difficult: _every_ Gram matrix, for all
$n$ and all choices of points, must be positive semidefinite. In practice one rarely checks this directly;
one exhibits a feature map (@sec:rkhs-feature-maps) or builds kernels from simpler ones by operations that
preserve positive definiteness (@sec:rkhs-examples). Two structural facts make this work well.

_Positive definiteness is a closed condition._ If $K_n$ are positive definite and $K_n -> K$ pointwise,
then every quadratic form $sum overline(c_i) c_j K(x_i, x_j)$ is a limit of nonnegative numbers, and $K$ is
Hermitian as a limit of Hermitian functions; so $K$ is positive definite. This allows us to define kernels
by series and limits.

_Eigenvalues of Gram matrices are stable under perturbations._ If $G$ and $E$ are Hermitian
$n times n$ matrices, with eigenvalues $lambda_1 (G) >= dots >= lambda_n (G)$, then
$ abs(lambda_j (G + E) - lambda_j (G)) <= norm(E)_2 quad "for" j = 1, dots, n, $ <eq:rkhs-weyl>
where $norm(E)_2$ is the spectral norm (_Weyl's inequality_). For the smallest eigenvalue, which decides
positive (semi)definiteness, the Rayleigh quotient gives it in one line:
$ lambda_n (G + E) = min_(norm(z)_2 = 1) z^* (G + E) z >= min_(norm(z)_2 = 1) z^* G z - norm(E)_2 = lambda_n (G) - norm(E)_2 , $
and symmetrically with $G$ and $G + E$ exchanged; the general case follows in the same way from the
Courant–Fischer min-max characterization. Hence a positive definite $G$ stays positive definite under
every Hermitian perturbation with $norm(E)_2 < lambda_n (G)$ (positive definiteness is an _open_
condition), and if $G$ is positive semidefinite, then $G + E$ has no eigenvalue below $-norm(E)_2$: a Gram
matrix computed in floating point arithmetic is "positive semidefinite up to rounding".

This stability is special to Hermitian (more generally, normal) matrices, as the following example from
the lecture shows. For $a >= 0$ and $epsilon > 0$ let
$ A = mat(-a, 1; 0, -a), quad E_epsilon = mat(0, 0; -epsilon, 0), quad norm(E_epsilon)_2 = epsilon . $
The double eigenvalue $-a$ of $A$ becomes the pair $-a plus.minus i sqrt(epsilon)$ of $A + E_epsilon$
(the characteristic polynomial is $(lambda + a)^2 + epsilon$). A perturbation of size $epsilon$ moves the
eigenvalues by $sqrt(epsilon) >> epsilon$, and even off the real axis. (With $+epsilon$ instead of
$-epsilon$ the eigenvalues $-a plus.minus sqrt(epsilon)$ stay real but still move by $sqrt(epsilon)$.)
For the linear system $dot(x) = (A + E_epsilon) x$ this changes the qualitative behaviour of the
solutions: for $a > 0$, non-oscillating decay to $0$ becomes decay along spirals.
@fig:rkhs-eigenvalue-stability contrasts the two situations.

#figure(
  grid(
    columns: 2,
    column-gutter: 2.5em,
    align: bottom,
    cetz.canvas(length: 1cm, {
      import cetz.draw: *
      line((-1.0, 0), (5.6, 0), mark: (end: ">", fill: black), stroke: 0.6pt)
      content((5.6, -0.3), $RR$)
      line((0, -0.12), (0, 0.12), stroke: 0.6pt)
      content((0, -0.4), $0$)
      arc((0.6, 0), start: 0deg, stop: 180deg, radius: 0.6, stroke: (dash: "dashed", paint: luma(120), thickness: 0.5pt))
      let eps = 0.35
      for (k, lam) in ((4, 0.6), (3, 1.7), (2, 2.6), (1, 4.3)) {
        rect((lam - eps, -0.09), (lam + eps, 0.09), fill: luma(215), stroke: none)
        line((lam - 0.09, -0.09), (lam + 0.09, 0.09), stroke: 0.9pt)
        line((lam - 0.09, 0.09), (lam + 0.09, -0.09), stroke: 0.9pt)
        content((lam, 0.45), text(size: 9pt, $lambda_#k$))
      }
      content((2.3, -1.1), text(size: 9pt)[Hermitian $G$: each eigenvalue moves at most $norm(E)_2$])
    }),
    cetz.canvas(length: 1cm, {
      import cetz.draw: *
      line((-2.0, 0), (1.2, 0), mark: (end: ">", fill: black), stroke: 0.6pt)
      line((0, -1.6), (0, 1.8), mark: (end: ">", fill: black), stroke: 0.6pt)
      content((1.2, -0.3), $RR$)
      content((0.35, 1.75), $i RR$)
      let a = -0.8
      circle((a, 0), radius: 0.4, stroke: (dash: "dashed", paint: luma(120), thickness: 0.5pt))
      line((a - 0.09, -0.09), (a + 0.09, 0.09), stroke: 0.9pt)
      line((a - 0.09, 0.09), (a + 0.09, -0.09), stroke: 0.9pt)
      content((a, -0.62), text(size: 9pt, $-a$))
      circle((a, 1.0), radius: 0.07, fill: black)
      circle((a, -1.0), radius: 0.07, fill: black)
      content((a - 0.95, 1.0), text(size: 9pt, $-a + i sqrt(epsilon)$))
      content((a - 0.95, -1.0), text(size: 9pt, $-a - i sqrt(epsilon)$))
      content((-0.4, -2.2), text(size: 9pt)[Jordan block: eigenvalues move by $sqrt(epsilon)$])
    }),
  ),
  caption: [Left: under a Hermitian perturbation $E$, the eigenvalues of a Hermitian matrix (crosses) stay
    real and in the shaded intervals of radius $norm(E)_2$; the dashed arc of radius $lambda_n$ around $0$
    indicates that the smallest eigenvalue stays positive if $norm(E)_2 < lambda_n$. Right: the double
    eigenvalue $-a$ of the Jordan block $A$ (cross) splits into $-a plus.minus i sqrt(epsilon)$ (dots) under
    a perturbation of norm $epsilon$ (dashed circle of radius $epsilon$; drawn for $epsilon = 0.16$).
    After a blackboard sketch from the lecture.],
) <fig:rkhs-eigenvalue-stability>

#context-note[
  Kernel ridge regression and Gaussian process regression solve linear systems with matrices $G + lambda N I$
  (@ex:reg-krr) or $G + sigma^2 I$, $G$ a Gram matrix. The shift of all eigenvalues by the regularization
  parameter makes these systems well conditioned and, by @eq:rkhs-weyl, insensitive to rounding errors in
  $G$. For the same reason practitioners add a tiny "jitter" $epsilon I$ to a Gram matrix before a
  Cholesky factorization.
]

== Completion of pre-RKHSs <sec:rkhs-completion>

Our next goal is to construct, for a given positive definite kernel $K$, an RKHS with kernel $K$. By
@lem:rkhs-span-dense, the span of the kernel sections $K_x$ must be dense, and on it the inner product is
dictated by $ip(K_(x'), K_x) = K(x, x')$. This gives an inner product space of functions with continuous
point evaluations, which is in general not complete. Its abstract completion consists of equivalence
classes of Cauchy sequences, not of functions on $X$; we need a completion _inside_ $KK^X$. The natural
idea is to add the pointwise limits of Cauchy sequences. This section clarifies when that works.

#definition(title: [Pre-RKHS and RKHS completion])[
  A _pre-RKHS_ on $X$ is a linear subspace $H_0 subset.eq KK^X$ with an inner product $ip(dot, dot)_(H_0)$
  such that every point evaluation $delta_x: H_0 -> KK$, $x in X$, is continuous. An _RKHS completion_ of
  $H_0$ is an RKHS $H$ on $X$ such that $H_0 subset.eq H$, $ip(f, g)_H = ip(f, g)_(H_0)$ for all
  $f, g in H_0$, and $H_0$ is dense in $H$.
] <def:rkhs-pre-rkhs>

Let $H_0$ be a pre-RKHS and $c_x := norm(delta_x)_(H_0 ')$. If $(f_n)$ is a Cauchy sequence in $H_0$, then
for every $x in X$
$ abs(f_n (x) - f_m (x)) <= c_x norm(f_n - f_m)_(H_0), $
so _every Cauchy sequence in $H_0$ has a pointwise limit_, and it is natural to consider
$ H := {f in KK^X : f "is the pointwise limit of a Cauchy sequence in" H_0} . $ <eq:rkhs-completion-space>
We would like to set $norm(f)_H := lim_n norm(f_n)_(H_0)$ if $f_n -> f$ pointwise (the limit exists
since $abs(norm(f_n) - norm(f_m)) <= norm(f_n - f_m)$). For this to be well defined, two Cauchy sequences
with the same pointwise limit must have the same limit of norms. Taking differences leads to the condition
$ (f_n) "Cauchy sequence in" H_0 "and" f_n -> 0 "pointwise" quad ==> quad norm(f_n)_(H_0) -> 0 , $ <eq:rkhs-completion-condition>
which, by the next theorem, is necessary and sufficient.

#theorem(title: [RKHS completion])[
  Let $H_0$ be a pre-RKHS on $X$.
  + $H_0$ has an RKHS completion if and only if @eq:rkhs-completion-condition holds.
  + An RKHS completion is unique: if it exists, it is the space $H$ of @eq:rkhs-completion-space with
    $ norm(f)_H = lim_(n -> oo) norm(f_n)_(H_0) quad "and" quad ip(f, g)_H = lim_(n -> oo) ip(f_n, g_n)_(H_0), $
    where $(f_n)$ and $(g_n)$ are any Cauchy sequences in $H_0$ converging pointwise to $f$ and $g$.
    Moreover, every such sequence converges to its pointwise limit in the norm of $H$.
] <thm:rkhs-completion>

#proof[
  #emph[Necessity of @eq:rkhs-completion-condition.] Let $tilde(H)$ be an RKHS completion of $H_0$, and let
  $(f_n)$ be a Cauchy sequence in $H_0$ with $f_n (x) -> 0$ for all $x$. Since the norms of $H_0$ and
  $tilde(H)$ agree on $H_0$, $(f_n)$ is a Cauchy sequence in the Hilbert space $tilde(H)$, so it converges
  in $tilde(H)$ to some $f in tilde(H)$. Norm convergence in the RKHS $tilde(H)$ implies pointwise
  convergence (@prop:rkhs-norm-convergence (i)), so $f(x) = lim_n f_n (x) = 0$ for all $x$. Thus $f = 0$
  and $norm(f_n)_(H_0) = norm(f_n - f)_(tilde(H)) -> 0$.

  _Uniqueness (part (ii))._ Let $tilde(H)$ be any RKHS completion; we show that it is determined by $H_0$.
  If $f in tilde(H)$, density gives $f_n in H_0$ with $f_n -> f$ in $tilde(H)$; then $(f_n)$ is a Cauchy
  sequence in $H_0$ converging pointwise to $f$ (@prop:rkhs-norm-convergence (i)), so $f in H$.
  Conversely, if $f in H$ with a Cauchy sequence $(f_n)$ in $H_0$ converging pointwise to $f$, then $(f_n)$
  converges in the Hilbert space $tilde(H)$ to some $g$, hence pointwise to $g$, so $f = g in tilde(H)$ and
  $f_n -> f$ in $tilde(H)$. Thus $tilde(H) = H$ as sets, every such sequence converges to $f$ in
  $tilde(H)$, and $ip(f, g)_(tilde(H)) = lim_n ip(f_n, g_n)_(H_0)$ by continuity of the inner product. (Alternatively, the norm
  $lim_n norm(f_n)_(H_0)$ determines the inner product through the polarization identity
  $ip(f, g) = 1/4 sum_(k=0)^3 i^k norm(f + i^k g)^2$ for $KK = CC$ and
  $ip(f, g) = 1/4 (norm(f + g)^2 - norm(f - g)^2)$ for $KK = RR$, @thm:app-projection.)

  #emph[Sufficiency of @eq:rkhs-completion-condition.] Assume @eq:rkhs-completion-condition holds, and let $H$ be
  defined by @eq:rkhs-completion-space. We show in five steps that $H$, with the inner product from (ii), is an RKHS
  completion of $H_0$. For $f in H$ we call a Cauchy sequence $(f_n)$ in $H_0$ with $f_n -> f$ pointwise an
  _approximating sequence_ of $f$.

  _Step 1: $H$ is a linear subspace of $KK^X$ containing $H_0$._ If $(f_n)$, $(g_n)$ approximate $f, g in H$
  and $alpha in KK$, then $(alpha f_n + g_n)$ is a Cauchy sequence in $H_0$ converging pointwise to
  $alpha f + g$. Every $f in H_0$ is approximated by the constant sequence $f_n = f$.

  _Step 2: the inner product is well defined._ Let $(f_n)$, $(g_n)$ approximate $f, g in H$. The sequence
  $(ip(f_n, g_n)_(H_0))$ is a Cauchy sequence in $KK$, because Cauchy sequences are bounded, say by $B$, and
  $ abs(ip(f_n, g_n) - ip(f_m, g_m)) <= abs(ip(f_n - f_m, g_n)) + abs(ip(f_m, g_n - g_m)) <= B (norm(f_n - f_m) + norm(g_n - g_m)). $
  If $(tilde(f)_n)$, $(tilde(g)_n)$ are other approximating sequences of $f$ and $g$, then $(f_n - tilde(f)_n)$
  is a Cauchy sequence in $H_0$ that converges pointwise to $0$, so $norm(f_n - tilde(f)_n)_(H_0) -> 0$ by
  @eq:rkhs-completion-condition, and likewise for $g$. The same estimate then shows
  $ip(f_n, g_n) - ip(tilde(f)_n, tilde(g)_n) -> 0$. Hence
  $ip(f, g)_H := lim_n ip(f_n, g_n)_(H_0)$ does not depend on the approximating sequences.

  _Step 3: $ip(dot, dot)_H$ is an inner product extending that of $H_0$._ Sesquilinearity and the Hermitian
  property pass to the limit (with the approximating sequences of Step 1 for linear combinations), and
  $ip(f, f)_H = lim_n norm(f_n)_(H_0)^2 >= 0$. Moreover
  $abs(f(x)) = lim_n abs(f_n (x)) <= c_x lim_n norm(f_n)_(H_0) = c_x norm(f)_H$ for all $x$; so
  $ip(f, f)_H = 0$ forces $f = 0$, and point evaluations are continuous on $H$. Constant sequences show
  $ip(f, g)_H = ip(f, g)_(H_0)$ for $f, g in H_0$.

  _Step 4: approximating sequences converge in $H$; in particular $H_0$ is dense in $H$._ Let $(f_n)$
  approximate $f in H$ and fix $n$. The sequence $(f_m - f_n)_(m in NN)$ is a Cauchy sequence in $H_0$ that
  converges pointwise to $f - f_n$, so it approximates $f - f_n$, and by definition of the norm,
  $ norm(f - f_n)_H = lim_(m -> oo) norm(f_m - f_n)_(H_0) <= sup_(m >= n) norm(f_m - f_n)_(H_0) . $
  The right-hand side tends to $0$ as $n -> oo$ because $(f_n)$ is a Cauchy sequence.

  _Step 5: $H$ is complete._ Let $(h_k)$ be a Cauchy sequence in $H$. By Step 4, there are $g_k in H_0$ with
  $norm(h_k - g_k)_H < 1\/k$. Then
  $ norm(g_k - g_l)_(H_0) = norm(g_k - g_l)_H <= 1/k + norm(h_k - h_l)_H + 1/l, $
  so $(g_k)$ is a Cauchy sequence in $H_0$. Let $h$ be its pointwise limit. Then $h in H$, $(g_k)$
  approximates $h$, and $norm(h - g_k)_H -> 0$ by Step 4. Consequently
  $norm(h_k - h)_H <= 1\/k + norm(g_k - h)_H -> 0$.

  By Steps 1–5, $H$ is an RKHS completion of $H_0$, with the norm and inner product described in (ii).
]

#intuition[
  One can phrase the theorem in terms of the abstract completion $hat(H)_0$ of $H_0$. Every point evaluation
  extends uniquely to a continuous functional $hat(delta)_x$ on $hat(H)_0$, and each $xi in hat(H)_0$ defines
  a function $x |-> hat(delta)_x (xi)$ on $X$. The condition in @eq:rkhs-completion-condition says precisely that
  this map from $hat(H)_0$ to $KK^X$ is injective, so that the abstract completion can be realized as a
  space of functions: no nonzero "ideal element" of $hat(H)_0$ may be invisible to all point evaluations.
]

The condition in @eq:rkhs-completion-condition can fail, so the theorem has content:

#example(title: [A pre-RKHS without RKHS completion])[
  Let $X = NN$ and let $H_0$ be the space of finitely supported functions $f: NN -> KK$ with
  $ ip(f, g)_(H_0) := sum_(n in NN) f(n) overline(g(n)) + (sum_(n in NN) f(n)) overline((sum_(n in NN) g(n))) . $
  This is an inner product, and $abs(f(n)) <= norm(f)_(H_0)$, so $H_0$ is a pre-RKHS. Let
  $f_k := 1/k ind_({1, dots, k})$. Then $sum_n f_k (n) = 1$, so
  $norm(f_k)_(H_0)^2 = 1\/k + 1 -> 1$. On the other hand, $f_k - f_l$ has coordinate sum $0$, so
  $ norm(f_k - f_l)_(H_0) = norm(f_k - f_l)_(ell^2) <= norm(f_k)_(ell^2) + norm(f_l)_(ell^2) = k^(-1\/2) + l^(-1\/2), $
  and $(f_k)$ is a Cauchy sequence. It converges pointwise to $0$, since $f_k (n) = 1\/k$ for $k >= n$. So
  @eq:rkhs-completion-condition fails, and $H_0$ has no RKHS completion. The culprit is the functional
  $f |-> sum_n f(n)$: it is continuous for the norm of $H_0$, but it is not determined by the pointwise
  limit. In the abstract completion, $(f_k)$ converges to a nonzero element on which all point evaluations
  vanish.
] <ex:rkhs-no-completion>

== From kernels to spaces: the Moore–Aronszajn theorem <sec:rkhs-construction>

The kernel of an RKHS is positive definite (@prop:rkhs-kernel-properties). Conversely, every positive
definite kernel is the kernel of exactly one RKHS. This fundamental theorem allows us to _specify a
hypothesis space by writing down a kernel_.

Let $K: X times X -> KK$ be positive definite, and let
$ H_(K,0) := spn{K_x : x in X} = {sum_(i=1)^n a_i K_(x_i) : n in NN, a_i in KK, x_i in X} subset.eq KK^X . $
If $K$ is to be the reproducing kernel, then @prop:rkhs-kernel-properties (ii) and sesquilinearity leave only
one possible inner product on $H_(K,0)$: for $f = sum_(i=1)^n a_i K_(x_i)$ and $g = sum_(j=1)^m b_j K_(y_j)$
we must have
$ ip(f, g)_(H_(K,0)) := sum_(i=1)^n sum_(j=1)^m a_i overline(b_j) K(y_j, x_i) . $ <eq:rkhs-pre-inner-product>
We must show that this does not depend on the representations of $f$ and $g$ as linear combinations of
kernel sections, and that it is definite. For the latter we need the Cauchy–Schwarz inequality for forms
that are only known to be positive #emph[semi]definite.

#lemma(title: [Cauchy–Schwarz inequality for semi-inner products])[
  Let $V$ be a vector space over $KK$ and $s: V times V -> KK$ be sesquilinear (linear in the first,
  conjugate-linear in the second argument), Hermitian ($s(v, u) = overline(s(u, v))$) and positive
  semidefinite ($s(u, u) >= 0$). Then $abs(s(u, v))^2 <= s(u, u) s(v, v)$ for all $u, v in V$.
] <lem:rkhs-cauchy-schwarz>

#proof[
  For $t in KK$,
  $ 0 <= s(u - t v, u - t v) = s(u, u) - overline(t) s(u, v) - t overline(s(u, v)) + abs(t)^2 s(v, v). $
  If $s(v, v) > 0$, take $t = s(u, v) \/ s(v, v)$ to get $0 <= s(u, u) - abs(s(u, v))^2 \/ s(v, v)$. If
  $s(v, v) = 0$, take $t = r s(u, v)$, $r > 0$: $0 <= s(u, u) - 2 r abs(s(u, v))^2$ for all $r > 0$ forces
  $s(u, v) = 0$.
]

#proposition(title: [The pre-RKHS of a kernel])[
  Let $K$ be a positive definite kernel on $X$. Then @eq:rkhs-pre-inner-product is a well-defined inner
  product on $H_(K,0)$. With this inner product, $H_(K,0)$ is a pre-RKHS, and for all $f in H_(K,0)$ and
  $x, x' in X$
  $ f(x) = ip(f, K_x)_(H_(K,0)), quad ip(K_(x'), K_x)_(H_(K,0)) = K(x, x'), quad abs(f(x)) <= sqrt(K(x, x)) norm(f)_(H_(K,0)) . $
] <prop:rkhs-pre-rkhs>

#proof[
  _Well defined._ Let $f = sum_i a_i K_(x_i)$ and $g = sum_j b_j K_(y_j)$. Evaluating the right-hand side of
  @eq:rkhs-pre-inner-product by summing over $i$ first gives
  $ sum_j overline(b_j) sum_i a_i K(y_j, x_i) = sum_j overline(b_j) f(y_j), $
  which depends on $f$ only through its values, not on its representation. Summing over $j$ first and
  using that $K$ is Hermitian gives
  $ sum_i a_i sum_j overline(b_j) K(y_j, x_i) = sum_i a_i overline(sum_j b_j K(x_i, y_j)) = sum_i a_i overline(g(x_i)), $
  which does not depend on the representation of $g$. Hence the value depends only on $f$ and $g$.

  _Inner product._ Sesquilinearity is clear from @eq:rkhs-pre-inner-product, and the Hermitian property
  follows from $K(x_i, y_j) = overline(K(y_j, x_i))$. For $f = sum_i a_i K_(x_i)$,
  $ ip(f, f)_(H_(K,0)) = sum_(i,j) a_i overline(a_j) K(x_j, x_i) = sum_(i,j) overline(a_j) a_i K(x_j, x_i) >= 0 $
  by positive definiteness (with $c = a$ and the roles of the indices exchanged). So
  $s := ip(dot, dot)_(H_(K,0))$ is a positive semidefinite Hermitian sesquilinear form.

  _Reproducing property._ Taking $g = K_x$ in the first formula of the proof gives
  $ip(f, K_x)_(H_(K,0)) = f(x)$, and then $f = K_(x')$ gives $ip(K_(x'), K_x)_(H_(K,0)) = K(x, x')$.

  _Definiteness and continuity of point evaluations._ By @lem:rkhs-cauchy-schwarz,
  $ abs(f(x))^2 = abs(ip(f, K_x)_(H_(K,0)))^2 <= ip(f, f)_(H_(K,0)) ip(K_x, K_x)_(H_(K,0)) = ip(f, f)_(H_(K,0)) K(x, x). $
  If $ip(f, f)_(H_(K,0)) = 0$, then $f(x) = 0$ for all $x$, so $f = 0$. Hence $s$ is an inner product, and the
  same inequality shows $abs(f(x)) <= sqrt(K(x, x)) norm(f)_(H_(K,0))$, so all $delta_x$ are continuous.
]

#theorem(title: [Moore–Aronszajn])[
  Let $K: X times X -> KK$ be a positive definite kernel. Then there is exactly one RKHS on $X$ whose
  reproducing kernel is $K$. It is denoted by $H_K$. The space $H_(K,0) = spn{K_x : x in X}$ is dense in
  $H_K$, and
  $ H_K = {f in KK^X : f "is the pointwise limit of a Cauchy sequence" (f_n) "in" H_(K,0)}, $
  with $norm(f)_(H_K) = lim_(n -> oo) norm(f_n)_(H_(K,0))$ for any such sequence.
  Consequently, the maps
  $ H |-> "the reproducing kernel of" H quad "and" quad K |-> H_K $
  are mutually inverse bijections between the set of RKHSs on $X$ and the set of positive definite kernels
  on $X$.
] <thm:rkhs-moore-aronszajn>

#proof[
  _Existence._ By @prop:rkhs-pre-rkhs, $H_(K,0)$ is a pre-RKHS, and we verify
  @eq:rkhs-completion-condition. Let $(f_n)$ be a Cauchy sequence in $H_(K,0)$ with $f_n (x) -> 0$ for all
  $x$, let $B := sup_n norm(f_n)$, which is finite, and let $epsilon > 0$. Choose $m$ with
  $norm(f_n - f_m) <= epsilon$ for all $n >= m$ and write the fixed function $f_m$ as
  $f_m = sum_(j=1)^p b_j K_(y_j)$. For $n >= m$,
  $ norm(f_n)^2 = ip(f_n, f_n - f_m) + ip(f_n, f_m) <= B epsilon + abs(sum_(j=1)^p overline(b_j) f_n (y_j)), $
  where we used the Cauchy–Schwarz inequality and $ip(f_n, K_(y_j)) = f_n (y_j)$. The last sum is a fixed
  finite linear combination of values of $f_n$, so it tends to $0$ as $n -> oo$. Hence
  $limsup_n norm(f_n)^2 <= B epsilon$, and since $epsilon > 0$ was arbitrary, $norm(f_n) -> 0$. By
  @thm:rkhs-completion, $H_(K,0)$ has an RKHS completion $H_K$, described by the displayed formula.

  $K$ is the reproducing kernel of $H_K$: we have $K_x in H_(K,0) subset.eq H_K$, and for $f in H_K$ we choose
  $f_n in H_(K,0)$ with $f_n -> f$ in $H_K$. Then, using @prop:rkhs-pre-rkhs and
  @prop:rkhs-norm-convergence (i),
  $ ip(f, K_x)_(H_K) = lim_n ip(f_n, K_x)_(H_(K,0)) = lim_n f_n (x) = f(x). $

  _Uniqueness._ Let $H$ be any RKHS with reproducing kernel $K$. Then $K_x in H$ for all $x$, so
  $H_(K,0) subset.eq H$; on $H_(K,0)$ the inner product of $H$ is given by @eq:rkhs-pre-inner-product,
  because $ip(K_(x'), K_x)_H = K(x, x')$ (@prop:rkhs-kernel-properties (ii)) and both forms are sesquilinear;
  and $H_(K,0)$ is dense in $H$ by @lem:rkhs-span-dense. Thus $H$ is an RKHS completion of $H_(K,0)$, and by
  the uniqueness part of @thm:rkhs-completion, $H = H_K$ with the same inner product.

  _Bijection._ The kernel of an RKHS is positive definite by @prop:rkhs-kernel-properties (iii) and (vii),
  so the first map is well defined; the second is well defined by what we just proved. The kernel of $H_K$
  is $K$, and if $H$ is an RKHS with kernel $K$, then $H_K = H$ by uniqueness. So the maps are inverse to
  each other.
]

#example(title: [Finite input spaces])[
  The kernel is to the RKHS what the Gram matrix is to a finite set of vectors: it records all inner
  products of the "coordinate vectors" $K_x$, whose closed span is the space. This is literally true for
  $X = {1, dots, n}$: then $KK^X = KK^n$, and a kernel is a Hermitian positive semidefinite matrix
  $G in KK^(n times n)$ with $K(i, j) = G_(i j)$. The kernel sections are the columns of $G$, so
  $H_K = Ran G$ (a finite-dimensional space is complete). For $f = G a$ and $g = G b$,
  @eq:rkhs-pre-inner-product gives $ip(f, g)_(H_K) = sum_(i,j) a_i overline(b_j) G_(j i) = b^* G a$. With the
  Moore–Penrose pseudoinverse $G^+$, which satisfies $G G^+ G = G$, this can be written as
  $ ip(f, g)_(H_K) = g^* G^+ f, quad f, g in Ran G, $
  since $g^* G^+ f = b^* G G^+ G a = b^* G a$. If $G$ is invertible, then $H_K = KK^n$ with the inner product
  $g^* G^(-1) f$. So a "large" kernel (large eigenvalues) gives a "small" norm, and directions in which $G$
  has small eigenvalues are expensive. This reciprocity between the kernel and the norm reappears in the
  spectral description of $H_K$ in @sec:mercer.
] <ex:rkhs-finite>

For the warm-up example, $K(x, y) = min{x, y}$ is positive definite, being the kernel of the space $H$ of
@prop:rkhs-sobolev, and by uniqueness $H_K = H$. So the boundary condition $f(0) = 0$, the absolute
continuity and the norm $norm(f')_(L^2)$ are all encoded in the function $min{x, y}$.

#context-note[
  The correspondence between kernels and Hilbert spaces goes back to E. H. Moore's work on "positive
  Hermitian matrices" indexed by general sets and was developed systematically by Aronszajn
  @aronszajn1950. Reproducing kernels had appeared earlier in complex analysis (Bergman and Szegő kernels,
  see @ex:rkhs-kernels (iv)) and in Mercer's work on integral equations @mercer1909 (@sec:mercer).
]

== Feature maps and the kernel trick <sec:rkhs-feature-maps>

=== Motivation: linear methods in feature space

Many classical learning algorithms are _linear_: a linear classifier predicts the label of $x in RR^d$ by
the sign of $ip(w, x) + b$, linear regression predicts $ip(w, x) + b$. They are well understood, efficiently
computable and geometrically transparent, but the relationship between inputs and outputs is rarely
linear. In the left panel of @fig:rkhs-kernel-trick-motivation a line separates the two classes; in the
right panel only a curve does.

#figure(
  image("/images/kernel_trick_motivation.jpeg", width: 55%),
  caption: [Two binary classification problems on $X = [0, 1] times [0, 1]$ (blackboard sketch from the
    lecture). Left: the classes are separated by a straight line. Right: a curved decision boundary is
    needed.],
) <fig:rkhs-kernel-trick-motivation>

A classical way out is to transform the inputs first. If one class lies inside a disc and the other in a
surrounding ring (@fig:rkhs-feature-space), no line separates them. But with the _features_
$ Phi(x) := (x_1, x_2, x_1^2 + x_2^2) in RR^3, $
the classes are separated by the plane ${z in RR^3 : z_3 = r^2}$ for a suitable radius $r$: the linear
classifier $sign(ip(w, Phi(x)) + b)$ with $w = (0, 0, 1)$ and $b = -r^2$ has the circle $norm(x) = r$ as
its decision boundary. A _linear_ method applied to the features produces a _nonlinear_ method on the
original inputs.

#figure(
  placement: auto,
  grid(
    columns: 2,
    column-gutter: 2.5em,
    align: bottom,
    cetz.canvas(length: 0.85cm, {
      import cetz.draw: *
      line((-2.4, 0), (2.4, 0), mark: (end: ">", fill: black), stroke: 0.5pt)
      line((0, -2.4), (0, 2.4), mark: (end: ">", fill: black), stroke: 0.5pt)
      content((2.4, -0.3), $x_1$)
      content((0.35, 2.35), $x_2$)
      circle((0, 0), radius: 1.2, stroke: (dash: "dashed", paint: luma(110), thickness: 0.6pt))
      for k in range(11) {
        let th = k * 360deg / 11 + 10deg
        let r = 0.3 + 0.07 * calc.rem(k * 7, 11)
        circle((r * calc.cos(th), r * calc.sin(th)), radius: 0.07, fill: black)
      }
      for k in range(16) {
        let th = k * 22.5deg + 5deg
        let r = 1.55 + 0.1 * calc.rem(k * 3, 5)
        let (px, py) = (r * calc.cos(th), r * calc.sin(th))
        let s = 0.1
        line((px - s, py), (px, py + s), (px + s, py), (px, py - s), close: true, fill: rgb("#4a9a4a"), stroke: 0.4pt)
      }
      content((0, -2.9), text(size: 9pt)[input space $X = RR^2$])
    }),
    cetz.canvas(length: 0.85cm, {
      import cetz.draw: *
      let sy = 0.9
      line((-2.4, 0), (2.4, 0), mark: (end: ">", fill: black), stroke: 0.5pt)
      line((0, -0.2), (0, 4.6 * sy), mark: (end: ">", fill: black), stroke: 0.5pt)
      content((2.4, -0.3), $z_1 = x_1$)
      content((1.5, 4.5 * sy), $z_3 = x_1^2 + x_2^2$)
      line((-2.3, 1.44 * sy), (2.3, 1.44 * sy), stroke: (dash: "dashed", paint: luma(110), thickness: 0.6pt))
      for k in range(11) {
        let th = k * 360deg / 11 + 10deg
        let r = 0.3 + 0.07 * calc.rem(k * 7, 11)
        circle((r * calc.cos(th), r * r * sy), radius: 0.07, fill: black)
      }
      for k in range(16) {
        let th = k * 22.5deg + 5deg
        let r = 1.55 + 0.1 * calc.rem(k * 3, 5)
        let (px, py) = (r * calc.cos(th), r * r * sy)
        let s = 0.1
        line((px - s, py), (px, py + s), (px + s, py), (px, py - s), close: true, fill: rgb("#4a9a4a"), stroke: 0.4pt)
      }
      content((0, -0.8), text(size: 9pt)[feature space, coordinates $(z_1, z_3)$])
    }),
  ),
  caption: [Left: two classes in $RR^2$ that no line separates; the dashed circle is the desired decision
    boundary. Right: the same points after the feature map $Phi(x) = (x_1, x_2, x_1^2 + x_2^2)$, shown in the
    coordinates $(z_1, z_3)$. In feature space the classes are separated by the plane $z_3 = r^2$ (dashed),
    which corresponds to the circle $norm(x) = r$ on the left. (A three-dimensional version of this picture
    appeared in the lecture.)],
) <fig:rkhs-feature-space>

Moreover, many linear algorithms touch the data only through inner products $ip(Phi(x_i), Phi(x_j))$
(for regularized risk minimization we see this in @sec:reg). If these can be computed directly, the
features themselves, which may be very high- or even infinite-dimensional, are never needed. The function
$(x, x') |-> ip(Phi(x'), Phi(x))$ is a positive definite kernel, and conversely every kernel arises in this
way.

=== Feature maps

#definition(title: [Feature map])[
  Let $K: X times X -> KK$. A _feature map_ of $K$ is a map $Phi: X -> H_0$ into a Hilbert space $H_0$ over
  $KK$ such that
  $ K(x, x') = ip(Phi(x'), Phi(x))_(H_0) quad "for all" x, x' in X. $
  The space $H_0$ is called a _feature space_ of $K$. If $K$ is positive definite, the map
  $ Phi_K: X -> H_K, quad Phi_K (x) := K_x = K(dot, x), $
  is a feature map of $K$ by @prop:rkhs-kernel-properties (ii); it is called the _canonical feature map_.
] <def:rkhs-feature-map>

#proposition(title: [Kernels are exactly the functions with a feature map])[
  A function $K: X times X -> KK$ is positive definite if and only if it has a feature map.
] <prop:rkhs-feature-map-pd>

#proof[
  If $K$ is positive definite, then $Phi_K$ is a feature map. Conversely, let $Phi: X -> H_0$ be a feature map
  of $K$. Then $K(x', x) = ip(Phi(x), Phi(x'))_(H_0) = overline(ip(Phi(x'), Phi(x))_(H_0)) = overline(K(x, x'))$,
  and for $c in KK^n$ and $x_1, dots, x_n in X$,
  $ sum_(i,j=1)^n overline(c_i) c_j K(x_i, x_j) = sum_(i,j=1)^n overline(c_i) c_j ip(Phi(x_j), Phi(x_i))_(H_0) = norm(sum_(j=1)^n c_j Phi(x_j))_(H_0)^2 >= 0. #qedhere $
]

This is a flexible way of producing kernels: $X$ can be _any_ set (texts, graphs, molecules, probability
distributions), as long as we can map it into a Hilbert space. Feature maps are far from unique: with an
isometry $U: H_0 -> H_1$, $U compose Phi$ is again a feature map, and even the dimension of the feature
space is not determined:

- The linear kernel $x x'$ on $RR$ has the feature maps $x |-> x in RR$, $x |-> (x, x)\/sqrt(2) in RR^2$, and
  the canonical one $x |-> K_x$, $K_x (t) = x t$, into $H_K = {t |-> a t : a in RR}$.
- For $K(x, x') = (x x' + 1)^2$ on $RR$, expanding
  $(x x' + 1)^2 = x^2 x'^2 + 2 x x' + 1$ shows that $Phi(x) = (x^2, sqrt(2) x, 1) in RR^3$ is a feature map.
- For $K(x, y) = min{x, y}$ on $[0, 1]$, the map $Phi(x) := ind_([0, x]) in L^2 [0, 1]$ is a feature map,
  since $ip(ind_([0, y]), ind_([0, x]))_(L^2) = min{x, y}$.

The RKHS, however, is unique, and it can be described through _any_ feature map: its elements are the
"linear functions of the features".

#proposition(title: [RKHS of a feature map])[
  Let $K$ be a positive definite kernel on $X$ and $Phi: X -> H_0$ a feature map of $K$. For $w in H_0$ define
  the function
  $ V w: X -> KK, quad (V w)(x) := ip(w, Phi(x))_(H_0) . $
  Then:
  + $V$ maps $H_0$ linearly onto $H_K$, that is,
    $ H_K = {x |-> ip(w, Phi(x))_(H_0) : w in H_0}, $
    and $V Phi(x) = K_x$ for all $x in X$.
  + $Ker V = Phi(X)^perp$, and $V$ is an isometric isomorphism of $(Ker V)^perp = overline(spn) Phi(X)$
    onto $H_K$.
  + For every $f in H_K$,
    $ norm(f)_(H_K) = min{norm(w)_(H_0) : w in H_0, V w = f}, $
    and the minimum is attained at exactly one $w$, namely the unique preimage of $f$ in
    $overline(spn) Phi(X)$.
  In particular, $V: H_0 -> H_K$ is bounded with $norm(V) <= 1$, and $V$ is an isometric isomorphism if and
  only if $spn Phi(X)$ is dense in $H_0$.
] <prop:rkhs-feature-representation>

#proof[
  The idea is to transport the Hilbert space structure of $overline(spn) Phi(X)$ to its image under $V$,
  verify that the result is an RKHS with kernel $K$, and conclude with the uniqueness in the Moore–Aronszajn
  theorem.

  $V$ is linear, and $Ker V = Phi(X)^perp$ is closed with
  $(Ker V)^perp = overline(spn) Phi(X) =: W$ (@thm:app-projection). Let $P$ be the orthogonal projection onto
  $W$. Since $w - P w in Ker V$, $V w = V P w$; so $H := V(H_0) = V(W)$, and $V|_W: W -> H$ is a linear
  bijection. The inner product $ip(V u, V v)_H := ip(u, v)_(H_0)$, $u, v in W$, makes $V|_W$ an isometric
  isomorphism; as $W$ is closed in $H_0$, $H$ is a Hilbert space of functions on $X$.

  For $f in H$ let $w_f in W$ be its preimage. The preimages of $f$ in $H_0$ are exactly the vectors
  $w_f + k$ with $k in Ker V$, and since $w_f perp k$,
  $ norm(w_f + k)_(H_0)^2 = norm(w_f)_(H_0)^2 + norm(k)_(H_0)^2 >= norm(w_f)_(H_0)^2 = norm(f)_H^2, $
  with equality if and only if $k = 0$. This proves the formula in (iii) for the space $H$.

  To see that $H$ is an RKHS with kernel $K$, note that $(V Phi(x'))(x) = ip(Phi(x'), Phi(x))_(H_0) = K(x, x')$.
  So $K_(x') = V Phi(x') in H$ with $w_(K_(x')) = Phi(x') in W$, and for $f in H$,
  $ ip(f, K_(x'))_H = ip(w_f, Phi(x'))_(H_0) = (V w_f)(x') = f(x'), $
  which is the reproducing property. By @thm:rkhs-moore-aronszajn, $H = H_K$ with the same inner product.
  This proves (i), (ii) and (iii).

  Finally, $norm(V w)_(H_K) = norm(P w)_(H_0) <= norm(w)_(H_0)$, so $norm(V) <= 1$; and $V$ is injective (and
  then isometric) if and only if $Ker V = {0}$, that is, if and only if $W = H_0$.
]

#example[
  For $K(x, y) = min{x, y}$ and the feature map $Phi(x) = ind_([0, x]) in L^2 [0, 1]$, we get
  $(V w)(x) = integral_0^x w(t) dif t$. If $V w = 0$, then $w = (V w)' = 0$ almost everywhere, so $V$ is injective
  and $H_K = {integral_0^x w(t) dif t : w in L^2 [0, 1]}$ with $norm(V w)_(H_K) = norm(w)_(L^2)$. This recovers
  @prop:rkhs-sobolev without any computation.
]

#remark[
  For $Phi = Phi_K$, $(V w)(x) = ip(w, K_x)_(H_K) = w(x)$, so $V$ is the identity. For every feature map,
  $V compose Phi = Phi_K$: the canonical feature map is the "smallest" one, obtained from any other by the
  contraction $V$, and if $spn Phi(X)$ is dense in $H_0$, then $V$ is unitary and $Phi$ "is" $Phi_K$.
]

=== The kernel trick

Algorithms that use the features only through their inner products can be run _without ever computing
the features_: every occurrence of $ip(Phi(x'), Phi(x))$ is replaced by $K(x, x')$. By
@prop:rkhs-feature-representation, the resulting decision functions $x |-> ip(w, Phi(x))$ are exactly the
elements of $H_K$. A simple classifier illustrates this (real case, $KK = RR$).

#example(title: [A kernelized nearest-mean classifier])[
  Let $D = ((x_1, y_1), dots, (x_N, y_N))$ with $y_i in {-1, 1}$, let $I_plus.minus := {i : y_i = plus.minus 1}$ be
  nonempty and $N_plus.minus := abs(I_plus.minus)$. The nearest-mean classifier assigns to $x$ the label of
  the closer class mean $m_plus.minus := 1/N_plus.minus sum_(i in I_plus.minus) Phi(x_i)$ in feature space. Expanding,
  $ norm(Phi(x) - m_-)^2 - norm(Phi(x) - m_+)^2
    = 2/N_+ sum_(i in I_+) K(x, x_i) - 2/N_- sum_(i in I_-) K(x, x_i) + b, $
  with the constant
  $b = 1/N_-^2 sum_(i, j in I_-) K(x_i, x_j) - 1/N_+^2 sum_(i, j in I_+) K(x_i, x_j)$. So the classifier
  predicts $sign(f(x))$ with $f = sum_(i=1)^N a_i K_(x_i) + b$, $a_i = 2 y_i \/ N_(y_i)$, computed from
  kernel values only. It is linear in feature space (the perpendicular bisector hyperplane of $m_+$ and
  $m_-$) and nonlinear on $X$. For the Gaussian kernel of @ex:rkhs-gaussian, the two sums are
  (unnormalized) kernel density estimates of the two classes.
] <ex:rkhs-nearest-mean>

#context-note[
  Computing inner products of implicit features by a kernel goes back to the "potential function" method
  of Aizerman, Braverman and Rozonoer in the 1960s. It became central to machine learning when Boser, Guyon
  and Vapnik combined it with the maximal margin classifier, which led to support vector machines
  @cortes1995 @vapnik1998. Since then principal component analysis, Fisher discriminant analysis, ridge
  regression, $k$-means and many other linear methods have been "kernelized" @schoelkopf2002. The
  representer theorem (@thm:reg-representer) shows that the solutions of the regularized problems of
  @sec:reg have the form $sum_i a_i K_(x_i)$, just as in @ex:rkhs-nearest-mean.
]

=== The kernel metric

A feature map $Phi: X -> H_0$ of $K$ induces a distance on $X$, which will be useful for continuity:
$ d_Phi (x, x') := norm(Phi(x) - Phi(x'))_(H_0), quad x, x' in X . $
Expanding the square and using $ip(Phi(x), Phi(x')) = K(x', x) = overline(K(x, x'))$,
$ d_Phi (x, x')^2 = K(x, x) - 2 Re K(x, x') + K(x', x') . $ <eq:rkhs-kernel-metric>

#lemma(title: [Kernel metric])[
  Let $K$ be a positive definite kernel on $X$ and $Phi: X -> H_0$ a feature map of $K$.
  + $d_Phi$ is a pseudometric on $X$ (symmetric, satisfies the triangle inequality, $d_Phi (x, x) = 0$), and it
    depends only on $K$, not on the choice of the feature map.
  + $d_Phi$ is a metric if and only if $Phi$ is injective, if and only if $H_K$ separates the points of $X$
    (for $x != x'$ there is $f in H_K$ with $f(x) != f(x')$). In particular, either all feature maps of $K$ are
    injective or none is.
  + Every $f in H_K$ is Lipschitz continuous with respect to $d_Phi$:
    $ abs(f(x) - f(x')) <= norm(f)_(H_K) d_Phi (x, x') quad "for all" x, x' in X. $
] <lem:rkhs-kernel-metric>

#proof[
  (i) Symmetry, the triangle inequality and $d_Phi (x, x) = 0$ are inherited from the norm of $H_0$. By
  @eq:rkhs-kernel-metric, $d_Phi$ is determined by $K$. In particular, $d_Phi = d_(Phi_K)$, where
  $d_(Phi_K) (x, x') = norm(K_x - K_(x'))_(H_K)$.

  (ii) $d_Phi (x, x') = 0$ if and only if $Phi(x) = Phi(x')$; by (i) this does not depend on $Phi$. For
  $Phi_K$: if $K_x = K_(x')$, then $f(x) = ip(f, K_x) = ip(f, K_(x')) = f(x')$ for all $f in H_K$; conversely,
  $f := K_x - K_(x')$ gives $norm(K_x - K_(x'))^2 = f(x) - f(x')$.

  (iii) $abs(f(x) - f(x')) = abs(ip(f, K_x - K_(x'))_(H_K)) <= norm(f)_(H_K) norm(K_x - K_(x'))_(H_K) = norm(f)_(H_K) d_Phi (x, x')$.
]

For $K(x, y) = min{x, y}$ on $[0, 1]$ we get $d_Phi (x, y)^2 = x + y - 2 min{x, y} = abs(x - y)$, so (iii) is the Hölder estimate of @prop:rkhs-sobolev (ii). In general, points that are close in $d_Phi$
cannot be told apart by functions of small norm: $d_Phi$ is the "resolution" of $H_K$.

== Examples and constructions <sec:rkhs-examples>

We collect the most important kernels and the operations that produce new kernels from old ones, starting
with a principle that covers many examples at once.

#proposition(title: [Series kernels])[
  Let $I$ be a countable index set and $(phi_k)_(k in I)$ functions $X -> KK$ with
  $sum_(k in I) abs(phi_k (x))^2 < oo$ for every $x in X$. Then
  $ K(x, x') := sum_(k in I) phi_k (x) overline(phi_k (x')) $
  converges absolutely and defines a positive definite kernel. It has the feature map
  $Phi(x) := (overline(phi_k (x)))_(k in I) in ell^2 (I)$, and
  $ H_K = {sum_(k in I) a_k phi_k : a in ell^2 (I)}, quad norm(f)_(H_K) = min{norm(a)_(ell^2) : f = sum_(k in I) a_k phi_k}, $
  where the series converge absolutely at every point. If, in addition, $(phi_k)$ is _$ell^2$-independent_,
  meaning that $sum_k a_k phi_k (x) = 0$ for all $x$ with $a in ell^2 (I)$ implies $a = 0$, then
  $norm(sum_k a_k phi_k)_(H_K) = norm(a)_(ell^2)$ and $(phi_k)_(k in I)$ is an orthonormal basis of $H_K$.
] <prop:rkhs-series>

#proof[
  For every $a in ell^2 (I)$, the Cauchy–Schwarz inequality gives
  $sum_k abs(a_k phi_k (x)) <= norm(a)_(ell^2) (sum_k abs(phi_k (x))^2)^(1\/2) < oo$; this gives the absolute convergence of all series, including the one defining
  $K$ (take $a = (overline(phi_k (x')))_k$). By assumption $Phi(x) in ell^2 (I)$, and
  $ip(Phi(x'), Phi(x))_(ell^2) = sum_k overline(phi_k (x')) phi_k (x) = K(x, x')$, so $Phi$ is a feature map
  and $K$ is positive definite (@prop:rkhs-feature-map-pd). The operator $V$ of
  @prop:rkhs-feature-representation is $(V a)(x) = sum_k a_k phi_k (x)$, which gives the description of
  $H_K$ and of its norm. $ell^2$-independence means $Ker V = {0}$; then $V$ is an isometric isomorphism of
  $ell^2 (I)$ onto $H_K$ and maps the standard orthonormal basis $(u_k)$ of $ell^2 (I)$ to $V u_k = phi_k$.
]

#example(title: [Basic kernels])[
  + _Linear kernel._ On $X subset.eq RR^d$, $K(x, x') := ip(x, x') = sum_(k=1)^d x_k x'_k$ has the feature map
    $Phi(x) = x$, so $H_K = {ip(w, dot) : w in RR^d}$ with $norm(ip(w, dot))_(H_K) = min norm(w)_2$, the minimum
    over all $w$ inducing the same function on $X$ (if $X$ spans $RR^d$, the representation is unique and
    the norm is $norm(w)_2$). Here $K(x, x) = norm(x)_2^2$, which is unbounded on $RR^d$. In the complex case
    $X subset.eq CC^d$, the kernel $K(z, z') := sum_k z_k overline(z'_k)$ has the feature map
    $Phi(z) = overline(z)$, and $H_K$ consists of the linear functions $z |-> sum_k w_k z_k$.
  + _Polynomial kernels._ For $c >= 0$ and $m in NN$, let $K(x, x') := (ip(x, x') + c)^m$ on $X subset.eq RR^d$.
    Write $tilde(x) := (x_1, dots, x_d, sqrt(c)) in RR^(d+1)$. The multinomial theorem gives
    $ K(x, x') = (sum_(k=1)^(d+1) tilde(x)_k tilde(x)'_k)^m = sum_(alpha in NN_0^(d+1), abs(alpha) = m) m!/(alpha!) tilde(x)^alpha tilde(x)'^alpha, $
    with $alpha! = alpha_1 ! dots.c alpha_(d+1) !$ and $tilde(x)^alpha = product_k tilde(x)_k^(alpha_k)$. So
    $Phi(x) := (sqrt(m! \/ alpha!) tilde(x)^alpha)_(abs(alpha) = m)$ is a feature map into
    $RR^(binom(m+d, d))$, and by @prop:rkhs-series, $H_K$ is spanned by the monomials $x^beta$ appearing
    in the components of $Phi$. For $c > 0$ these are all monomials of degree $<= m$, so $H_K$ is the space of
    polynomials of degree at most $m$ (restricted to $X$); for $c = 0$ it is the space of homogeneous
    polynomials of degree $m$. If $X$ has an interior point, the monomials are linearly independent on $X$,
    and the norm of $f = sum_(abs(beta) <= m) b_beta x^beta$ is, for $c > 0$,
    $ norm(f)_(H_K)^2 = sum_(abs(beta) <= m) (beta! (m - abs(beta))!)/(m! c^(m - abs(beta))) abs(b_beta)^2 . $
    For instance, for $d = 1$, $m = 2$ we get the feature map $(x^2, sqrt(2 c) x, c)$.
  + _Orthonormal series kernels._ Let $mu$ be a measure on $(X, cal(A))$, $(e_k)_(k in NN)$ an orthonormal system
    in $L^2 (mu)$ whose elements are fixed functions $e_k: X -> KK$ (not just classes), and $w_k >= 0$ weights
    with $sup_k w_k < oo$ and $sum_k w_k abs(e_k (x))^2 < oo$ for all $x in X$. Then
    $ K(x, x') := sum_(k=1)^oo w_k e_k (x) overline(e_k (x')) $
    is positive definite (@prop:rkhs-series with $phi_k = sqrt(w_k) e_k$), and with $I_+ := {k : w_k > 0}$,
    $ H_K = {sum_(k in I_+) b_k e_k : sum_(k in I_+) abs(b_k)^2 / w_k < oo}, quad norm(f)_(H_K)^2 = sum_(k in I_+) abs(b_k)^2 / w_k, $
    where $b_k = ip(f, e_k)_(L^2 (mu))$ and the series converge pointwise and in $L^2 (mu)$. Indeed, for
    $a in ell^2 (I_+)$ let $f := sum_(k in I_+) a_k sqrt(w_k) e_k$ (pointwise sum). As $w$ is bounded,
    $(a_k sqrt(w_k)) in ell^2$, so the series converges in $L^2 (mu)$ to some $g$ with
    $ip(g, e_j)_(L^2 (mu)) = a_j sqrt(w_j)$; a subsequence of the partial sums converges to $g$ $mu$-almost
    everywhere @rudin1987[Thm. 3.12], so $f = g$ almost everywhere and $b_j := ip(f, e_j)_(L^2 (mu)) = a_j sqrt(w_j)$.
    In particular $f = 0$ forces $a = 0$, i.e. $(sqrt(w_k) e_k)_(k in I_+)$ is $ell^2$-independent, and
    @prop:rkhs-series gives the claim with $norm(f)_(H_K)^2 = norm(a)_(ell^2)^2 = sum_k abs(b_k)^2 \/ w_k$.
    Large weights make the component along $e_k$ cheap, small weights make it expensive.

    _Example:_ on $X = [-1, 1]$ with Lebesgue measure, the normalized Legendre polynomials
    $e_k := sqrt((2k + 1)\/2) P_k$, $k in NN_0$, form an orthonormal basis of $L^2 [-1, 1]$, and
    $abs(P_k) <= 1$ on $[-1, 1]$. For $w_k := (k + 1)^(-s)$ with $s > 2$ we have
    $sum_k w_k abs(e_k (x))^2 <= sum_k (k + 1)^(-s) (2k + 1)\/2 < oo$, and $H_K$ consists of the functions
    $f = sum_k b_k e_k$ with $sum_k (k + 1)^s abs(b_k)^2 < oo$: the larger $s$, the faster the Legendre
    coefficients must decay. Chebyshev or other Jacobi polynomials (with their orthogonality weights as $mu$)
    work in the same way. Conversely, every continuous kernel on a compact space has such an expansion
    (Mercer's theorem, @thm:mercer); Fourier series kernels on the torus follow in @ex:mercer-torus.
  + _The Hardy space and the Szegő kernel._ Let $X = {z in CC : abs(z) < 1}$ and $phi_n (z) := z^n$,
    $n in NN_0$. Then $sum_n abs(z)^(2n) < oo$, and @prop:rkhs-series gives the kernel
    $ K(z, w) = sum_(n=0)^oo z^n overline(w)^n = 1/(1 - z overline(w)) . $
    The family $(z^n)$ is $ell^2$-independent by the identity theorem for power series. So
    $H_K = {sum_n a_n z^n : sum_n abs(a_n)^2 < oo}$ with $norm(f)^2 = sum_n abs(a_n)^2$: this is the Hardy space
    $H^2$ of the disc, one of the classical RKHSs of complex analysis.
  + _The Brownian motion kernel_ $K(x, y) = min{x, y}$ on $[0, 1]$, with $H_K$ as in @prop:rkhs-sobolev.
] <ex:rkhs-kernels>

The following rules are the main tool for proving that a given function is positive definite.

#proposition(title: [Operations preserving positive definiteness])[
  Let $K, K_1, K_2, K_3, dots$ be positive definite kernels on $X$.
  + For $alpha, beta >= 0$, the kernel $alpha K_1 + beta K_2$ is positive definite.
  + If $K_n (x, x') -> tilde(K)(x, x')$ for all $x, x' in X$, then $tilde(K)$ is positive definite.
  + The product $K_1 K_2$, $(x, x') |-> K_1 (x, x') K_2 (x, x')$, is positive definite.
  + For every function $g: X -> KK$, the kernel $(x, x') |-> g(x) K(x, x') overline(g(x'))$ is positive definite.
  + If $T: tilde(X) -> X$ is any map, then $(u, u') |-> K(T u, T u')$ is positive definite on $tilde(X)$.
  + Let $F(t) = sum_(n=0)^oo a_n t^n$ be a power series with $a_n >= 0$ and radius of convergence
    $rho in (0, oo]$. If $K(x, x) < rho$ for all $x in X$, then $F compose K$,
    $(x, x') |-> sum_n a_n K(x, x')^n$, is positive definite.
] <prop:rkhs-kernel-operations>

#proof[
  In each case the Hermitian property is immediate (in (vi) because the coefficients $a_n$ are real, so
  $F(overline(t)) = overline(F(t))$), and we only check the quadratic forms. Fix $x_1, dots, x_n$ and
  $c in KK^n$.

  (i) $sum overline(c_i) c_j (alpha K_1 + beta K_2)(x_i, x_j) = alpha sum overline(c_i) c_j K_1 (x_i, x_j) + beta sum overline(c_i) c_j K_2 (x_i, x_j) >= 0$.

  (ii) The quadratic form of $tilde(K)$ is the limit of the nonnegative quadratic forms of the $K_n$.

  (iii) This is the _Schur product theorem_. Let $A := (K_1 (x_i, x_j))_(i,j)$ and
  $B := (K_2 (x_i, x_j))_(i,j)$. The Hermitian positive semidefinite matrix $B$ has a spectral decomposition
  $B = sum_(k=1)^n lambda_k v_k v_k^*$ with $lambda_k >= 0$ and $v_k in KK^n$, so
  $B_(i j) = sum_k lambda_k v_(k,i) overline(v_(k,j))$. With $d_(k,j) := c_j overline(v_(k,j))$ we have
  $overline(d_(k,i)) d_(k,j) = overline(c_i) v_(k,i) c_j overline(v_(k,j))$, so
  $ sum_(i,j) overline(c_i) c_j A_(i j) B_(i j) = sum_(k=1)^n lambda_k sum_(i,j) overline(d_(k,i)) d_(k,j) A_(i j) = sum_(k=1)^n lambda_k d_k^* A d_k >= 0 . $

  (iv) With $d_j := c_j overline(g(x_j))$, we get
  $sum_(i,j) overline(c_i) c_j g(x_i) K(x_i, x_j) overline(g(x_j)) = sum_(i,j) overline(d_i) d_j K(x_i, x_j) >= 0$.

  (v) The Gram matrix of $u_1, dots, u_n$ for the new kernel is the Gram matrix of $T u_1, dots, T u_n$
  for $K$.

  (vi) By @eq:rkhs-cs-kernel, $abs(K(x, x')) <= sqrt(K(x, x) K(x', x')) < rho$, so the series converges for
  all $x, x'$. The powers $K^n$ are positive definite by (iii) and induction ($K^0 equiv 1$ is positive
  definite, since $sum overline(c_i) c_j = abs(sum c_j)^2$), the partial sums by (i), and the limit by (ii).
]

#remark[
  The product rule has a natural interpretation in terms of feature maps: if $Phi_1: X -> H_1$ and
  $Phi_2: X -> H_2$ are feature maps of $K_1$ and $K_2$, then $x |-> Phi_1 (x) times.o Phi_2 (x)$ is a feature
  map of $K_1 K_2$ into the Hilbert space tensor product $H_1 times.o H_2$, because
  $ip(u_1 times.o u_2, v_1 times.o v_2) = ip(u_1, v_1) ip(u_2, v_2)$. For finite-dimensional feature spaces this is
  just the map $x |-> (Phi_(1,k)(x) Phi_(2,l)(x))_(k,l)$ into all products of features. Likewise, the sum rule
  corresponds to concatenating feature vectors, $x |-> (Phi_1 (x), Phi_2 (x)) in H_1 plus.o H_2$.
]

#example(title: [Exponential and Gaussian kernels])[
  Let $X subset.eq RR^d$ and $KK = RR$.
  + _Exponential kernel._ $K(x, x') := exp(ip(x, x'))$ is positive definite by
    @prop:rkhs-kernel-operations (vi) applied to the linear kernel and $F = exp$, which has $a_n = 1\/n! > 0$
    and $rho = oo$.
  + _Gaussian kernel._ For $sigma > 0$,
    $ K_sigma (x, x') := exp(- norm(x - x')_2^2 / sigma^2) = e^(-norm(x)_2^2 \/ sigma^2) exp((2 ip(x, x'))/sigma^2) e^(-norm(x')_2^2 \/ sigma^2), $
    as $-norm(x - x')^2 = -norm(x)^2 + 2 ip(x, x') - norm(x')^2$. The middle factor is an exponential kernel
    (of the rescaled inputs $sqrt(2) x \/ sigma$, @prop:rkhs-kernel-operations (v)), and multiplying by
    $g(x) g(x')$ with $g(x) = e^(-norm(x)^2 \/ sigma^2)$ preserves positive definiteness
    (@prop:rkhs-kernel-operations (iv)). So $K_sigma$ is positive definite. It satisfies $K_sigma (x, x) = 1$,
    and its kernel metric
    $ d(x, x')^2 = 2 - 2 exp(-norm(x - x')^2 \/ sigma^2) <= min{2, 2 norm(x - x')^2 \/ sigma^2} $
    (using $1 - e^(-t) <= t$) shows with @lem:rkhs-kernel-metric that every $f in H_(K_sigma)$ is Lipschitz
    continuous with constant $sqrt(2) norm(f)_(H_(K_sigma)) \/ sigma$ and bounded by $norm(f)_(H_(K_sigma))$.
    The parameter $sigma$ is the length scale on which functions in $H_(K_sigma)$ can vary.
  + _Polynomial kernels_ are positive definite also by @prop:rkhs-kernel-operations: $ip(x, x') + c$ is the sum of
    the linear kernel and the constant kernel $c >= 0$, and powers are handled by (iii).
  The Gaussian kernel is in fact strictly positive definite, and even _universal_; see @sec:univ, in
  particular @ex:univ-taylor, and @steinwart2008[Sect. 4.4] for a description of its RKHS.
] <ex:rkhs-gaussian>

Finally, we describe how RKHSs behave under three basic operations on spaces: passing to closed subspaces,
adding kernels, and restricting to subsets of $X$.

#proposition(title: [Subspaces, sums and restrictions])[
  + _Closed subspaces._ Let $H$ be an RKHS on $X$ with kernel $K$, let $tilde(H) subset.eq H$ be a closed
    subspace, and let $P$ be the orthogonal projection onto $tilde(H)$. Then $tilde(H)$ (with the inner product of
    $H$) is an RKHS with kernel
    $ tilde(K)(x, x') = (P K_(x'))(x), quad "i.e." quad tilde(K)_(x') = P K_(x'), $
    and for all $f in H$ and $x in X$,
    $ (P f)(x) = ip(f, tilde(K)_x)_H . $
    Moreover $K = tilde(K) + tilde(K)^perp$, where $tilde(K)^perp$ is the kernel of $tilde(H)^perp$.
  + _Sums._ Let $K_1, K_2$ be positive definite kernels on $X$ and $K := K_1 + K_2$. Then
    $ H_K = H_(K_1) + H_(K_2) = {f_1 + f_2 : f_1 in H_(K_1), f_2 in H_(K_2)}, $
    $ norm(f)_(H_K)^2 = min{norm(f_1)_(H_(K_1))^2 + norm(f_2)_(H_(K_2))^2 : f = f_1 + f_2} . $
    If moreover $H_(K_1) inter H_(K_2) = {0}$, then the decomposition $f = f_1 + f_2$ is unique, the norms
    satisfy $norm(f)_(H_K)^2 = norm(f_1)_(H_(K_1))^2 + norm(f_2)_(H_(K_2))^2$, and $H_K$ is the orthogonal
    direct sum of its closed subspaces $H_(K_1)$ and $H_(K_2)$.
  + _Inclusions._ If $K_1$ and $K - K_1$ are positive definite, then $H_(K_1) subset.eq H_K$, with
    $norm(f)_(H_K) <= norm(f)_(H_(K_1))$ for all $f in H_(K_1)$.
  + _Restrictions._ Let $X_0 subset.eq X$ be nonempty and $K_0 := K|_(X_0 times X_0)$. Then
    $ H_(K_0) = {f|_(X_0) : f in H_K}, quad norm(g)_(H_(K_0)) = min{norm(f)_(H_K) : f in H_K, f|_(X_0) = g}, $
    and the minimum is attained by exactly one $f$, namely the unique extension of $g$ in
    $overline(spn){K_x : x in X_0}$.
] <prop:rkhs-sum-restriction>

#proof[
  (i) Point evaluations remain continuous on the subspace, and $tilde(H)$ is complete as a closed subspace, so
  $tilde(H)$ is an RKHS; we identify its kernel. Let $tilde(K)_(x) := P K_x in tilde(H)$. For $f in H$, using
  that $P$ is self-adjoint,
  $ ip(f, tilde(K)_x)_H = ip(f, P K_x)_H = ip(P f, K_x)_H = (P f)(x) . $
  For $f in tilde(H)$ we have $P f = f$, so this is the reproducing property in $tilde(H)$; by uniqueness of the
  kernel (@prop:rkhs-kernel-properties (i)), $tilde(K)(x, x') = tilde(K)_(x') (x) = (P K_(x'))(x)$ is the kernel
  of $tilde(H)$. Applying this to $tilde(H)^perp$, with projection $I - P$, gives
  $tilde(K)^perp_(x') = K_(x') - P K_(x')$, so $K = tilde(K) + tilde(K)^perp$.

  (ii) On the external orthogonal direct sum $H_0 := H_(K_1) plus.o H_(K_2)$, with inner product
  $ip((u_1, u_2), (v_1, v_2)) := ip(u_1, v_1)_(H_(K_1)) + ip(u_2, v_2)_(H_(K_2))$, consider the map
  $Phi(x) := (K_(1,x), K_(2,x))$, where $K_(i,x) := K_i (dot, x)$. Then
  $ip(Phi(x'), Phi(x))_(H_0) = K_1 (x, x') + K_2 (x, x') = K(x, x')$, so $Phi$ is a feature map of $K$. The
  operator of @prop:rkhs-feature-representation is
  $ V(u_1, u_2)(x) = ip(u_1, K_(1,x))_(H_(K_1)) + ip(u_2, K_(2,x))_(H_(K_2)) = u_1 (x) + u_2 (x), $
  that is, $V(u_1, u_2) = u_1 + u_2$. Both claims of the first part are now
  @prop:rkhs-feature-representation (i) and (iii). The kernel of $V$ is
  ${(g, -g) : g in H_(K_1) inter H_(K_2)}$. If the intersection is ${0}$, $V$ is injective, hence an
  isometric isomorphism of $H_0$ onto $H_K$ by @prop:rkhs-feature-representation (ii), and the images of
  the orthogonal closed subspaces $H_(K_1) plus.o {0}$ and ${0} plus.o H_(K_2)$ are the orthogonal closed
  subspaces $H_(K_1)$ and $H_(K_2)$ of $H_K$.

  (iii) Apply (ii) to $K = K_1 + (K - K_1)$ and take $f_2 = 0$ in the minimum.

  (iv) The restriction $Phi := Phi_K|_(X_0): X_0 -> H_K$ of the canonical feature map satisfies
  $ip(Phi(x'), Phi(x))_(H_K) = K_0 (x, x')$ for $x, x' in X_0$, so it is a feature map of $K_0$.
  Its operator is $(V w)(x) = ip(w, K_x)_(H_K) = w(x)$ for $x in X_0$, that is, $V w = w|_(X_0)$. Now apply
  @prop:rkhs-feature-representation; the space $overline(spn) Phi(X_0)$ is $overline(spn){K_x : x in X_0}$.
]

#example[
  Let $H$ be the space of @prop:rkhs-sobolev and $tilde(H) := {f in H : f(1) = 0} = {K_1}^perp$, which is closed.
  The projection onto $tilde(H)$ is $P f = f - ip(f, K_1) K_1 \/ K(1, 1)$, so by (i) the kernel of $tilde(H)$ is
  $ tilde(K)(x, y) = K(x, y) - (K(x, 1) K(1, y))/K(1, 1) = min{x, y} - x y, $
  the covariance function of the Brownian bridge. By (i), the kernel of the one-dimensional complement
  $spn{K_1}$ is $x y$, and indeed $min{x, y} = (min{x, y} - x y) + x y$.
]

#remark[
  The slogan "$H_(K_1) plus.o H_(K_2)$ is an RKHS with kernel $K_1 + K_2$" requires care: the direct sum
  consists of pairs, and $(f_1, f_2) |-> f_1 + f_2$ is injective only if $H_(K_1) inter H_(K_2) = {0}$. In
  general, $H_K$ is its image with the quotient norm. For instance, $H_(2 K_1) = H_(K_1)$ as sets, with
  $norm(f)_(H_(2 K_1))^2 = min_(f_1) {norm(f_1)^2 + norm(f - f_1)^2} = norm(f)_(H_(K_1))^2 \/ 2$.
]

== Measurability and boundedness <sec:rkhs-measurability>

For the learning problem, the functions in $H$ must be measurable (otherwise $risk(L, P)(f)$ is
undefined), and for many estimates bounded. Both properties can be read off from the kernel. Here $KK$
carries its Borel $sigma$-algebra.

#proposition(title: [Measurability])[
  Let $(X, cal(A))$ be a measurable space and $H$ an RKHS on $X$ with kernel $K$.
  + Every $f in H$ is measurable if and only if $K_x = K(dot, x): X -> KK$ is measurable for every $x in X$.
  + Assume that the conditions in (i) hold and that $H$ is separable, and let $(e_n)_(n in J)$ be an
    orthonormal basis of $H$ ($J$ countable). Then
    $ K(x, x') = sum_(n in J) e_n (x) overline(e_n (x')) quad "and" quad K(x, x) = sum_(n in J) abs(e_n (x))^2 quad "for all" x, x' in X, $
    $K$ is $cal(A) times.o cal(A)$-measurable, $x |-> K(x, x)$ is measurable, and the canonical feature map
    $Phi_K: X -> H$ is measurable with respect to the Borel $sigma$-algebra of $H$ and strongly measurable.
] <prop:rkhs-measurable>

#proof[
  (i) If every $f in H$ is measurable, then in particular every $K_x in H$ is. Conversely, assume all $K_x$
  are measurable. Then every element of $H_(K,0) = spn{K_x}$ is measurable. For $f in H$, choose
  $f_n in H_(K,0)$ with $f_n -> f$ in $H$ (@lem:rkhs-span-dense). Then $f_n -> f$ pointwise
  (@prop:rkhs-norm-convergence (i)), and a pointwise limit of measurable $KK$-valued functions is measurable
  (apply the real case to real and imaginary parts).

  (ii) The coefficients of $K_(x')$ in the orthonormal basis are
  $ip(K_(x'), e_n)_H = overline(ip(e_n, K_(x'))_H) = overline(e_n (x'))$, so we get
  $K_(x') = sum_n overline(e_n (x')) e_n$ with convergence in $H$, hence pointwise. Evaluating at $x$ gives the
  series for $K(x, x')$, and $x' = x$ gives the one for $K(x, x)$. Each term $(x, x') |-> e_n (x) overline(e_n (x'))$
  is $cal(A) times.o cal(A)$-measurable as a product of measurable functions of one variable each, so the
  pointwise limit $K$ is measurable, and so is $x |-> K(x, x)$.

  For $g in H$, the function $x |-> ip(Phi_K (x), g)_H = overline(g(x))$ is measurable, so $Phi_K$ is weakly
  measurable. Since $H$ is separable, Pettis' theorem (@thm:app-bochner-properties (ii)) shows that $Phi_K$
  is strongly measurable and Borel measurable.
]

#remark(title: [Measurable kernels])[
  We call $K$ _measurable_ if it is $cal(A) times.o cal(A)$-measurable. Then every section $K_x$ is
  measurable, hence so is every $f in H_K$; by (ii) the converse holds for separable $H_K$ (e.g. for
  continuous $K$ on a separable space, @prop:rkhs-separable). Strong measurability of $Phi_K$ makes Bochner
  integrals such as $integral h(x, y) Phi_K (x) dif P(x, y)$ meaningful (@sec:mercer,
  @thm:reg-general-representer).
]

The following "norms" of a kernel measure the size of the diagonal, i.e. of the point evaluations
(@prop:rkhs-kernel-properties (iv)).

#definition(title: [Kernel norms])[
  Let $K$ be a positive definite kernel on $X$. We set
  $ abs(K)_oo := sup_(x in X) sqrt(K(x, x)) in [0, oo], $
  and call $K$ _bounded_ if $abs(K)_oo < oo$. If $(X, cal(A), mu)$ is a measure space and $x |-> K(x, x)$ is
  measurable, we set, for $1 <= p < oo$,
  $ abs(K)_p := (integral_X K(x, x)^(p\/2) dif mu(x))^(1\/p) in [0, oo] . $
] <def:rkhs-kernel-norms>

By @eq:rkhs-cs-kernel, $sup_(x, x') abs(K(x, x')) = abs(K)_oo^2$, so $K$ is bounded as a function on
$X times X$ if and only if $abs(K)_oo < oo$. For the Gaussian kernel $abs(K)_oo = 1$, for $min{x, y}$ on
$[0, 1]$ also $abs(K)_oo = 1$, and for the linear kernel on $RR^d$, $abs(K)_oo = oo$. The quantities
$abs(K)_p$ are used in @sec:mercer to embed $H_K$ into $L^p (mu)$ (@thm:mercer-lp-embedding).

The next proposition is used most often later: bounded kernels are exactly those whose RKHS consists of
bounded functions, and then the RKHS norm controls the supremum norm.

#proposition(title: [Bounded kernels])[
  Let $H$ be an RKHS on $X$ with kernel $K$. The following are equivalent:
  + $K$ is bounded, $abs(K)_oo < oo$;
  + every $f in H$ is bounded, $H subset.eq ell^oo (X)$.
  In this case,
  $ norm(f)_oo <= abs(K)_oo norm(f)_H quad "for all" f in H, $
  and the inclusion $id: H -> ell^oo (X)$ is a bounded linear operator with norm exactly $abs(K)_oo$.
] <prop:rkhs-bounded>

#proof[
  (i) $=>$ (ii). By @prop:rkhs-kernel-properties (iv),
  $abs(f(x)) <= sqrt(K(x, x)) norm(f)_H <= abs(K)_oo norm(f)_H$ for all $x$; take the supremum over $x$.

  (ii) $=>$ (i). Consider the family ${delta_x : x in X}$ of continuous linear functionals on the Banach space
  $H$. For each fixed $f in H$, $sup_(x in X) abs(delta_x (f)) = norm(f)_oo < oo$ by (ii). By the uniform
  boundedness principle (@thm:app-uniform-boundedness), $sup_(x in X) norm(delta_x)_(H') < oo$. Since
  $norm(delta_x)_(H') = sqrt(K(x, x))$ by @prop:rkhs-kernel-properties (iv), this says $abs(K)_oo < oo$.

  _Norm of the inclusion._ Interchanging two suprema,
  $ norm(id) = sup_(norm(f)_H <= 1) sup_(x in X) abs(f(x)) = sup_(x in X) sup_(norm(f)_H <= 1) abs(delta_x (f)) = sup_(x in X) norm(delta_x)_(H') = abs(K)_oo . #qedhere $
]

#remark[
  If $K$ is bounded and every $K_x$ is measurable, then $H_K$ consists of bounded measurable functions, and
  for every probability measure $P_X$ on $X$,
  $ norm(f)_(L^oo (P_X)) <= norm(f)_oo <= abs(K)_oo norm(f)_(H_K) quad "for all" f in H_K . $
  So $H_K$ embeds continuously into $L^oo (P_X)$ and into every $L^p (P_X)$. Combined with the continuity of
  the risk on $L^oo (P_X)$ (@prop:loss-risk-continuity), this is the mechanism behind the existence of
  regularized minimizers in @thm:reg-existence.
]

== Continuity, compactness and separability <sec:rkhs-continuity>

Throughout this section, $(X, tau)$ is a topological space. We ask when the functions in $H_K$ are
continuous, when the unit ball of $H_K$ is compact in the supremum norm, and when $H_K$ is separable. Since
$K_x in H_K$, a necessary condition for $H_K subset.eq C(X)$ is that all sections $K_x$ are continuous.

#definition(title: [Separately continuous kernel])[
  A positive definite kernel $K$ on $X$ is _separately continuous_ if $K_x = K(dot, x)$ is continuous for every
  $x in X$. (Since $K(x, dot) = overline(K_x)$, then also $K(x, dot)$ is continuous for every $x$.)
] <def:rkhs-separately-continuous>

#proposition(title: [Continuous functions in $H_K$])[
  Let $H$ be an RKHS on $X$ with kernel $K$.
  + If $K$ is separately continuous and $x |-> K(x, x)$ is locally bounded (every point has a neighbourhood on
    which it is bounded), then $H subset.eq C(X)$, and norm convergence in $H$ implies uniform convergence on
    every set on which $x |-> K(x, x)$ is bounded, in particular locally uniform convergence. Conversely,
    if $H subset.eq C(X)$, then $K$ is separately continuous and $x |-> K(x, x)$ is bounded on every compact
    subset of $X$.
  + $K$ is bounded and separately continuous if and only if $H subset.eq C_b (X)$. In this case the inclusion
    $id: H -> C_b (X)$ is bounded with norm $abs(K)_oo$, where $C_b (X)$ carries the supremum norm.
] <prop:rkhs-continuous>

#proof[
  (i) Let $f in H$ and $x_0 in X$. Choose a neighbourhood $U$ of $x_0$ with $sup_(x in U) K(x, x) < oo$ and
  $f_n in H_(K,0)$ with $f_n -> f$ in $H$ (@lem:rkhs-span-dense). The $f_n$ are finite linear combinations of
  continuous functions $K_x$, hence continuous, and by @prop:rkhs-norm-convergence (i) they converge to $f$
  uniformly on $U$. A uniform limit of continuous functions on $U$ is continuous on $U$ (with the subspace
  topology), and since $U$ is a neighbourhood of $x_0$, $f$ is continuous at $x_0$. The statement about
  uniform convergence is @prop:rkhs-norm-convergence (i).

  Conversely, let $H subset.eq C(X)$. Then $K_x in H$ is continuous for every $x$. Let $C subset.eq X$ be
  compact. For every $f in H$, the continuous function $f$ is bounded on $C$, that is,
  $sup_(x in C) abs(delta_x (f)) < oo$. By the uniform boundedness principle
  (@thm:app-uniform-boundedness), $sup_(x in C) norm(delta_x)_(H') = sup_(x in C) sqrt(K(x, x)) < oo$.

  (ii) If $K$ is bounded and separately continuous, then $H subset.eq C(X)$ by (i) and $H subset.eq ell^oo (X)$ by
  @prop:rkhs-bounded, so $H subset.eq C_b (X)$. Conversely, if $H subset.eq C_b (X)$, then all $K_x in H$ are
  continuous, and $K$ is bounded by @prop:rkhs-bounded. The norm of the inclusion is computed in
  @prop:rkhs-bounded, since $C_b (X)$ carries the norm of $ell^oo (X)$.
]

The local boundedness assumption in (i) cannot be dropped, and separate continuity is much weaker than joint
continuity, as the following example shows.

#example(title: [Separately continuous, but not continuous])[
  Let $X = [0, 1]$, and for $n in NN$ let $phi_n$ be the "tent" function that vanishes outside
  $[1\/(n+1), 1\/n]$, is linear on both halves of this interval, and takes the value $1$ at its midpoint
  $t_n$. The supports of the $phi_n$ overlap at most at endpoints, where the functions vanish, so for each $t$
  at most one $phi_n (t)$ is nonzero. For a sequence $(h_n)$ of positive numbers, the functions
  $h_n phi_n$ satisfy $sum_n abs(h_n phi_n (t))^2 < oo$ for every $t$ (at most one term is nonzero), so by
  @prop:rkhs-series
  $ K(s, t) := sum_(n=1)^oo h_n^2 phi_n (s) phi_n (t) $
  is a positive definite kernel on $[0, 1]$, with feature map $Phi(t) = (h_n phi_n (t))_n in ell^2$, and
  $H_K = {sum_n a_n h_n phi_n : a in ell^2}$.

  _$K$ is separately continuous._ For fixed $t$, $K_t = h_m^2 phi_m (t) phi_m$ if $phi_m (t) != 0$ for some
  (then unique) $m$, and $K_t = 0$ otherwise; in both cases $K_t$ is continuous.

  _$K$ is not continuous._ Take $h_n = 1$ for all $n$. Then $K$ is bounded by $1$, so
  $H_K subset.eq C_b [0, 1]$ by @prop:rkhs-continuous (ii). But $K(t_n, t_n) = 1$ and $K(0, 0) = 0$, so the
  diagonal is discontinuous at $0$, and $K$ is not continuous on $[0, 1]^2$. Accordingly
  (@prop:rkhs-continuity-equivalences below), the feature map is not continuous at $0$:
  $norm(Phi(t_n) - Phi(0))_(ell^2) = 1$ for all $n$, although $ip(w, Phi(t_n))_(ell^2) = w_n -> 0$ for every
  $w in ell^2$ (in fact $Phi$ is weakly continuous).

  _Local boundedness is needed in @prop:rkhs-continuous (i)._ Now take $h_n = n$. The kernel is still separately
  continuous, but $K(t_n, t_n) = n^2$ is unbounded near $0$. With $a = (1\/n)_n in ell^2$ we obtain the function
  $f := sum_n (1\/n) n phi_n = sum_n phi_n in H_K$, which satisfies $f(t_n) = 1$ for all $n$ and $f(0) = 0$,
  so $f$ is not continuous at $0$.
] <ex:rkhs-separately-continuous>

For jointly continuous kernels the situation is much cleaner: continuity of the kernel is equivalent to
continuity of any of its feature maps.

#proposition(title: [Continuity of kernels and feature maps])[
  Let $K$ be a positive definite kernel on $X$ and $Phi: X -> H_0$ any feature map of $K$. The following are
  equivalent:
  + $K: X times X -> KK$ is continuous (with respect to the product topology);
  + $K$ is separately continuous and $x |-> K(x, x)$ is continuous;
  + $Phi$ is continuous;
  + the identity map $(X, tau) -> (X, d_Phi)$ is continuous, i.e. every open $d_Phi$-ball
    ${x' in X : d_Phi (x, x') < epsilon}$ is open in $tau$.
  If these conditions hold, then $H_K subset.eq C(X)$. In particular, if one feature map of $K$ is continuous,
  then all of them are.
] <prop:rkhs-continuity-equivalences>

#proof[
  (i) $=>$ (ii). The maps $x |-> (x, x_0)$ and $x |-> (x, x)$ from $X$ to $X times X$ are continuous, so
  $K_(x_0) = K(dot, x_0)$ and $x |-> K(x, x)$ are continuous as compositions of continuous maps.

  (ii) $=>$ (iii). Fix $x_0 in X$. By @eq:rkhs-kernel-metric,
  $ norm(Phi(x) - Phi(x_0))_(H_0)^2 = K(x, x) - 2 Re K(x, x_0) + K(x_0, x_0) =: g(x) . $
  By (ii), $g$ is continuous (it involves the diagonal and the section $K_(x_0)$), and $g(x_0) = 0$. Hence
  for every $epsilon > 0$ there is a neighbourhood $U$ of $x_0$ with $g(x) < epsilon^2$ for $x in U$, that is,
  $norm(Phi(x) - Phi(x_0)) < epsilon$ on $U$. So $Phi$ is continuous at $x_0$.

  (iii) $=>$ (iv). For fixed $x$, the function $x' |-> d_Phi (x, x') = norm(Phi(x) - Phi(x'))$ is continuous as
  a composition of continuous maps, so the ball ${x' : d_Phi (x, x') < epsilon}$, its preimage of
  $(-oo, epsilon)$, is open. Every $d_Phi$-open set is a union of such balls, hence open.

  (iv) $=>$ (iii). Let $x_0 in X$ and $epsilon > 0$. The set
  ${x : norm(Phi(x) - Phi(x_0)) < epsilon} = {x : d_Phi (x_0, x) < epsilon}$ is a $d_Phi$-ball, hence open by (iv),
  and it contains $x_0$. So $Phi$ is continuous at $x_0$.

  (iii) $=>$ (i). Let $(x_0, x'_0) in X times X$ and $epsilon > 0$. For all $x, x' in X$,
  $ abs(K(x, x') - K(x_0, x'_0)) &= abs(ip(Phi(x'), Phi(x)) - ip(Phi(x'_0), Phi(x_0))) \
    &<= abs(ip(Phi(x') - Phi(x'_0), Phi(x))) + abs(ip(Phi(x'_0), Phi(x) - Phi(x_0))) \
    &<= norm(Phi(x') - Phi(x'_0)) norm(Phi(x)) + norm(Phi(x'_0)) norm(Phi(x) - Phi(x_0)) . $
  By continuity of $Phi$ there are neighbourhoods $U$ of $x_0$ and $U'$ of $x'_0$ on which
  $norm(Phi(x) - Phi(x_0)) < delta$ and $norm(Phi(x') - Phi(x'_0)) < delta$, where $delta in (0, 1]$ is chosen such that
  $delta (norm(Phi(x_0)) + 1 + norm(Phi(x'_0))) < epsilon$. On the neighbourhood $U times U'$ of $(x_0, x'_0)$ we
  then have $norm(Phi(x)) < norm(Phi(x_0)) + 1$ and hence $abs(K(x, x') - K(x_0, x'_0)) < epsilon$.

  _Consequences._ If (iii) holds for one feature map, then (i) holds, and (i) does not involve $Phi$; so (iii)
  holds for every feature map. Applying this to $Phi_K$, and using $abs(f(x) - f(x_0)) <= norm(f)_(H_K) norm(K_x - K_(x_0))_(H_K)$
  (@lem:rkhs-kernel-metric (iii)), every $f in H_K$ is continuous.
]

The conclusion $H_K subset.eq C(X)$ holds for every continuous kernel, bounded or not (e.g. the linear and
polynomial kernels on $RR^d$). On a compact space, a continuous kernel is bounded, and then
$H_K subset.eq C(X)$ with $norm(f)_oo <= abs(K)_oo norm(f)_(H_K)$.

In learning theory it matters that balls of the hypothesis space are _compact_ in the supremum norm: they
can then be covered by finitely many small sup-norm balls, and the number of such balls (the covering
number) controls how far the empirical risk can deviate from the risk uniformly over the ball.

#proposition(title: [Compact embedding into $ell^oo (X)$])[
  Let $K$ be a positive definite kernel on a set $X$ with canonical feature map $Phi_K$. If $Phi_K (X)$ is
  relatively compact in $H_K$ (that is, its closure is compact), then $K$ is bounded and the inclusion
  $id: H_K -> ell^oo (X)$ is a compact operator. This holds in particular if $X$ is a compact topological space
  and $K$ is continuous.
] <prop:rkhs-compact-embedding>

#proof[
  The idea is to regard the functions of $H_K$ as functions on the compact metric space
  $Z := overline(Phi_K (X)) subset.eq H_K$, where the unit ball becomes a bounded equicontinuous family.

  _Boundedness._ As a compact set, $Z$ is bounded in $H_K$: $R := sup_(v in Z) norm(v)_(H_K) < oo$. Hence
  $abs(K)_oo = sup_x norm(K_x)_(H_K) <= R$, and $id$ is bounded by @prop:rkhs-bounded.

  _Transfer to $Z$._ For $f in H_K$ let $hat(f)(v) := ip(f, v)_(H_K)$, $v in Z$, so that
  $hat(f)(Phi_K (x)) = f(x)$. For $f$ in the closed unit ball $B$ of $H_K$ and $v, v' in Z$,
  $ abs(hat(f)(v)) <= R quad "and" quad abs(hat(f)(v) - hat(f)(v')) <= norm(v - v')_(H_K), $
  so $cal(F) := {hat(f) : f in B} subset.eq C(Z)$ is uniformly bounded and equicontinuous on the compact
  metric space $Z$, hence relatively compact in $(C(Z), norm(dot)_oo)$ by the Arzelà–Ascoli theorem
  (@thm:app-arzela-ascoli).

  _Back to $X$._ The linear map $J: C(Z) -> ell^oo (X)$, $J g := g compose Phi_K$, satisfies
  $norm(J g)_oo <= norm(g)_oo$ and $J hat(f) = f$. So $id(B) = J(cal(F))$ is the continuous image of a
  relatively compact set, hence relatively compact in $ell^oo (X)$, and $id$ is compact.

  _The special case._ If $X$ is compact and $K$ continuous, then $Phi_K$ is continuous
  (@prop:rkhs-continuity-equivalences), so $Phi_K (X)$ is compact.
]

#remark[
  If $Phi: X -> H_0$ is any feature map with $Phi(X)$ relatively compact, then so is $Phi_K (X) = V(Phi(X))$,
  since the operator $V$ of @prop:rkhs-feature-representation is continuous. If $X$ is compact and $K$
  continuous, then $H_K subset.eq C(X)$, and the closed unit ball $B$ of $H_K$ is even a compact subset of
  $C(X)$: it is relatively compact by the proposition, and closed, because a uniform limit of functions in
  $B$ lies in $B$ by @prop:rkhs-norm-convergence (iii).
]

Finally, separability of $H_K$ gives countable orthonormal bases, used for series expansions of the
kernel, and is needed for the Bochner integrals in @sec:mercer and @sec:reg (@prop:rkhs-measurable (ii)).

#proposition(title: [Separability])[
  Let $(X, tau)$ be a separable topological space and $K$ a continuous positive definite kernel on $X$. Then
  $H_K$ is separable.
] <prop:rkhs-separable>

#proof[
  Let $A subset.eq X$ be countable and dense. The canonical feature map $Phi_K$ is continuous by
  @prop:rkhs-continuity-equivalences, so $Phi_K (A)$ is dense in $Phi_K (X)$: by continuity,
  $Phi_K (X) = Phi_K (overline(A)) subset.eq overline(Phi_K (A))$. Let $QQ_KK := QQ$ if $KK = RR$ and $QQ_KK := QQ + i QQ$ if $KK = CC$. The set
  $ M := {sum_(i=1)^n q_i K_(a_i) : n in NN, q_i in QQ_KK, a_i in A} $
  is countable, and its closure is a closed subspace (the closure of the $QQ_KK$-span equals the closure of
  the $KK$-span) containing $overline(Phi_K (A)) supset.eq Phi_K (X)$. Therefore it contains the closed span of
  $Phi_K (X)$, which is $H_K$ by @lem:rkhs-span-dense. So $M$ is a countable dense subset of $H_K$.
]

Continuity cannot be dropped: for the kernel $K(x, x') = ind_({x = x'})$ on $X = RR$ (which is positive definite,
its Gram matrices at distinct points being identity matrices), $H_K = ell^2 (RR)$ is not separable
(@ex:rkhs-exercise-delta).

As a consequence, continuous kernels have series expansions that converge uniformly on compact sets, a
first glimpse of Mercer's theorem (@thm:mercer), which provides a particularly useful orthonormal basis.

#corollary(title: [Expansion in an orthonormal basis])[
  Let $(X, tau)$ be a separable topological space, $K$ a continuous positive definite kernel on $X$, and
  $(e_n)_(n in J)$ an orthonormal basis of $H_K$ ($J$ countable, by @prop:rkhs-separable). Then
  $ K_x = sum_(n in J) overline(e_n (x)) e_n quad "in" H_K quad "and" quad K(x, x') = sum_(n in J) e_n (x) overline(e_n (x')), $
  and the convergence is uniform in $x in C$, respectively in $(x, x') in C times C$, for every compact set
  $C subset.eq X$ (for any enumeration of $J$).
] <cor:rkhs-onb-expansion>

#proof[
  The expansions hold pointwise by the argument in @prop:rkhs-measurable (ii). Let $J = NN$ (the finite case is
  trivial), let $C$ be compact, and let $R_N$ be the orthogonal projection onto
  $overline(spn){e_n : n > N}$. By Parseval's identity,
  $ norm(K_x - sum_(n=1)^N overline(e_n (x)) e_n)_(H_K)^2 = norm(R_N K_x)^2 = K(x, x) - sum_(n=1)^N abs(e_n (x))^2 =: r_N (x) . $
  The functions $r_N$ are continuous ($K$ is continuous, and the $e_n in H_K$ are continuous by
  @prop:rkhs-continuity-equivalences), they decrease monotonically in $N$, and they converge pointwise to $0$.
  By Dini's theorem (@thm:app-dini), $r_N -> 0$ uniformly on $C$. This proves the first claim. For the second,
  since $ip(K_(x'), K_x) - sum_(n <= N) overline(e_n (x')) e_n (x) = ip(R_N K_(x'), R_N K_x)$ by Parseval's
  identity, the Cauchy–Schwarz inequality gives
  $ abs(K(x, x') - sum_(n=1)^N e_n (x) overline(e_n (x'))) = abs(ip(R_N K_(x'), R_N K_x)_(H_K)) <= sqrt(r_N (x) r_N (x')) , $
  which tends to $0$ uniformly on $C times C$.
]

== Summary

- An _RKHS_ is a Hilbert space of functions on $X$ with continuous point evaluations; norm convergence
  implies pointwise convergence, uniformly where $K(x, x)$ is bounded.
- Every RKHS has a unique _reproducing kernel_: $K_x = K(dot, x) in H$, $f(x) = ip(f, K_x)_H$,
  $K(x, x') = ip(K_(x'), K_x)_H$. It is _positive definite_ (all Gram matrices positive semidefinite), and
  $sqrt(K(x, x)) = norm(delta_x)_(H')$.
- _Moore–Aronszajn_: every positive definite $K$ is the kernel of exactly one RKHS $H_K$, the completion of
  $spn{K_x}$ inside $KK^X$; it works because Cauchy sequences converging pointwise to $0$ converge to $0$
  in norm, which can fail for general pre-RKHSs (@thm:rkhs-completion).
- Kernels are exactly the functions $K(x, x') = ip(Phi(x'), Phi(x))$ with a _feature map_ $Phi$, and for
  any feature map $H_K = {ip(w, Phi(dot)) : w in H_0}$ with the minimal-norm representation
  (@prop:rkhs-feature-representation): the _kernel trick_.
- Sums, products, limits, power series with nonnegative coefficients and $g(x) K(x, x') overline(g(x'))$
  preserve positive definiteness; this gives polynomial, exponential and Gaussian kernels. Series kernels
  have RKHSs described by weighted coefficient conditions.
- Regularity is inherited from the kernel: measurable sections give measurable functions, $abs(K)_oo < oo$
  is equivalent to $H_K subset.eq ell^oo (X)$ with $norm(f)_oo <= abs(K)_oo norm(f)_(H_K)$, continuity of
  $K$ is equivalent to continuity of the feature maps and gives $H_K subset.eq C(X)$, and continuous kernels
  on separable spaces have separable RKHSs.

In @sec:mercer we take a different look at $H_K$: when $X$ carries a measure, $H_K$ sits inside
$L^2 (mu)$, and its structure is revealed by the eigenfunctions and eigenvalues of the integral operator with
kernel $K$.

== Notes and further reading

Aronszajn's paper @aronszajn1950 contains the Moore–Aronszajn theorem, the treatment of sums,
restrictions and subspaces, and many other results of this chapter. Our presentation follows Chapter 4 of Steinwart and Christmann @steinwart2008, which also contains a detailed
study of the RKHSs of Gaussian kernels and of the measurability, continuity and separability questions of
@sec:rkhs-measurability and @sec:rkhs-continuity. The approach via pre-RKHSs and their completions is taken
in the modern textbook of Paulsen and Raghupathi @paulsen2016, which also covers interpolation, operations on
kernels, and connections with operator theory and complex analysis. Berlinet and Thomas-Agnan @berlinet2004
emphasize the connections with probability and statistics, in particular Gaussian processes and splines;
Wahba @wahba1990 is the classical reference for spline smoothing in RKHSs, building on Kimeldorf and Wahba
@kimeldorf1971. Cucker and Zhou @cucker2007 study RKHSs from the viewpoint of approximation theory, including
covering numbers of RKHS balls, which quantify the compactness of @prop:rkhs-compact-embedding. For kernel
methods in machine learning and many examples of kernels on structured data, see Schölkopf and Smola
@schoelkopf2002, and for a broader statistical perspective Hastie, Tibshirani and Friedman @hastie2009.

== Exercises

#exercise(title: [$L^2$ is not an RKHS in disguise])[
  Suppose $H subset.eq KK^([0, 1])$ is an RKHS such that every $f in H$ is Lebesgue measurable and square
  integrable, and $f |-> [f]$ (the equivalence class of $f$) is an isometric isomorphism of $H$ onto
  $L^2 [0, 1]$. Derive a contradiction.

  _Hint:_ Fix a countable orthonormal basis $(e_n)$ of $H$. By @prop:rkhs-measurable (ii),
  $K(x, x) = sum_n abs(e_n (x))^2$ is measurable, so some set $A_M := {x : K(x, x) <= M}$ has positive
  measure. Choose infinitely many orthonormal $u_1, u_2, dots in H$ whose classes vanish outside $A_M$ (they
  exist because $L^2 (A_M)$ is infinite-dimensional), and use
  $sum_(k <= n) abs(u_k (x))^2 <= K(x, x)$ (Bessel's inequality applied to $K_x$) to show that
  $n = integral_(A_M) sum_(k <= n) abs(u_k)^2 <= M lambda(A_M)$ for all $n$.
] <ex:rkhs-exercise-l2>

#exercise(title: [A Sobolev space on the real line])[
  Let $H^1 (RR)$ be the space of absolutely continuous (on every bounded interval) functions $f: RR -> RR$ with
  $f, f' in L^2 (RR)$, with inner product $ip(f, g) := integral_RR (f g + f' g') dif x$. Assuming that $H^1 (RR)$
  is a Hilbert space, show that it is an RKHS with kernel $K(x, y) = 1/2 e^(-abs(x - y))$. This is the space
  corresponding to the regularizer $norm(f)_(L^2)^2 + norm(f')_(L^2)^2$ mentioned in @sec:rkhs-warmup.

  _Hint:_ Show $K_y in H^1 (RR)$ and compute $ip(f, K_y)$ by splitting the integral at $y$ and integrating by
  parts on $(-oo, y)$ and $(y, oo)$; use that $K''_y = K_y$ away from $y$, that $K'_y$ jumps by $-1$ at $y$,
  and that $f(x) -> 0$ as $abs(x) -> oo$ for $f in H^1 (RR)$.
] <ex:rkhs-exercise-h1>

#exercise(title: [Aronszajn's criterion])[
  Let $K$ be a positive definite kernel on $X$, $f: X -> KK$ and $r > 0$. Show that $f in H_K$ with
  $norm(f)_(H_K) <= r$ if and only if $(x, x') |-> r^2 K(x, x') - f(x) overline(f(x'))$ is positive definite.

  _Hint:_ For "if", note that $f(x) overline(f(x'))$ is the kernel of the one-dimensional RKHS $spn{f}$ with
  $norm(f) = 1$ (if $f != 0$), that $H_(r^2 K) = H_K$ with $norm(g)_(H_(r^2 K)) = norm(g)_(H_K) \/ r$, and use
  @prop:rkhs-sum-restriction (iii). For "only if", compute
  $sum overline(c_i) c_j (r^2 K(x_i, x_j) - f(x_i) overline(f(x_j)))$ using $f(x_i) = ip(f, K_(x_i))$ and the
  Cauchy–Schwarz inequality.
] <ex:rkhs-exercise-aronszajn>

#exercise(title: [The $delta$-kernel])[
  Let $X$ be any nonempty set and $K(x, x') := ind_({x = x'})$. Show that $K$ is strictly positive definite and
  that $H_K = ell^2 (X)$, the space of functions $f: X -> KK$ with $sum_(x in X) abs(f(x))^2 < oo$ (such functions
  have countable support), with the norm of $ell^2 (X)$. Conclude that $H_K$ is not separable if $X$ is
  uncountable, and explain why this does not contradict @prop:rkhs-separable for $X = RR$.

  _Hint:_ $ell^2 (X)$ is a Hilbert space in which $delta_x$ has norm $1$ and is represented by $ind_({x})$.
] <ex:rkhs-exercise-delta>

#exercise(title: [Uniform convergence of kernel expansions])[
  Let $K$ be the orthonormal series kernel of @ex:rkhs-kernels (iii) built from the normalized Legendre
  polynomials with weights $w_k = (k + 1)^(-s)$, $s > 2$. Show that $K$ is continuous on $[-1, 1]^2$ and
  that $H_K subset.eq C[-1, 1]$. Show that $H_K$ contains all polynomials, and compute the $H_K$-norm of the
  function $x |-> x$.

  _Hint:_ Use the Weierstrass M-test for continuity, and $P_1 (x) = x$.
] <ex:rkhs-exercise-legendre>

#exercise(title: [Weak convergence and interpolation])[
  Let $H$ be an RKHS on $X$ with kernel $K$.
  + Show that a sequence $(f_n)$ in $H$ converges weakly to $f in H$ if and only if it is bounded and converges
    pointwise to $f$.
  + Let $x_1, dots, x_n in X$ and $v in KK^n$, and assume that some $f in H$ satisfies $f(x_i) = v_i$ for all
    $i$. Show that among all such $f$ there is a unique one of minimal norm, that it lies in
    $spn{K_(x_1), dots, K_(x_n)}$, and that, if the Gram matrix $G = (K(x_i, x_j))_(i,j)$ is invertible, it is
    $f = sum_i a_i K_(x_i)$ with $G a = v$ and has norm $(v^* G^(-1) v)^(1\/2)$.

  _Hint:_ For (i), use @prop:rkhs-norm-convergence and the uniform boundedness principle. For (ii), the set of
  interpolants is a closed affine subspace, parallel to ${K_(x_1), dots, K_(x_n)}^perp$.
] <ex:rkhs-exercise-interpolation>
