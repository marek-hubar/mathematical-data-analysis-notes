#import "/template.typ": *

// Local notation for this appendix.
#let TT = math.bb("T")
#let weakto = sym.harpoon.rt
#let Re = math.op("Re")
#let Im = math.op("Im")
#let dist = math.op("dist")
#let HS = math.upright("HS")

= Mathematical Background <sec:app>

This appendix collects the results from measure theory, functional analysis, convex analysis and
approximation theory on which the main text relies. We assume that the reader has seen measure and
integration theory and the basic theory of Banach and Hilbert spaces. The purpose of the appendix is
threefold: to fix notation, to state *precisely* (with all hypotheses) the versions of the results that
the book uses, and to explain where they are used. Results whose proofs are short, or whose proofs
illuminate arguments in the main text, are proved. For the others we give a reference, with a theorem
number where possible.

The appendix is meant to be consulted rather than read from beginning to end. Each section starts with
a few sentences explaining why its results are needed.

*Conventions.* Throughout, $KK in {RR, CC}$ denotes the field of scalars, and all vector spaces are over
$KK$ unless said otherwise. For normed spaces $E$ and $F$ we write $cal(L)(E, F)$ for the space of bounded
linear operators $A: E -> F$ with the operator norm $norm(A) = sup_(norm(x) <= 1) norm(A x)$,
$cal(L)(E) := cal(L)(E, E)$, $E' := cal(L)(E, KK)$ for the (topological) dual space, and
$B_E := {x in E : norm(x) <= 1}$ for the closed unit ball. Inner products are linear in the first and
conjugate-linear in the second argument. For an arbitrary index set $I$ and numbers $a_i in [0, oo]$ we
put $sum_(i in I) a_i := sup {sum_(i in F) a_i : F subset.eq I "finite"}$; if this sum is finite, then at
most countably many $a_i$ are non-zero. Finally, $NN = {1, 2, 3, ...}$.

== Measure theory and probability <sec:app-measure>

The risk $risk(L, P)(f) = integral L(x, y, f(x)) dif P(x, y)$ is the integral of a function of several
variables which, in addition, depends on the function $f$. To define it and to study it as a functional
of $f$ (@sec:loss) we need joint measurability of functions of several variables
(@thm:app-caratheodory, used in @prop:loss-measurability), integrals depending on a parameter (Tonelli's
theorem), and the standard convergence theorems (@thm:app-convergence), which are used in almost every
proof of @sec:loss. Polish spaces appear because they are the natural spaces for which regular conditional
probabilities exist (@lem:learn-regular-conditional) and because the function spaces of @sec:loss on which
the risk is measurable are Polish.

=== Polish spaces

#definition(title: [Polish space])[
  A topological space $Z$ is called *Polish* if it is separable and its topology is induced by a complete
  metric.
] <def:app-polish>

#proposition(title: [Examples and permanence properties])[
  + $RR^d$ and $CC^d$ are Polish, and every closed subset of a Polish space is Polish (with the
    relative topology). In particular every closed set $Y subset.eq RR$ is Polish.
  + Every compact metric space and every separable Banach space is Polish.
  + Finite and countable products of Polish spaces are Polish.
  + If $Z_1, Z_2$ are separable metric spaces, then the Borel σ-algebra of the product is the product of
    the Borel σ-algebras: $borel(Z_1 times Z_2) = borel(Z_1) times.o borel(Z_2)$.
] <prop:app-polish>

#proof[
  (i) The restriction of a complete metric to a closed subset is complete, and subsets of separable metric
  spaces are separable. (ii) A compact metric space is complete, and it is separable because it can be
  covered by finitely many balls of radius $1\/n$ for every $n$; the centres of all these balls form a
  countable dense set. (iii) If $d_k$ are complete metrics on $Z_k$, then
  $d(z, z') := sum_k 2^(-k) min{d_k (z_k, z'_k), 1}$ is a complete metric inducing the product topology, and
  finite sequences of points from countable dense subsets (filled up with a fixed point) form a countable
  dense set. (iv) Since the projections are continuous, $borel(Z_1) times.o borel(Z_2) subset.eq borel(Z_1 times Z_2)$.
  Conversely, a separable metric space has a countable base, so every open subset of $Z_1 times Z_2$ is a
  countable union of products $U_1 times U_2$ of open sets, which lie in $borel(Z_1) times.o borel(Z_2)$;
  see also @kallenberg2002[Lemma 1.2].
]

Part (iv) is what makes Borel functions of several measurable quantities measurable. If $(Omega, cal(A))$
is a measurable space and $g_k: Omega -> Z_k$ ($k = 1, 2$) are measurable maps into separable metric
spaces, then $omega |-> (g_1 (omega), g_2 (omega))$ is measurable with respect to
$borel(Z_1) times.o borel(Z_2) = borel(Z_1 times Z_2)$, so $h(g_1, g_2)$ is measurable for every Borel
(for instance, every continuous) $h: Z_1 times Z_2 -> RR$. A related, simpler observation, for which the
definition of the product σ-algebra suffices: if $L$ is a loss function
(measurable on $X times Y times RR$ with respect to $cal(A) times.o borel(Y) times.o borel(RR)$) and
$f: X -> RR$ is measurable, then $(x, y) |-> (x, y, f(x))$ is measurable, hence so is
$(x, y) |-> L(x, y, f(x))$; this is why the risk in @def:learn-risk is well defined.

Polish spaces are also the setting in which regular conditional probabilities exist; see
@lem:learn-regular-conditional and @dudley2002[Sect. 10.2], @kallenberg2002[Ch. 6].

=== Joint measurability and parameter integrals

A function of two variables that is measurable in each variable separately need not be jointly
measurable. The following theorem shows that joint measurability does hold if the function is continuous in
one of the variables and this variable ranges over a separable metric space. It is the key to the
measurability of the risk as a function of $f$ (@prop:loss-measurability), where it is applied to the
evaluation map $(f, x) |-> f(x)$.

#theorem(title: [Carathéodory functions are jointly measurable])[
  Let $(X, cal(A))$ be a measurable space, let $Z$ be a separable metrizable space (for instance a Polish
  space) with Borel σ-algebra $borel(Z)$, and let $phi: X times Z -> RR$ be a function such that
  + $phi(x, dot): Z -> RR$ is continuous for every $x in X$, and
  + $phi(dot, z): X -> RR$ is $cal(A)$-measurable for every $z in Z$.
  Then $phi$ is $cal(A) times.o borel(Z)$-measurable. The same holds for $KK$-valued $phi$ (apply the
  result to real and imaginary parts).
] <thm:app-caratheodory>

#proof[
  The idea is to approximate $phi(x, z)$ by $phi(x, z_k)$, where $z_k$ is a point of a countable dense
  set close to $z$ that is chosen in a measurable way. Let $d$ be a metric inducing the topology of $Z$ and
  let ${z_1, z_2, ...}$ be dense in $Z$. For $n, k in NN$ let $U_(n,k) := {z in Z : d(z, z_k) < 1\/n}$ and
  $ B_(n,k) := U_(n,k) without union.big_(j < k) U_(n,j). $
  For fixed $n$ the sets $B_(n,k)$, $k in NN$, are Borel and pairwise disjoint, and they cover $Z$ because
  the $z_k$ are dense. Define
  $ phi_n (x, z) := sum_(k=1)^oo phi(x, z_k) ind_(B_(n,k)) (z). $
  Each summand is the product of the $cal(A)$-measurable function $x |-> phi(x, z_k)$ and the Borel
  function $z |-> ind_(B_(n,k)) (z)$, hence $cal(A) times.o borel(Z)$-measurable. For each $(x, z)$ at
  most one summand is non-zero, so $phi_n$ is the pointwise limit of finite partial sums and therefore
  measurable. If $z in B_(n,k)$, then $phi_n (x, z) = phi(x, z_k)$ with $d(z, z_k) < 1\/n$. Hence, by the
  continuity of $phi(x, dot)$, $phi_n (x, z) -> phi(x, z)$ as $n -> oo$ for every $(x, z)$, and $phi$ is
  measurable as a pointwise limit of measurable functions. (For more on Carathéodory functions see
  @aliprantis2006.)
]

#theorem(title: [Tonelli and Fubini])[
  Let $(Omega_1, cal(A)_1)$ be a measurable space and $(Omega_2, cal(A)_2, mu_2)$ a σ-finite measure
  space.
  + If $g: Omega_1 times Omega_2 -> [0, oo]$ is $cal(A)_1 times.o cal(A)_2$-measurable, then
    $g(omega_1, dot)$ is $cal(A)_2$-measurable for every $omega_1$, and
    $ omega_1 |-> integral_(Omega_2) g(omega_1, omega_2) dif mu_2 (omega_2) $
    is $cal(A)_1$-measurable.
  + If, in addition, $mu_1$ is a σ-finite measure on $(Omega_1, cal(A)_1)$ and $g$ is as in (i), then
    $ integral_(Omega_1 times Omega_2) g dif (mu_1 times.o mu_2) = integral_(Omega_1) integral_(Omega_2) g(omega_1, omega_2) dif mu_2 (omega_2) dif mu_1 (omega_1) = integral_(Omega_2) integral_(Omega_1) g(omega_1, omega_2) dif mu_1 (omega_1) dif mu_2 (omega_2). $
  + (Fubini) If $mu_1, mu_2$ are σ-finite and $g in cal(L)^1 (mu_1 times.o mu_2)$ is $KK$-valued, then
    $g(omega_1, dot) in cal(L)^1 (mu_2)$ for $mu_1$-almost every $omega_1$, the (almost everywhere defined)
    function $omega_1 |-> integral g(omega_1, omega_2) dif mu_2 (omega_2)$ is in $cal(L)^1 (mu_1)$, and the
    iterated integrals in both orders equal $integral g dif (mu_1 times.o mu_2)$.
] <thm:app-fubini>

#proof[
  (ii) and (iii) are @rudin1987[Thm. 8.8]. Part (i) needs no measure on $Omega_1$, so we indicate the
  argument. Measurability of the sections $g(omega_1, dot)$ is standard. Assume first that $mu_2$ is
  finite and let $cal(D)$ be the family of sets $Q in cal(A)_1 times.o cal(A)_2$ for which
  $omega_1 |-> mu_2 (Q_(omega_1))$ is measurable, where $Q_(omega_1) := {omega_2 : (omega_1, omega_2) in Q}$.
  For a rectangle, $mu_2 ((A times B)_(omega_1)) = ind_A (omega_1) mu_2 (B)$ is measurable. Moreover
  $cal(D)$ is a Dynkin system: it contains $Omega_1 times Omega_2$, it is closed under complements because
  $mu_2 ((Q^c)_(omega_1)) = mu_2 (Omega_2) - mu_2 (Q_(omega_1))$ (here finiteness is used), and it is closed
  under countable disjoint unions by σ-additivity. Since rectangles form an intersection-stable generator
  of $cal(A)_1 times.o cal(A)_2$, Dynkin's π-λ theorem gives $cal(D) = cal(A)_1 times.o cal(A)_2$. If
  $mu_2$ is σ-finite, write $Omega_2$ as a disjoint union of sets $C_m$ of finite measure and use
  $mu_2 (Q_(omega_1)) = sum_m mu_2 (Q_(omega_1) inter C_m)$. Finally, for general $g >= 0$ approximate $g$
  from below by an increasing sequence of simple functions and use linearity and the monotone convergence
  theorem.
]

In @prop:loss-measurability, (i) is applied with $Omega_1$ a Polish space of functions (which carries no
measure) and $mu_2 = P$.

=== Modes of convergence and the convergence theorems

Let $(Omega, cal(A), mu)$ be a measure space and let $f, f_1, f_2, ...: Omega -> KK$ be measurable. We say
that
- $f_n -> f$ *$mu$-almost everywhere* (a.e.; for probability measures *almost surely*, a.s.) if
  $mu({omega : f_n (omega) arrow.not f(omega)}) = 0$;
- $f_n -> f$ *in measure* (for probability measures *in probability*) if
  $mu({abs(f_n - f) > epsilon}) -> 0$ for every $epsilon > 0$;
- $f_n -> f$ *in $cal(L)^p$*, for $p in (0, oo)$, if $integral abs(f_n - f)^p dif mu -> 0$.

#lemma(title: [Markov and Chebyshev inequalities])[
  Let $(Omega, cal(A), mu)$ be a measure space, $f: Omega -> KK$ measurable, $p in (0, oo)$ and
  $epsilon > 0$. Then
  $ mu({abs(f) >= epsilon}) <= epsilon^(-p) integral abs(f)^p dif mu. $
  In particular, for a real random variable $xi$ with $EE xi^2 < oo$ on a probability space,
  $P(abs(xi - EE xi) >= epsilon) <= epsilon^(-2) op("Var")(xi)$, and for a random variable $xi$ with values
  in a normed space such that $norm(xi)$ is measurable, $P(norm(xi) >= epsilon) <= epsilon^(-2) EE norm(xi)^2$.
] <lem:app-markov>

#proof[
  Integrate the pointwise inequality $epsilon^p ind_({abs(f) >= epsilon}) <= abs(f)^p$. The other two
  statements are the special cases $p = 2$ with $f = xi - EE xi$ and $f = norm(xi)$.
]

The following elementary principle is used repeatedly to upgrade statements about subsequences.

#lemma(title: [Subsequence principle])[
  Let $(a_n)$ be a sequence in a topological space and let $a$ be a point. If every subsequence of $(a_n)$
  has a further subsequence converging to $a$, then $a_n -> a$.
] <lem:app-subsequence>

#proof[
  If $a_n arrow.not a$, there are a neighbourhood $U$ of $a$ and a subsequence $(a_(n_k))$ with
  $a_(n_k) in.not U$ for all $k$. No subsequence of $(a_(n_k))$ converges to $a$, a contradiction.
]

#theorem(title: [Convergence theorems])[
  Let $(Omega, cal(A), mu)$ be a measure space and let $f, f_1, f_2, ...$ be measurable functions on
  $Omega$.
  + (Monotone convergence) If $0 <= f_1 <= f_2 <= ...$ are $[0, oo]$-valued and $f_n -> f$ pointwise, then
    $integral f_n dif mu -> integral f dif mu$.
  + (Fatou's lemma) If the $f_n$ are $[0, oo]$-valued, then
    $ integral liminf_(n -> oo) f_n dif mu <= liminf_(n -> oo) integral f_n dif mu. $
  + (Dominated convergence) If the $f_n$ are $KK$-valued, $f_n -> f$ $mu$-a.e., and there is
    $g in cal(L)^1 (mu)$ with $abs(f_n) <= g$ $mu$-a.e. for all $n$, then $f in cal(L)^1 (mu)$,
    $integral abs(f_n - f) dif mu -> 0$, and in particular $integral f_n dif mu -> integral f dif mu$.
  + If $f_n -> f$ in measure, then a subsequence $(f_(n_k))$ converges to $f$ $mu$-a.e.
  + If $mu(Omega) < oo$ and $f_n -> f$ $mu$-a.e., then $f_n -> f$ in measure. Consequently, if
    $mu(Omega) < oo$, then $f_n -> f$ in measure if and only if every subsequence of $(f_n)$ has a further
    subsequence that converges to $f$ $mu$-a.e.
  + Let $p in (0, oo)$. If $f, f_n in cal(L)^p (mu)$ and $f_n -> f$ in $cal(L)^p$, then $f_n -> f$ in
    measure, and there are a subsequence $(f_(n_k))$ and a function $g in cal(L)^p (mu)$ such that
    $f_(n_k) -> f$ $mu$-a.e. and $abs(f_(n_k)) <= g$ for all $k$.
] <thm:app-convergence>

#proof[
  (i)–(iii) are @rudin1987[Thm. 1.26, Lemma 1.28, Thm. 1.34]. Note that in (ii) nothing but
  non-negativity is assumed; the inequality may be strict, e.g. for $f_n = n ind_((0, 1\/n))$ on $(0, 1)$
  with Lebesgue measure.

  (iv) Choose $n_1 < n_2 < ...$ with $mu(A_k) <= 2^(-k)$, where $A_k := {abs(f_(n_k) - f) > 2^(-k)}$. The set
  $N := inter.big_(m) union.big_(k >= m) A_k$ satisfies $mu(N) <= sum_(k >= m) 2^(-k) = 2^(1 - m)$ for
  every $m$ (Borel–Cantelli), so $mu(N) = 0$. For $omega in.not N$ we have $omega in.not A_k$ for all large
  $k$, i.e. $abs(f_(n_k) (omega) - f(omega)) <= 2^(-k)$ eventually, so $f_(n_k) (omega) -> f(omega)$.

  (v) For $epsilon > 0$ the functions $ind_({abs(f_n - f) > epsilon})$ are bounded by the integrable
  function $ind_Omega$ and converge to $0$ a.e., so $mu({abs(f_n - f) > epsilon}) -> 0$ by (iii). For the
  equivalence: if $f_n -> f$ in measure, then so does every subsequence, and (iv) yields a further
  subsequence converging a.e. Conversely, fix $epsilon > 0$ and put $a_n := mu({abs(f_n - f) > epsilon})$.
  Every subsequence of $(f_n)$ has a further subsequence converging a.e., hence in measure by the first
  part, so every subsequence of $(a_n)$ has a further subsequence converging to $0$. By
  @lem:app-subsequence, $a_n -> 0$.

  (vi) Convergence in measure follows from @lem:app-markov, since
  $ mu({abs(f_n - f) >= epsilon}) <= epsilon^(-p) integral abs(f_n - f)^p dif mu. $
  Choose $n_1 < n_2 < ...$ such that $epsilon_k := integral abs(f_(n_k) - f)^p dif mu <= min{2^(-k), 2^(-k p)}$, and put
  $h := sum_k abs(f_(n_k) - f)$. If $p >= 1$, Minkowski's inequality and monotone convergence give
  $norm(h)_p <= sum_k epsilon_k^(1\/p) <= 1$. If $p < 1$, the inequality $(a + b)^p <= a^p + b^p$ for
  $a, b >= 0$ (see @sec:app-lp) and monotone convergence give $integral h^p dif mu <= sum_k epsilon_k <= 1$.
  In both cases $h in cal(L)^p (mu)$, so $h < oo$ a.e., which forces $abs(f_(n_k) - f) -> 0$ a.e. Finally
  $g := abs(f) + h in cal(L)^p (mu)$ (by the same two inequalities) satisfies
  $abs(f_(n_k)) <= abs(f) + abs(f_(n_k) - f) <= g$.
]

Part (v) is how "convergence in probability" enters the lower semicontinuity of the risk
(@prop:loss-lsc), and part (vi) provides the integrable majorant in the proof of continuity of the risk on
$L^p$ (@prop:loss-risk-continuity).

== $L^p$ spaces <sec:app-lp>

The $L^p$ spaces are the natural domains of risk functionals: for a Nemitski loss of order $p$ the risk is
continuous on $L^p (P_X)$ (@prop:loss-risk-continuity), an RKHS with $abs(K)_p < oo$ embeds into $L^p (mu)$
(@thm:mercer-lp-embedding), and the duality $(L^p)' = L^(p')$ is what produces the function $h$ in the
general representer theorem (@thm:reg-general-representer). The spaces with $0 < p < 1$ appear with the
$L_p$-losses of @ex:loss-catalogue and, for atomless measures, are *not* normable, as we show at the end
of this section.

#definition(title: [$cal(L)^p$ and $L^p$])[
  Let $(Omega, cal(A), mu)$ be a measure space. For $p in (0, oo)$ let $cal(L)^p (mu)$ be the space of
  measurable $f: Omega -> KK$ with
  $ norm(f)_(L^p (mu)) := (integral_Omega abs(f)^p dif mu)^(1\/p) < oo, $
  and let $cal(L)^oo (mu)$ be the space of measurable $f$ with finite essential supremum
  $ norm(f)_(L^oo (mu)) := esssup_(omega in Omega) abs(f(omega)) := inf{c >= 0 : abs(f) <= c " " mu"-a.e."}. $
  The space $L^p (mu)$ is the quotient of $cal(L)^p (mu)$ by the subspace of functions that vanish
  $mu$-a.e.; its elements are equivalence classes $[f]$ of functions that agree $mu$-almost everywhere.
  For $p in [1, oo]$ the number $p' in [1, oo]$ with $1\/p + 1\/p' = 1$ is the *conjugate exponent*.
] <def:app-lp>

When the measure is clear from the context we abbreviate $norm(f)_p := norm(f)_(L^p (mu))$. For $p = oo$
this abbreviation is used only in the present section: elsewhere in the book $norm(f)_oo = sup_x abs(f(x))$
always denotes the supremum norm of a bounded function, and the essential supremum is written
$norm(f)_(L^oo (mu))$.

We usually write $f$ instead of $[f]$. This is harmless as long as only integrals of $f$ are involved, but
it must be done with care in this book, because the elements of an RKHS are genuine functions whose point
values matter. For instance, the inclusion $H_K arrow.hook L^2 (mu)$ maps $f$ to its class $[f]$ and need not
be injective (@thm:mercer-lp-embedding). Note also that for bounded $f$ the essential supremum $norm(f)_(L^oo (mu))$ can be strictly smaller than
the supremum norm $sup_omega abs(f(omega))$; for instance $norm(ind_({0}))_(L^oo (lambda)) = 0$ for Lebesgue
measure $lambda$.

#theorem(title: [Hölder, Minkowski, Riesz–Fischer])[
  Let $(Omega, cal(A), mu)$ be a measure space.
  + (Hölder) Let $p in [1, oo]$. If $f in cal(L)^p (mu)$ and $g in cal(L)^(p') (mu)$, then
    $f g in cal(L)^1 (mu)$ and $norm(f g)_1 <= norm(f)_p norm(g)_(p')$.
  + (Minkowski, Riesz–Fischer) For $p in [1, oo]$, $norm(dot)_p$ is a norm on $L^p (mu)$, and $L^p (mu)$
    is a Banach space. $L^2 (mu)$ is a Hilbert space with the inner product
    $ip(f, g)_(L^2 (mu)) = integral f overline(g) dif mu$.
  + If $mu(Omega) = 1$ and $0 < p <= q <= oo$, then $norm(f)_p <= norm(f)_q$ for all measurable $f$. In
    particular $L^q (mu) subset.eq L^p (mu)$, and the inclusion is continuous with norm $1$.
] <thm:app-holder>

#proof[
  (i) and (ii): @rudin1987[Ch. 3]. (iii) For $q = oo$ this is clear, since $abs(f) <= norm(f)_oo$ a.e. For
  $q < oo$ apply Hölder's inequality with the exponents $r := q\/p >= 1$ and $r'$ to $abs(f)^p$ and $1$:
  $integral abs(f)^p dif mu <= (integral abs(f)^q dif mu)^(p\/q) mu(Omega)^(1\/r') = norm(f)_q^p$.
]

#theorem(title: [Duality of $L^p$ spaces])[
  Let $(Omega, cal(A), mu)$ be a σ-finite measure space and $p in [1, oo)$. Then
  $ J: L^(p') (mu) -> (L^p (mu))', quad (J g)(f) := integral_Omega f g dif mu, $
  is an isometric linear isomorphism. In other words, every bounded linear functional $phi$ on $L^p (mu)$ is
  of the form $phi(f) = integral f g dif mu$ for a unique $g in L^(p') (mu)$, and $norm(phi) = norm(g)_(p')$.
] <thm:app-lp-duality>

#proof[
  @rudin1987[Thm. 6.16]. (For $1 < p < oo$ the σ-finiteness assumption can be dropped, but all measures
  in this book are σ-finite.)
]

#remark[
  + The pairing $(f, g) |-> integral f g dif mu$ is *bilinear*, whereas the inner product of $L^2 (mu)$ is
    sesquilinear. For $p = 2$ the two identifications of $(L^2 (mu))'$ with $L^2 (mu)$ (by $J$ and by the
    Riesz map of @thm:app-riesz) differ by complex conjugation: $J g = ip(dot, overline(g))_(L^2 (mu))$.
  + For $p = oo$ the map $J: L^1 (mu) -> (L^oo (mu))'$ ($mu$ σ-finite) is still isometric, but in general not surjective
    (e.g. for Lebesgue measure on $[0, 1]$); see @brezis2011[Sect. 4.3]. This is why the general representer
    theorem (@thm:reg-general-representer) is formulated for $p < oo$.
  + For $1 < p < oo$, applying the theorem to $p$ and to $p'$ shows that $L^p (mu)$ is reflexive
    (@def:app-reflexive).
]

For $0 < p < 1$ the function $norm(dot)_p$ is not a norm: the triangle inequality fails. What survives is
the inequality $abs(a + b)^p <= abs(a)^p + abs(b)^p$ for $a, b in KK$ (subadditivity of the concave function
$t |-> t^p$ on $[0, oo)$), which makes
$ d_p (f, g) := integral abs(f - g)^p dif mu $
a metric on $L^p (mu)$. With this metric $L^p (mu)$ is complete (the proof is the same as for $p >= 1$) and
addition and scalar multiplication are continuous. But the resulting topology cannot come from a norm, as
the following proposition shows (compare the figure in @ex:loss-catalogue). In the language of
topological vector spaces: $L^p (mu)$ is not *locally convex*.

The proposition needs a mild assumption on $mu$, since, for instance, $L^p$ of a counting measure on a finite
set is finite-dimensional and hence normable. A set $A in cal(A)$ is an *atom* of $mu$ if $mu(A) > 0$ and
every measurable $B subset.eq A$ satisfies $mu(B) = 0$ or $mu(A without B) = 0$; $mu$ is *atomless* if it
has no atoms. Lebesgue measure on an interval is atomless. For a finite Borel measure $mu$ on a separable
metric space, $mu$ is atomless if and only if $mu({z}) = 0$ for every point $z$. (Let $A$ be an atom. For
each $n$, countably many closed balls of radius $1\/n$ cover the space, and since $A$ is an atom, one of them,
$B_n$, satisfies $mu(A without B_n) = 0$. Then $A inter inter.big_n B_n$ has measure $mu(A) > 0$ and
diameter $0$, so it is a point of positive mass.)

#lemma(title: [Partitions into small pieces])[
  Let $nu$ be a finite atomless measure on $(Omega, cal(A))$ and $delta > 0$. Then there is a finite
  partition $Omega = A_1 union ... union A_m$ into measurable sets with $nu(A_i) <= delta$ for all $i$.
] <lem:app-atomless-partition>

#proof[
  _Step 1: every $A$ with $nu(A) > 0$ contains a measurable $B$ with $0 < nu(B) <= delta$._ Since $A$ is not
  an atom, $A = B_1 union C_1$ with disjoint $B_1, C_1$ of positive measure; one of them has measure at most
  $nu(A)\/2$. Repeating the argument with this set, after $k$ steps we get a subset of $A$ with measure in
  $(0, 2^(-k) nu(A)]$.

  _Step 2: exhaustion._ Choose disjoint measurable sets $C_1, C_2, ...$ recursively: with
  $R_k := Omega without (C_1 union ... union C_(k-1))$ let
  $s_k := sup{nu(C) : C subset.eq R_k "measurable", nu(C) <= delta}$ and choose $C_k subset.eq R_k$ with
  $nu(C_k) <= delta$ and $nu(C_k) >= s_k \/ 2$. Since $sum_k nu(C_k) <= nu(Omega) < oo$, we have $s_k -> 0$.
  If $R := Omega without union.big_k C_k$ had positive measure, Step 1 would give $B subset.eq R$ with
  $0 < nu(B) <= delta$, and since $B subset.eq R_k$ for all $k$, $s_k >= nu(B)$ for all $k$, a contradiction.
  So $nu(R) = 0$. Choose $M$ with $sum_(k > M) nu(C_k) <= delta$; then $C_1, ..., C_M$ and
  $R union union.big_(k > M) C_k$ form the desired partition.
]

#proposition(title: [$L^p$ is not normable for $0 < p < 1$])[
  Let $0 < p < 1$ and let $mu$ be a non-zero, σ-finite, atomless measure on $(Omega, cal(A))$, for instance
  Lebesgue measure on $[0, 1]$, or a distribution $P_X$ on a separable metric space $X$ with
  $P_X ({x}) = 0$ for all $x$. Equip $L^p (mu)$ with the metric $d_p$. Then:
  + the only convex open subset of $L^p (mu)$ containing $0$ is $L^p (mu)$ itself;
  + there is no norm on $L^p (mu)$ that induces the topology of $d_p$;
  + the only continuous linear functional on $L^p (mu)$ is $0$.
] <prop:app-lp-small-p>

#proof[
  (i) Let $U$ be convex and open with $0 in U$; then $U$ contains a ball ${h : d_p (h, 0) < r}$ for some
  $r > 0$. Let $f in L^p (mu)$ and $c := integral abs(f)^p dif mu$; if $c = 0$ then $f = 0 in U$. Otherwise
  consider the finite measure $nu(A) := integral_A abs(f)^p dif mu$. It is atomless: if $nu(A) > 0$, then
  $A' := A inter {f != 0}$ has $mu(A') > 0$, and since $A'$ is not a $mu$-atom there is $B subset.eq A'$ with
  $mu(B) > 0$ and $mu(A' without B) > 0$; as $abs(f)^p > 0$ on $A'$, both $nu(B)$ and
  $nu(A without B) >= nu(A' without B)$ are positive. Let $delta > 0$, to be fixed below, and let
  $A_1, ..., A_m$ be a partition as in @lem:app-atomless-partition with $nu(A_i) <= delta$. Discard the
  $A_i$ with $nu(A_i) = 0$ (on them $f = 0$ a.e.) and put $t_i := nu(A_i) \/ c$ and
  $g_i := t_i^(-1) f ind_(A_i)$. Then $t_i > 0$, $sum_i t_i = 1$, $f = sum_i t_i g_i$ almost everywhere, and
  $ d_p (g_i, 0) = t_i^(-p) nu(A_i) = c t_i^(1 - p) <= c^p delta^(1 - p). $
  Since $p < 1$, we can choose $delta$ so small that $c^p delta^(1 - p) < r$. Then all $g_i$ lie in $U$, and
  so does their convex combination $f$. Hence $U = L^p (mu)$.

  (ii) Since $mu$ is σ-finite and non-zero, there is a set $A$ with $0 < mu(A) < oo$, so $f := ind_A$ is a
  non-zero element of $L^p (mu)$. If a norm induced the topology, its open unit ball would be a convex open
  set containing $0$ that is not the whole space (it does not contain $2 f \/ norm(f)$), contradicting (i).

  (iii) If $phi$ is linear and continuous, the set ${f : abs(phi(f)) < 1}$ is convex, open and contains $0$,
  so by (i) it is all of $L^p (mu)$. Thus $abs(phi(t f)) < 1$ for all $t > 0$ and all $f$, so $phi = 0$.
]

== The Bochner integral <sec:app-bochner>

Several objects in this book are integrals of functions with values in a Hilbert space: the adjoint of the
embedding $H_K arrow.hook L^2 (mu)$ is $g |-> integral g(y) K(dot, y) dif mu(y)$ (@thm:mercer-lp-embedding);
the general representer theorem writes the regularized minimizer as
$f_(P, lambda) = -1/(2 lambda) integral h(x, y) Phi(x) dif P(x, y)$ (@thm:reg-general-representer); and the
stability estimate of @thm:stab-measure and the outlook in @sec:stab-outlook work with expectations of
$H$-valued random variables. The appropriate integral is the Bochner integral, which extends the Lebesgue
integral to Banach-space-valued functions in the most direct way. Its central practical property is that
it commutes with bounded linear operators, in particular with inner products and, in an RKHS, with point
evaluations.

Throughout this section $(Omega, cal(A), mu)$ is a measure space and $E$, $F$ are Banach spaces.

#definition(title: [Bochner integral])[
  + A *simple function* is a function $s: Omega -> E$ of the form $s = sum_(i=1)^n ind_(A_i) x_i$ with
    $A_i in cal(A)$ and $x_i in E$. It is *$mu$-simple* if moreover $mu(A_i) < oo$ for all $i$; then its
    integral is $integral s dif mu := sum_(i=1)^n mu(A_i) x_i$ (which does not depend on the representation).
  + A function $f: Omega -> E$ is *strongly measurable* if there are simple functions $s_n$ with
    $s_n (omega) -> f(omega)$ in $E$ for every $omega in Omega$. It is *weakly measurable* if
    $phi compose f$ is measurable for every $phi in E'$. For a strongly measurable $f$, the function
    $omega |-> norm(f(omega))$ is measurable (as the limit of $norm(s_n)$). If $E$ is separable, strong,
    weak and Borel measurability coincide (Pettis' theorem, @thm:app-bochner-properties (ii)).
  + A strongly measurable $f$ is *Bochner integrable* if there are $mu$-simple functions $s_n$ with
    $integral norm(f - s_n) dif mu -> 0$. Then
    $ integral_Omega f dif mu := lim_(n -> oo) integral_Omega s_n dif mu, $
    and this limit exists in $E$ and does not depend on the choice of $(s_n)$, since
    $norm(integral s_n dif mu - integral s_m dif mu) <= integral norm(s_n - s_m) dif mu$. For $A in cal(A)$ we
    put $integral_A f dif mu := integral ind_A f dif mu$, and for a probability measure we write
    $EE f := integral f dif mu$. By @thm:app-bochner-properties, $f$ is Bochner integrable if and only if
    $integral norm(f) dif mu < oo$ (i), and the integral commutes with bounded linear operators, in
    particular with bounded linear functionals (iv).
] <def:app-bochner>

#theorem(title: [Properties of the Bochner integral])[
  Let $(Omega, cal(A), mu)$ be a measure space and $E, F$ Banach spaces.
  + (Bochner's criterion) A strongly measurable $f: Omega -> E$ is Bochner integrable if and only if
    $integral norm(f) dif mu < oo$. The integral is linear in $f$, and
    $norm(integral f dif mu) <= integral norm(f) dif mu$.
  + (Pettis, separable case) If $E$ is separable, then for $f: Omega -> E$ the following are equivalent:
    $f$ is strongly measurable; $f$ is Borel measurable ($f^(-1)(B) in cal(A)$ for all $B in borel(E)$);
    $f$ is weakly measurable. If $E$ is a Hilbert space, weak measurability means that
    $omega |-> ip(f(omega), z)$ is measurable for every $z in E$.
  + If $f: Omega -> E$ is strongly measurable and $g: Omega -> KK$ is measurable, then $g f$ is strongly
    measurable.
  + (Commuting with operators) If $f$ is Bochner integrable and $T in cal(L)(E, F)$, then $T compose f$ is
    Bochner integrable and
    $ T (integral_Omega f dif mu) = integral_Omega T f dif mu. $
    In particular $phi(integral f dif mu) = integral phi(f) dif mu$ for all $phi in E'$; if $E$ is a Hilbert
    space, then $ip(integral f dif mu, z) = integral ip(f, z) dif mu$ for all $z in E$; and if $E = H$ is an
    RKHS of functions on a set $X$, then, applying this to the point evaluations,
    $ (integral_Omega f dif mu)(x) = integral_Omega f(omega)(x) dif mu(omega) quad "for all" x in X. $
  + (Dominated convergence) Let $f, f_n: Omega -> E$ be strongly measurable with $f_n -> f$ pointwise
    $mu$-a.e., and assume $norm(f_n) <= g$ a.e. for all $n$, for some $g in cal(L)^1 (mu)$. Then $f$ and all
    $f_n$ are Bochner integrable, $integral norm(f_n - f) dif mu -> 0$, and
    $integral f_n dif mu -> integral f dif mu$.
] <thm:app-bochner-properties>

#proof[
  (i) If $f$ is Bochner integrable with approximating $mu$-simple $s_n$, then
  $integral norm(f) <= integral norm(f - s_n) + integral norm(s_n) < oo$. Conversely, let $s_n -> f$ pointwise
  with simple $s_n$ and put $tilde(s)_n := s_n ind_({norm(s_n) <= 2 norm(f)})$. Then $tilde(s)_n$ is simple,
  $tilde(s)_n -> f$ pointwise (if $f(omega) != 0$, then eventually $norm(s_n (omega)) <= 2 norm(f(omega))$;
  if $f(omega) = 0$, then $tilde(s)_n (omega) = 0$ for all $n$), and
  $norm(tilde(s)_n - f) <= 3 norm(f)$. Each non-zero value $x$ of $tilde(s)_n$ is taken on a set where
  $norm(f) >= norm(x)\/2 > 0$, which has finite measure since $integral norm(f) < oo$; so $tilde(s)_n$ is
  $mu$-simple. By dominated convergence (@thm:app-convergence (iii)),
  $integral norm(tilde(s)_n - f) dif mu -> 0$. Linearity and the norm inequality hold for $mu$-simple functions
  and pass to the limit.

  (ii) We use a countable norming family: if ${x_1, x_2, ...}$ is dense in $E$, choose by the Hahn–Banach
  theorem (@thm:app-hahn-banach (ii)) $phi_k in E'$ with $norm(phi_k) <= 1$ and $phi_k (x_k) = norm(x_k)$.
  Then $norm(x) = sup_k abs(phi_k (x))$ for all $x in E$: $norm(x) >= sup_k abs(phi_k (x))$ is clear, and
  $abs(phi_k (x)) >= norm(x_k) - norm(x - x_k) >= norm(x) - 2 norm(x - x_k)$, where $norm(x - x_k)$ can be made
  arbitrarily small. Now let $f$ be weakly measurable. For every $z in E$,
  $omega |-> norm(f(omega) - z) = sup_k abs(phi_k (f(omega)) - phi_k (z))$ is measurable, so preimages of
  open balls are measurable. Since every open subset of the separable space $E$ is a countable union of open
  balls, $f$ is Borel measurable. If $f$ is Borel measurable, define $s_n (omega) := x_(k)$ where $k <= n$
  is the smallest index minimizing $norm(f(omega) - x_k)$ over $k <= n$; $s_n$ is simple with measurable
  level sets, and $s_n (omega) -> f(omega)$ by density. Finally, a strongly measurable $f$ is weakly
  measurable, since $phi compose f = lim phi compose s_n$. The statement for Hilbert spaces follows from
  the Riesz representation theorem (@thm:app-riesz).

  (iii) If $s_n -> f$ and $g_n -> g$ pointwise with simple $s_n$ and simple scalar functions $g_n$, then
  $g_n s_n$ is simple and converges pointwise to $g f$.

  (iv) For $mu$-simple $s$ the identity $T integral s = integral T s$ is linearity of $T$. If $s_n$
  approximates $f$, then $T s_n$ is $mu$-simple and
  $integral norm(T f - T s_n) <= norm(T) integral norm(f - s_n) -> 0$, so $T f$ is Bochner integrable and
  $integral T f = lim integral T s_n = lim T integral s_n = T integral f$. The special cases use
  $T = phi$, $T = ip(dot, z)$ and $T = $ evaluation at $x$, which is continuous on an RKHS (@def:rkhs).

  (v) $norm(f) <= g$ a.e., so $f$ and $f_n$ are Bochner integrable by (i). The functions
  $norm(f_n - f)$ are measurable, bounded by $2 g$ and tend to $0$ a.e., so
  $integral norm(f_n - f) -> 0$ by @thm:app-convergence (iii), and
  $norm(integral f_n - integral f) <= integral norm(f_n - f)$.
]

For more on vector-valued integration see @diestel1977[Ch. II], @hytonen2016[Ch. 1] and
@steinwart2008[App. A]. We record two consequences.

#proposition(title: [Integrals of the canonical feature map])[
  Let $H$ be a separable RKHS on a measurable space $(X, cal(A))$ with kernel $K$ such that every $f in H$
  is measurable, let $Phi(x) = K(dot, x)$ be the canonical feature map, let $mu$ be a measure on $X$ and let
  $g: X -> KK$ be measurable with $integral abs(g(x)) sqrt(K(x, x)) dif mu(x) < oo$. Then $g Phi$ is
  Bochner integrable, and for all $f in H$ and $x' in X$,
  $ ip(f, integral g Phi dif mu)_H = integral overline(g(x)) f(x) dif mu(x), quad (integral g Phi dif mu)(x') = integral g(x) K(x', x) dif mu(x). $
] <prop:app-bochner-feature-map>

#proof[
  For $f in H$, $x |-> ip(Phi(x), f)_H = overline(f(x))$ is measurable, so $Phi$ is weakly and hence, by
  @thm:app-bochner-properties (ii), strongly measurable; by (iii) so is $g Phi$. Since
  $norm(Phi(x))_H = sqrt(K(x, x))$, (i) shows that $g Phi$ is Bochner integrable. By (iv), applied to the functional
  $ip(dot, f)$ and followed by complex conjugation,
  $ip(f, integral g Phi dif mu) = integral ip(f, g(x) Phi(x)) dif mu(x) = integral overline(g(x)) f(x) dif mu(x)$,
  using the reproducing property $ip(f, K(dot, x)) = f(x)$. The second formula is (iv) for point
  evaluations, since $Phi(x)(x') = K(x', x)$.
]

#proposition(title: [Independent Hilbert-space-valued random variables])[
  Let $H$ be a separable Hilbert space and let $xi, eta: Omega -> H$ be independent Bochner integrable random
  variables on a probability space $(Omega, cal(A), P)$. Then $ip(xi, eta)_H$ is integrable and
  $ EE ip(xi, eta)_H = ip(EE xi, EE eta)_H. $
] <prop:app-bochner-independent>

#proof[
  By @thm:app-bochner-properties (ii), $xi$ and $eta$ are Borel measurable, and by @prop:app-polish (iv)
  the joint distribution of $(xi, eta)$ is a measure on $borel(H) times.o borel(H) = borel(H times H)$; by
  independence it is the product $P_xi times.o P_eta$ of the distributions. By Tonelli,
  $EE abs(ip(xi, eta)) <= EE (norm(xi) norm(eta)) = EE norm(xi) dot EE norm(eta) < oo$. By Fubini
  (@thm:app-fubini (iii)),
  $ EE ip(xi, eta) = integral_H integral_H ip(a, b) dif P_xi (a) dif P_eta (b). $
  For fixed $b in H$, the transformation formula and @thm:app-bochner-properties (iv) show that the inner
  integral equals $EE ip(xi, b) = ip(EE xi, b)$. In the same way,
  $ integral_H ip(EE xi, b) dif P_eta (b) = EE ip(EE xi, eta) = overline(EE ip(eta, EE xi)) = overline(ip(EE eta, EE xi)) = ip(EE xi, EE eta). $
]

== Hilbert and Banach spaces <sec:app-hilbert>

Reproducing kernel Hilbert spaces are, first of all, Hilbert spaces, and most arguments in @sec:rkhs and
@sec:reg are Hilbert-space geometry: orthogonal projections (@prop:rkhs-sum-restriction,
@thm:reg-representer), the Riesz representation theorem (which *defines* the reproducing kernel,
@def:rkhs-kernel), polarization (@thm:rkhs-completion), adjoints (@thm:mercer-lp-embedding) and weak
compactness (@thm:stab-lambda). Banach spaces enter through $L^p$ and $ell^oo$, through dual spaces, and
through the subdifferential calculus of @sec:reg.

=== Hilbert space geometry

#lemma(title: [Cauchy–Schwarz for positive semidefinite forms])[
  Let $V$ be a vector space and $s: V times V -> KK$ linear in the first and conjugate-linear in the second
  argument, with $s(y, x) = overline(s(x, y))$ and $s(x, x) >= 0$ for all $x, y in V$. Then
  $ abs(s(x, y))^2 <= s(x, x) s(y, y) quad "for all" x, y in V. $
  Consequently $N := {x in V : s(x, x) = 0} = {x in V : s(x, y) = 0 "for all" y in V}$ is a linear subspace.
] <lem:app-cauchy-schwarz>

#proof[
  Let $x, y in V$ with $s(x, y) != 0$ (otherwise there is nothing to prove) and put
  $alpha := s(x, y) \/ abs(s(x, y))$. For $t in RR$,
  $ 0 <= s(x - t alpha y, x - t alpha y) = s(x, x) - 2 t abs(s(x, y)) + t^2 s(y, y), $
  because $s(x, t alpha y) + s(t alpha y, x) = 2 t Re(overline(alpha) s(x, y)) = 2 t abs(s(x, y))$. If
  $s(y, y) = 0$, letting $t -> oo$ gives a contradiction to $s(x, y) != 0$; so $s(y, y) > 0$, and the
  quadratic polynomial in $t$ has at most one real zero, i.e. its discriminant is non-positive:
  $4 abs(s(x, y))^2 <= 4 s(x, x) s(y, y)$. The description of $N$ follows: if $s(x, x) = 0$, then
  $s(x, y) = 0$ for all $y$, and conversely; the second set is clearly a subspace.
]

This is used in the construction of the RKHS of a positive definite kernel (@thm:rkhs-moore-aronszajn),
where the form is a priori only positive semidefinite.

#theorem(title: [Projection theorem and polarization])[
  Let $H$ be a Hilbert space.
  + (Parallelogram law and polarization) For all $x, y in H$,
    $ norm(x + y)^2 + norm(x - y)^2 = 2 norm(x)^2 + 2 norm(y)^2, $
    and
    $ ip(x, y) = 1/4 (norm(x + y)^2 - norm(x - y)^2) quad (KK = RR), quad ip(x, y) = 1/4 sum_(k=0)^3 i^k norm(x + i^k y)^2 quad (KK = CC). $
  + (Projection onto convex sets) Let $C subset.eq H$ be non-empty, closed and convex. For every $x in H$
    there is a unique $P_C x in C$ with $norm(x - P_C x) = inf_(c in C) norm(x - c)$. It is characterized by
    $ P_C x in C quad "and" quad Re ip(x - P_C x, c - P_C x) <= 0 quad "for all" c in C. $
    In particular, $C$ has a unique element of minimal norm, namely $P_C 0$.
  + (Orthogonal projection) Let $M subset.eq H$ be a closed subspace. Then $P_M x$ is characterized by
    $P_M x in M$ and $x - P_M x in M^perp := {y in H : ip(m, y) = 0 "for all" m in M}$. The map $P_M$ is
    linear, $norm(P_M x)^2 + norm(x - P_M x)^2 = norm(x)^2$ (so $norm(P_M) <= 1$), $H = M plus.o M^perp$, and
    $(M^perp)^perp = M$.
  + For every subset $S subset.eq H$, $(S^perp)^perp = overline(spn S)$. In particular, a subspace
    $M subset.eq H$ is dense if and only if $M^perp = {0}$.
] <thm:app-projection>

#proof[
  (i) Expand $norm(x plus.minus y)^2 = norm(x)^2 plus.minus 2 Re ip(x, y) + norm(y)^2$; adding gives the
  parallelogram law and subtracting gives the real polarization identity. In the complex case,
  $norm(x + i^k y)^2 = norm(x)^2 + norm(y)^2 + i^(-k) ip(x, y) + i^k overline(ip(x, y))$ since
  $ip(x, i^k y) = i^(-k) ip(x, y)$. Multiplying by $i^k$ and summing over $k = 0, ..., 3$, the terms
  $i^k (norm(x)^2 + norm(y)^2)$ and $i^(2k) overline(ip(x, y))$ sum to zero, while $ip(x, y)$ appears four
  times.

  (ii) Let $delta := inf_(c in C) norm(x - c)$ and $c_n in C$ with $norm(x - c_n) -> delta$. By the
  parallelogram law applied to $x - c_n$ and $x - c_m$, and since $(c_n + c_m)\/2 in C$,
  $ norm(c_n - c_m)^2 = 2 norm(x - c_n)^2 + 2 norm(x - c_m)^2 - 4 norm(x - (c_n + c_m)/2)^2 <= 2 norm(x - c_n)^2 + 2 norm(x - c_m)^2 - 4 delta^2 -> 0. $
  So $(c_n)$ is a Cauchy sequence; its limit $p$ lies in $C$ (closedness) and $norm(x - p) = delta$. The same
  inequality applied to two minimizers shows uniqueness. If $p = P_C x$, $c in C$ and $t in (0, 1]$, then
  $p + t (c - p) in C$ and
  $ 0 <= norm(x - p - t(c - p))^2 - norm(x - p)^2 = -2 t Re ip(x - p, c - p) + t^2 norm(c - p)^2; $
  dividing by $t$ and letting $t -> 0$ gives the inequality. Conversely, if $p in C$ satisfies the
  inequality, then $norm(x - c)^2 = norm(x - p)^2 - 2 Re ip(x - p, c - p) + norm(c - p)^2 >= norm(x - p)^2$
  for all $c in C$.

  (iii) For a subspace $M$, $c - P_M x$ ranges over all of $M$ as $c$ ranges over $M$; replacing $m$ by
  $-m$ and (if $KK = CC$) by $i m$ turns the inequality of (ii) into $ip(x - P_M x, m) = 0$ for all
  $m in M$. The characterization shows linearity of $P_M$, and Pythagoras gives the norm identity. Every
  $x$ is $P_M x + (x - P_M x) in M + M^perp$, and $M inter M^perp = {0}$. Clearly $M subset.eq (M^perp)^perp$;
  if $x in (M^perp)^perp$, then $x - P_M x in M^perp inter (M^perp)^perp = {0}$, so $x in M$.

  (iv) $S^perp = (overline(spn S))^perp$ by linearity and continuity of the inner product, so (iii) gives
  $(S^perp)^perp = overline(spn S)$.
]

#theorem(title: [Riesz representation theorem])[
  Let $H$ be a Hilbert space. For every $phi in H'$ there is a unique $y_phi in H$ with
  $ phi(x) = ip(x, y_phi)_H quad "for all" x in H, $
  and $norm(y_phi)_H = norm(phi)_(H')$. The *Riesz map* $R: H' -> H$, $phi |-> y_phi$, is bijective,
  isometric and conjugate-linear, i.e. $R(alpha phi + beta psi) = overline(alpha) R phi + overline(beta) R psi$;
  its inverse is $y |-> ip(dot, y)_H$. (For $KK = RR$, $R$ is a linear isometric isomorphism.) Consequently
  $H'$ is a Hilbert space with the inner product $ip(phi, psi)_(H') := ip(R psi, R phi)_H$, and $H$ is
  reflexive.
] <thm:app-riesz>

#proof[
  If $phi = 0$ take $y_phi = 0$. Otherwise $N := Ker phi$ is a closed proper subspace, so $N^perp != {0}$
  by @thm:app-projection (iii); pick $w in N^perp$, $w != 0$. Then $phi(w) != 0$, and $z := w \/ phi(w)$
  satisfies $phi(z) = 1$. For $x in H$ we have $x - phi(x) z in N$, hence $ip(x - phi(x) z, z) = 0$, i.e.
  $phi(x) = ip(x, z) \/ norm(z)^2$; so $y_phi := z \/ norm(z)^2$ works. If $y, y'$ both represent $phi$, then
  $ip(x, y - y') = 0$ for all $x$, in particular for $x = y - y'$. By Cauchy–Schwarz
  $abs(phi(x)) <= norm(x) norm(y_phi)$, and $phi(y_phi) = norm(y_phi)^2$, so $norm(phi) = norm(y_phi)$.
  Conjugate linearity follows from $alpha phi(x) = ip(x, overline(alpha) y_phi)$, and surjectivity from the
  fact that $ip(dot, y) in H'$ for every $y$. The inner product on $H'$ is linear in $phi$ because both $R$
  and the second argument of $ip(dot, dot)_H$ are conjugate-linear. For reflexivity let $Lambda in H''$;
  by the theorem applied to the Hilbert space $H'$ there is $phi_0 in H'$ with
  $Lambda(psi) = ip(psi, phi_0)_(H') = ip(R phi_0, R psi)_H = psi(R phi_0)$ for all $psi in H'$, so
  $Lambda$ is evaluation at $R phi_0$.
]

#theorem(title: [Orthonormal bases])[
  Let $H$ be a Hilbert space and $(e_i)_(i in I)$ an orthonormal system (ONS) in $H$.
  + (Bessel) $sum_(i in I) abs(ip(x, e_i))^2 <= norm(x)^2$ for every $x in H$.
  + For every $(a_i) in ell^2 (I)$ the series $sum_i a_i e_i$ converges unconditionally in $H$, and
    $norm(sum_i a_i e_i)^2 = sum_i abs(a_i)^2$.
  + The following are equivalent: $(e_i)$ is an orthonormal basis (ONB), i.e. $overline(spn){e_i : i in I} = H$;
    $x = sum_i ip(x, e_i) e_i$ for every $x$; $norm(x)^2 = sum_i abs(ip(x, e_i))^2$ for every $x$
    (Parseval); $ip(x, e_i) = 0$ for all $i$ implies $x = 0$.
  + Every Hilbert space has an ONB, and every ONS can be extended to an ONB. $H$ is separable if and only if
    it has an ONB that is finite or countable.
] <thm:app-onb>

#proof[
  See @rudin1987[Ch. 4].
]

=== Dual spaces and the fundamental theorems for Banach spaces

#theorem(title: [Hahn–Banach])[
  Let $E$ be a normed space.
  + Every bounded linear functional $phi_0$ on a subspace $M subset.eq E$ has an extension $phi in E'$ with
    $norm(phi) = norm(phi_0)$.
  + For every $x in E$ there is $phi in E'$ with $norm(phi) <= 1$ and $phi(x) = norm(x)$. In particular
    $E'$ separates the points of $E$, and $norm(x) = max_(phi in B_(E')) abs(phi(x))$.
  + If $M subset.eq E$ is a subspace and $x in.not overline(M)$, there is $phi in E'$ with $phi|_M = 0$ and
    $phi(x) != 0$. Hence $M$ is dense if and only if the only $phi in E'$ vanishing on $M$ is $phi = 0$.
  + (Separation) If $C subset.eq E$ is non-empty, closed and convex and $x in.not C$, there are $phi in E'$
    and $gamma in RR$ with $Re phi(c) <= gamma < Re phi(x)$ for all $c in C$.
] <thm:app-hahn-banach>

#proof[
  See @brezis2011[Ch. 1] (real scalars) and @rudin1987[Ch. 5] (complex scalars); the complex case of (iv)
  follows from the real one applied to $Re phi$, since $phi(x) = Re phi(x) - i Re phi(i x)$.
]

#theorem(title: [Uniform boundedness principle])[
  Let $E$ be a Banach space, $F$ a normed space and $(T_i)_(i in I)$ a family in $cal(L)(E, F)$ such that
  $sup_(i in I) norm(T_i x) < oo$ for every $x in E$. Then $sup_(i in I) norm(T_i) < oo$.
] <thm:app-uniform-boundedness>

#proof[
  @brezis2011[Thm. 2.2], @rudin1987[Thm. 5.8].
]

Two consequences are used in the book. First, if $H$ is a Hilbert space of functions on $X$ such that
$sup_(x in X) abs(f(x)) < oo$ for every $f in H$, and point evaluations are continuous, then the family
of point evaluations is bounded in $H'$; for an RKHS this means $sup_x sqrt(K(x, x)) < oo$
(@prop:rkhs-bounded). Second, weakly convergent sequences are bounded (@prop:app-weak-basic).

#definition(title: [Reflexive space])[
  Let $E$ be a normed space. The *canonical embedding* $J_E: E -> E''$, $(J_E x)(phi) := phi(x)$, is linear
  and, by @thm:app-hahn-banach (ii), isometric. $E$ is *reflexive* if $J_E$ is surjective.
] <def:app-reflexive>

Hilbert spaces are reflexive (@thm:app-riesz), and so are the spaces $L^p (mu)$ for $1 < p < oo$ (apply
@thm:app-lp-duality to $p$ and $p'$) and all finite-dimensional spaces. The spaces $L^1 [0, 1]$ and
$L^oo [0, 1]$ are not reflexive @brezis2011[Sect. 4.3], and neither is the space $c_0$ of null sequences
with the supremum norm, whose dual is $ell^1$ and whose bidual is $ell^oo$.

=== Adjoint operators

We use two different notions of adjoint, and the notation distinguishes them.

#definition(title: [Banach-space adjoint and Hilbert-space adjoint])[
  + Let $E, F$ be normed spaces and $A in cal(L)(E, F)$. The *(Banach-space) adjoint* $A' in cal(L)(F', E')$
    is $(A' psi)(x) := psi(A x)$ for $psi in F'$ and $x in E$. It satisfies $norm(A') = norm(A)$ and
    $(A B)' = B' A'$.
  + Let $E, F$ be Hilbert spaces and $A in cal(L)(E, F)$. The *(Hilbert-space) adjoint* $A^* in cal(L)(F, E)$
    is the unique operator with
    $ ip(A x, y)_F = ip(x, A^* y)_E quad "for all" x in E, y in F. $
    It exists by @thm:app-riesz and satisfies $norm(A^*) = norm(A)$, $A^(**) = A$, $(A B)^* = B^* A^*$ and
    $norm(A^* A) = norm(A)^2$. In terms of the Riesz maps $R_E: E' -> E$ and $R_F: F' -> F$,
    $A^* = R_E A' R_F^(-1)$.
  + The *annihilators* of subsets $M subset.eq E$ and $N subset.eq E'$ are
    $M^perp := {phi in E' : phi(x) = 0 "for all" x in M}$ and
    $attach(N, tl: perp) := {x in E : phi(x) = 0 "for all" phi in N}$. In a Hilbert space, $M^perp$ denotes
    instead the orthogonal complement ${y : ip(x, y) = 0 "for all" x in M}$; the two notions correspond to
    each other under the Riesz map.
] <def:app-adjoint>

The identity $A^* = R_E A' R_F^(-1)$ is verified by evaluating: for $y in F$, $A'(R_F^(-1) y) = ip(A dot, y)_F$,
and $R_E$ maps this functional to the vector $z$ with $ip(x, z)_E = ip(A x, y)_F$ for all $x$, i.e. to
$A^* y$. Note that $A'$ is linear while the Riesz maps are conjugate-linear.

#proposition(title: [Kernels and ranges of adjoints])[
  Let $E, F$ be normed spaces and $A in cal(L)(E, F)$.
  + $Ker A' = (Ran A)^perp$ and $Ker A = attach((Ran A'), tl: perp)$.
  + $overline(Ran A) = attach((Ker A'), tl: perp)$. In particular, $A$ has dense range if and only if $A'$ is
    injective.
  + $overline(Ran A') subset.eq (Ker A)^perp$, with equality if $E$ is reflexive. In particular, if $E$ is
    reflexive, then $A$ is injective if and only if $A'$ has dense range.
  + If $E$ and $F$ are Hilbert spaces, then
    $ Ker A^* = (Ran A)^perp, quad Ker A = (Ran A^*)^perp, quad overline(Ran A) = (Ker A^*)^perp, quad overline(Ran A^*) = (Ker A)^perp. $
    In particular, $A$ has dense range if and only if $A^*$ is injective, and $A$ is injective if and only if
    $A^*$ has dense range.
] <prop:app-adjoint-kernel-range>

#proof[
  (i) $A' psi = 0$ if and only if $psi(A x) = 0$ for all $x$, i.e. $psi in (Ran A)^perp$. Next,
  $x in attach((Ran A'), tl: perp)$ if and only if $psi(A x) = (A' psi)(x) = 0$ for all $psi in F'$, which by
  @thm:app-hahn-banach (ii) is equivalent to $A x = 0$.

  (ii) If $psi in Ker A'$, then $psi$ vanishes on $Ran A$ and by continuity on $overline(Ran A)$; so
  $overline(Ran A) subset.eq attach((Ker A'), tl: perp)$. Conversely, if $y in.not overline(Ran A)$,
  @thm:app-hahn-banach (iii) yields $psi in F'$ vanishing on $Ran A$ with $psi(y) != 0$; then $psi in Ker A'$ by
  (i), so $y in.not attach((Ker A'), tl: perp)$.

  (iii) If $phi = A' psi$ and $x in Ker A$, then $phi(x) = psi(A x) = 0$; since $(Ker A)^perp$ is closed, the
  inclusion follows. Let $E$ be reflexive and suppose there is
  $phi in (Ker A)^perp without overline(Ran A')$. By @thm:app-hahn-banach (iii), applied in $E'$, there is
  $Lambda in E''$ vanishing on $overline(Ran A')$ with $Lambda(phi) != 0$. By reflexivity
  $Lambda = J_E x$ for some $x in E$, so $psi(A x) = (A' psi)(x) = Lambda(A' psi) = 0$ for all $psi in F'$,
  hence $A x = 0$ by @thm:app-hahn-banach (ii). But then $Lambda(phi) = phi(x) = 0$ since
  $phi in (Ker A)^perp$, a contradiction.

  (iv) $A^* y = 0$ if and only if $ip(x, A^* y) = ip(A x, y) = 0$ for all $x in E$, i.e.
  $y in (Ran A)^perp$. Applying this to $A^*$ and using $A^(**) = A$ gives $Ker A = (Ran A^*)^perp$. Taking
  orthogonal complements and using @thm:app-projection (iv) gives the two remaining identities.
]

This proposition is how density of an RKHS in $L^p (mu)$ is characterized in @thm:mercer-lp-embedding: the
embedding has dense range if and only if its adjoint, an integral operator, is injective.

=== Weak convergence and weak compactness

In infinite dimensions, bounded sequences need not have norm-convergent subsequences (think of an
orthonormal sequence). The substitute is weak convergence: bounded sequences in Hilbert spaces (more
generally, in reflexive spaces) have *weakly* convergent subsequences. Together with the weak lower
semicontinuity of convex functionals (@thm:app-mazur) this yields the existence of minimizers
(@lem:app-existence-minimizer), and together with the Radon–Riesz property it yields norm convergence in
the stability theory of @sec:stab.

#definition(title: [Weak convergence])[
  Let $E$ be a normed space. A sequence $(x_n)$ in $E$ *converges weakly* to $x in E$, written
  $x_n weakto x$, if $phi(x_n) -> phi(x)$ for every $phi in E'$. If $E$ is a Hilbert space, by
  @thm:app-riesz this means $ip(x_n, y) -> ip(x, y)$ for every $y in E$.
] <def:app-weak>

#proposition(title: [Basic properties of weak convergence])[
  Let $E, F$ be normed spaces and $x_n weakto x$ in $E$.
  + Weak limits are unique, and norm convergence implies weak convergence.
  + $(x_n)$ is bounded.
  + $A x_n weakto A x$ for every $A in cal(L)(E, F)$.
  + If $E$ is a Hilbert space and $y_n -> y$ in norm, then $ip(x_n, y_n) -> ip(x, y)$.
  + If $E = H$ is an RKHS on a set $X$, then $x_n (t) -> x(t)$ for every $t in X$; that is, weak convergence
    implies pointwise convergence.
] <prop:app-weak-basic>

#proof[
  (i) Uniqueness follows from @thm:app-hahn-banach (ii), and $abs(phi(x_n) - phi(x)) <= norm(phi) norm(x_n - x)$.

  (ii) The functionals $J_E x_n in E''$ on the Banach space $E'$ satisfy
  $ sup_n abs((J_E x_n)(phi)) = sup_n abs(phi(x_n)) < oo quad "for every" phi in E', $
  so $sup_n norm(x_n) = sup_n norm(J_E x_n) < oo$ by @thm:app-uniform-boundedness.

  (iii) $psi(A x_n) = (A' psi)(x_n)$ for $psi in F'$.

  (iv) $abs(ip(x_n, y_n) - ip(x, y)) <= sup_k norm(x_k) norm(y_n - y) + abs(ip(x_n - x, y))$, and both terms
  tend to zero by (ii) and weak convergence.

  (v) Point evaluations are continuous linear functionals on an
  RKHS (@def:rkhs).
]

#example[
  If $(e_n)$ is an orthonormal sequence in a Hilbert space $H$, then $e_n weakto 0$, because
  $sum_n abs(ip(y, e_n))^2 <= norm(y)^2 < oo$ by Bessel's inequality, so $ip(e_n, y) -> 0$. But
  $norm(e_n) = 1$, so $(e_n)$ does not converge in norm, and $0 = norm(0) < liminf norm(e_n) = 1$. This shows
  that the inequality in @thm:app-weak-compactness (iii) can be strict, and that weak convergence alone does
  not give norm convergence (compare @thm:app-radon-riesz).
]

#theorem(title: [Weak compactness and weak lower semicontinuity of the norm])[
  + Let $H$ be a Hilbert space. Every bounded sequence in $H$ has a weakly convergent subsequence.
  + More generally, every bounded sequence in a reflexive Banach space has a weakly convergent subsequence.
  + Let $E$ be a normed space. If $x_n weakto x$ in $E$, then $norm(x) <= liminf_(n -> oo) norm(x_n)$.
] <thm:app-weak-compactness>

#proof[
  (i) Let $norm(x_n) <= C$ for all $n$. The closed linear span $M$ of ${x_n : n in NN}$ is separable (finite
  linear combinations with coefficients in $QQ$ or $QQ + i QQ$ are dense); let ${m_1, m_2, ...}$ be dense in
  $M$. For each $k$ the sequence $(ip(x_n, m_k))_n$ is bounded by $C norm(m_k)$, so by Bolzano–Weierstrass
  and a diagonal argument there is a subsequence $(x_(n_j))$ such that $(ip(x_(n_j), m_k))_j$ converges for
  every $k$. For $y in M$ and $epsilon > 0$ choose $m_k$ with $norm(y - m_k) < epsilon$; then
  $ abs(ip(x_(n_i), y) - ip(x_(n_j), y)) <= 2 C epsilon + abs(ip(x_(n_i), m_k) - ip(x_(n_j), m_k)), $
  so $(ip(x_(n_j), y))_j$ is a Cauchy sequence and converges. For $y in M^perp$ all terms vanish. Since
  $H = M plus.o M^perp$ (@thm:app-projection (iii)), $ell(y) := lim_j ip(y, x_(n_j))$ exists for every
  $y in H$. The functional $ell$ is linear, and $abs(ell(y)) <= C norm(y)$. By @thm:app-riesz there is
  $x in H$ with $ell(y) = ip(y, x)$ for all $y$; taking complex conjugates, $ip(x_(n_j), y) -> ip(x, y)$ for
  all $y$, i.e. $x_(n_j) weakto x$.

  (ii) @brezis2011[Thm. 3.18].

  (iii) By @thm:app-hahn-banach (ii) choose $phi in E'$ with $norm(phi) <= 1$ and $phi(x) = norm(x)$. Then
  $norm(x) = lim_n abs(phi(x_n)) <= liminf_n norm(x_n)$. (In a Hilbert space one can take
  $phi = ip(dot, x \/ norm(x))$ for $x != 0$.)
]

#theorem(title: [Radon–Riesz property of Hilbert spaces])[
  Let $H$ be a Hilbert space and $x_n weakto x$ in $H$. Then the following are equivalent:
  + $x_n -> x$ in norm;
  + $norm(x_n) -> norm(x)$;
  + $limsup_(n -> oo) norm(x_n) <= norm(x)$.
] <thm:app-radon-riesz>

#proof[
  (i) ⇒ (ii) ⇒ (iii) is clear. For (iii) ⇒ (i), expand
  $ norm(x_n - x)^2 = norm(x_n)^2 - 2 Re ip(x_n, x) + norm(x)^2. $
  Since $ip(x_n, x) -> ip(x, x) = norm(x)^2$ by weak convergence, (iii) gives
  $ limsup_(n -> oo) norm(x_n - x)^2 <= norm(x)^2 - 2 norm(x)^2 + norm(x)^2 = 0. $
]

The same property holds in uniformly convex Banach spaces, e.g. in $L^p (mu)$ for $1 < p < oo$
(@brezis2011[Prop. 3.32]), but we only need the Hilbert space case.

#remark(title: [Weak\* topology])[
  On a dual space $E'$ one also considers *weak\* convergence*: $phi_n -> phi$ weak\* if
  $phi_n (x) -> phi(x)$ for every $x in E$. By the Banach–Alaoglu theorem the closed unit ball of $E'$ is
  compact in the weak\* topology (@brezis2011[Thm. 3.16]). This is behind the weak\* compactness of
  subdifferentials in @sec:reg (see @def:reg-subdifferential). For Hilbert spaces, and more generally for
  reflexive spaces, weak and weak\* convergence on $E'$ coincide.
]

== Compact operators and the spectral theorem <sec:app-operators>

Mercer's theorem and the spectral description of an RKHS (@sec:mercer) rest on the integral operator
$T_K$ on $L^2 (mu)$ being compact, positive and self-adjoint, so that it can be diagonalized like a
symmetric positive semidefinite matrix. The eigenvalues then quantify how "large" $H_K$ is: $S_K$ is
Hilbert–Schmidt, $T_K$ is trace class, and the trace is $integral K(x, x) dif mu(x)$
(@thm:mercer-integral-operator). This section collects the necessary facts.

Throughout, $H$, $H_1$, $H_2$ are Hilbert spaces and $E$, $F$, $G$ are Banach spaces.

#definition(title: [Compact, Hilbert–Schmidt and trace-class operators])[
  + An operator $A in cal(L)(E, F)$ is *compact* if $A(B_E)$ is relatively compact in $F$; equivalently,
    for every bounded sequence $(x_n)$ in $E$ the sequence $(A x_n)$ has a convergent subsequence. It has
    *finite rank* if $Ran A$ is finite-dimensional. We write $cal(K)(E, F)$ for the set of compact operators.
  + An operator $T in cal(L)(H)$ is *self-adjoint* if $T^* = T$, and *positive* if it is self-adjoint and
    $ip(T x, x) >= 0$ for all $x in H$.
  + An operator $S in cal(L)(H_1, H_2)$ is a *Hilbert–Schmidt operator* if for some ONB $(e_i)_(i in I)$ of
    $H_1$
    $ norm(S)_HS^2 := sum_(i in I) norm(S e_i)_(H_2)^2 < oo. $
    By @thm:app-operator-facts (ii) this quantity does not depend on the choice of the ONB, and every
    Hilbert–Schmidt operator is compact.
  + A positive compact operator $T in cal(L)(H)$ with eigenvalues $lambda_1 >= lambda_2 >= ... > 0$ (repeated
    according to multiplicity, @thm:app-spectral) is *trace class* (or *nuclear*) if
    $tr T := sum_j lambda_j < oo$. More generally, a compact $T in cal(L)(H)$ is trace class if the positive
    compact operator $abs(T) := (T^* T)^(1\/2)$ (@thm:app-spectral (iii)) is trace class, and
    $norm(T)_1 := tr abs(T)$ is its *trace norm*.
] <def:app-compact-operators>

In this book trace-class operators only appear in the form $T = S^* S$ with $S$ Hilbert–Schmidt, which is
positive; for such $T$ the trace can be computed in any ONB (@thm:app-operator-facts (iii), (iv)).

#theorem(title: [Spectral theorem for compact self-adjoint operators])[
  Let $H$ be a Hilbert space and $T in cal(L)(H)$ compact and self-adjoint.
  + There are an index set $J = {1, ..., n}$ ($n in NN_0$) or $J = NN$, an orthonormal system
    $(e_j)_(j in J)$ in $H$ and real numbers $lambda_j != 0$ with $abs(lambda_1) >= abs(lambda_2) >= ...$ and
    $lambda_j -> 0$ if $J = NN$, such that $T e_j = lambda_j e_j$ for all $j$ and
    $ T x = sum_(j in J) lambda_j ip(x, e_j) e_j quad "for all" x in H, $
    with convergence in $H$.
  + $(e_j)_(j in J)$ is an ONB of $overline(Ran T) = (Ker T)^perp$. Every non-zero eigenvalue of $T$ occurs
    among the $lambda_j$, and $dim Ker(T - lambda I) = \#{j : lambda_j = lambda} < oo$ for $lambda != 0$.
    Moreover $norm(T) = abs(lambda_1)$ if $T != 0$.
  + $T$ is positive if and only if $lambda_j > 0$ for all $j$. In this case
    $ T^(1\/2) x := sum_(j in J) sqrt(lambda_j) ip(x, e_j) e_j $
    defines the unique positive operator $T^(1\/2) in cal(L)(H)$ with $(T^(1\/2))^2 = T$. It is compact,
    $Ker T^(1\/2) = Ker T$, $ip(T x, x) = norm(T^(1\/2) x)^2$, and
    $ Ran T^(1\/2) = { sum_(j in J) a_j sqrt(lambda_j) e_j : (a_j) in ell^2 (J) }. $
  + $T$ is Hilbert–Schmidt if and only if $sum_j lambda_j^2 < oo$, and then $norm(T)_HS^2 = sum_j lambda_j^2$.
] <thm:app-spectral>

#proof[
  (i) and the first statement of (ii): for separable $H$ see @brezis2011[Thm. 6.11], which gives an
  ONB of $H$ consisting of eigenvectors, together with @brezis2011[Sect. 6.2–6.3] (non-zero eigenvalues of
  compact operators have finite multiplicity and can only accumulate at $0$); see also @conway1990[Ch. II]
  and @werner2018[Ch. VI]. The general case reduces to the separable one: $Ran T subset.eq union.big_n T(n B_H)$
  is separable because $T(B_H)$ is relatively compact, and $H_0 := overline(Ran T) = (Ker T)^perp$
  (@prop:app-adjoint-kernel-range (iv), $T = T^*$) is invariant under $T$. The restriction of $T$ to $H_0$
  is compact, self-adjoint and injective, so the separable result gives an ONB of $H_0$ of eigenvectors with
  non-zero eigenvalues. Because only finitely many of these eigenvalues (counted with multiplicity) exceed
  any $epsilon > 0$ in absolute value, they can be enumerated in non-increasing order of absolute value. The
  expansion of $T x$ follows by writing $x = P_(H_0) x + (x - P_(H_0) x)$ with $x - P_(H_0) x in Ker T$.
  If $T x = lambda x$ with $lambda != 0$ and $x != 0$, then
  $lambda ip(x, e_j) = ip(T x, e_j) = ip(x, T e_j) = lambda_j ip(x, e_j)$ (the $lambda_j$ are real), so
  $ip(x, e_j) = 0$ unless $lambda_j = lambda$; since $x = T(x\/lambda) in H_0$, this gives
  $x in spn{e_j : lambda_j = lambda}$ and hence the second statement of (ii).

  For the rest, complete $(e_j)$ to an ONB of $H$ by an ONB of $Ker T$ (@thm:app-onb (iv)). Then
  $norm(T x)^2 = sum_j lambda_j^2 abs(ip(x, e_j))^2 <= lambda_1^2 norm(x)^2$ with equality for $x = e_1$,
  which gives $norm(T) = abs(lambda_1)$, and (iv) follows by computing the Hilbert–Schmidt norm in this ONB.

  (iii) $ip(T x, x) = sum_j lambda_j abs(ip(x, e_j))^2$, which is $>= 0$ for all $x$ if and only if all
  $lambda_j > 0$ (test with $x = e_j$). Let all $lambda_j > 0$. The series defining $T^(1\/2)$ converges by
  @thm:app-onb (ii), $T^(1\/2)$ is positive, $T^(1\/2) e_j = sqrt(lambda_j) e_j$, $T^(1\/2) = 0$ on $Ker T$,
  and hence $(T^(1\/2))^2 = T$ and $ip(T x, x) = sum_j lambda_j abs(ip(x, e_j))^2 = norm(T^(1\/2) x)^2$.
  Both $Ker T^(1\/2)$ and $Ker T$ equal ${x : ip(x, e_j) = 0 "for all" j}$, by the series expansions and
  $lambda_j > 0$. Compactness: the finite-rank operators
  $x |-> sum_(j <= n) sqrt(lambda_j) ip(x, e_j) e_j$ converge to $T^(1\/2)$ in operator norm (the error has
  norm $sup_(j > n) sqrt(lambda_j) -> 0$), and norm limits of finite-rank operators are compact
  (@thm:app-operator-facts (i)). The description of $Ran T^(1\/2)$ holds because the coefficient sequence
  $(ip(x, e_j))_j$ of $x in H$ ranges over all of $ell^2 (J)$ (@thm:app-onb (ii)).

  Uniqueness: let $S$ be positive with $S^2 = T$. Then $S T = S^3 = T S$, so $S$ maps each eigenspace
  $V_lambda := Ker(T - lambda I)$ into itself. For $lambda != 0$, $V_lambda$ is finite-dimensional and
  $S|_(V_lambda)$ is a positive self-adjoint operator with square $lambda I$; diagonalizing it (finite
  dimensional spectral theorem) shows that $S = sqrt(lambda) I$ on $V_lambda$. For $x in Ker T$,
  $norm(S x)^2 = ip(S^2 x, x) = ip(T x, x) = 0$. Since the $V_lambda$, $lambda != 0$, together with
  $Ker T$ span a dense subspace, $S = T^(1\/2)$.
]

#theorem(title: [Facts about compact, Hilbert–Schmidt and trace-class operators])[
  + (Compact operators) $cal(K)(E, F)$ is a closed subspace of $cal(L)(E, F)$. If $T in cal(K)(E, F)$,
    $A in cal(L)(F, G)$ and $B in cal(L)(G, E)$, then $A T in cal(K)(E, G)$ and $T B in cal(K)(G, F)$.
    Bounded finite-rank operators are compact, hence so are norm limits of such operators. (Schauder) $T$ is
    compact if and only if $T'$ is compact. For Hilbert spaces, $T$ is compact if and only if $T^*$ is.
  + (Hilbert–Schmidt operators) Let $S in cal(L)(H_1, H_2)$. For all ONBs $(e_i)$ of $H_1$ and $(f_k)$ of
    $H_2$,
    $ sum_i norm(S e_i)^2 = sum_(i, k) abs(ip(S e_i, f_k))^2 = sum_k norm(S^* f_k)^2. $
    Hence $norm(S)_HS$ is independent of the ONB and $norm(S^*)_HS = norm(S)_HS$. Moreover
    $norm(S) <= norm(S)_HS$, $norm(A S B)_HS <= norm(A) norm(S)_HS norm(B)$ for bounded $A$, $B$, and every
    Hilbert–Schmidt operator is compact.
  + If $S in cal(L)(H_1, H_2)$ is Hilbert–Schmidt, then $T := S^* S in cal(L)(H_1)$ is positive, compact and
    trace class, and for every ONB $(e_i)$ of $H_1$
    $ tr(S^* S) = sum_i ip(S^* S e_i, e_i) = sum_i norm(S e_i)^2 = norm(S)_HS^2. $
  + Let $T in cal(L)(H)$ be positive and compact with eigenvalues $(lambda_j)$. Then
    $sum_i ip(T e_i, e_i) = sum_j lambda_j = norm(T^(1\/2))_HS^2$ for every ONB $(e_i)$ of $H$ (both sides may
    be $+oo$). If $T$ is trace class, then it is Hilbert–Schmidt with
    $norm(T)_HS^2 = sum_j lambda_j^2 <= lambda_1 tr T$.
] <thm:app-operator-facts>

#proof[
  (i) For the first statements see @brezis2011[Ch. 6] (Schauder's theorem is @brezis2011[Thm. 6.4]); the
  ideal property is immediate from the sequence characterization, and finite-rank bounded operators map
  bounded sets to bounded subsets of a finite-dimensional space. For the Hilbert-space statement let
  $T in cal(K)(H_1, H_2)$; then $T T^*$ is compact. If $norm(y_n) <= C$, choose a subsequence with
  $(T T^* y_(n_k))$ convergent. Then
  $norm(T^* (y_(n_k) - y_(n_l)))^2 = ip(T T^* (y_(n_k) - y_(n_l)), y_(n_k) - y_(n_l)) <= 2 C norm(T T^* (y_(n_k) - y_(n_l))) -> 0$,
  so $(T^* y_(n_k))$ is Cauchy. Hence $T^*$ is compact; apply this to $T^*$ for the converse.

  (ii) By Parseval (@thm:app-onb (iii)) in $H_2$ and in $H_1$,
  $norm(S e_i)^2 = sum_k abs(ip(S e_i, f_k))^2$ and
  $norm(S^* f_k)^2 = sum_i abs(ip(S^* f_k, e_i))^2 = sum_i abs(ip(S e_i, f_k))^2$; sums of non-negative
  terms may be interchanged. Since the left-hand side does not depend on $(f_k)$ and the right-hand side
  not on $(e_i)$, neither depends on the ONB. If $norm(x) = 1$, complete $x$ to an ONB to get
  $norm(S x)^2 <= norm(S)_HS^2$. Clearly $norm(A S)_HS <= norm(A) norm(S)_HS$, and
  $norm(S B)_HS = norm(B^* S^*)_HS <= norm(B^*) norm(S^*)_HS = norm(B) norm(S)_HS$. For compactness, note
  that only countably many $e_i$, say $e_1, e_2, ...$, satisfy $S e_i != 0$. The finite-rank operators
  $S_n x := sum_(i <= n) ip(x, e_i) S e_i$ satisfy, by Cauchy–Schwarz in $ell^2$,
  $ norm((S - S_n) x) = norm(sum_(i > n) ip(x, e_i) S e_i) <= (sum_(i > n) abs(ip(x, e_i))^2)^(1\/2) (sum_(i > n) norm(S e_i)^2)^(1\/2) <= norm(x) (sum_(i > n) norm(S e_i)^2)^(1\/2), $
  so $norm(S - S_n) -> 0$ and $S$ is compact by (i).

  (iii) $T^* = S^* S^(**) = T$ and $ip(T x, x) = norm(S x)^2 >= 0$, so $T$ is positive; it is compact by
  (ii) and (i). Moreover $ip(T e_i, e_i) = norm(S e_i)^2$, so $sum_i ip(T e_i, e_i) = norm(S)_HS^2 < oo$ for
  every ONB, and by (iv) this equals $sum_j lambda_j = tr T$.

  (iv) $ip(T e_i, e_i) = norm(T^(1\/2) e_i)^2$ by @thm:app-spectral (iii), so
  $sum_i ip(T e_i, e_i) = norm(T^(1\/2))_HS^2$, independently of the ONB by (ii). Evaluating in an ONB
  consisting of the eigenvectors $e_j$ and an ONB of $Ker T$ gives $sum_j lambda_j$. If this is finite, then
  $sum_j lambda_j^2 <= lambda_1 sum_j lambda_j < oo$, and @thm:app-spectral (iv) applies.
]

#proposition(title: [Integral operators with square-integrable kernels])[
  Let $(Omega, cal(A), mu)$ be a σ-finite measure space and $k in cal(L)^2 (mu times.o mu)$. Then
  $ (T_k g)(x) := integral_Omega k(x, y) g(y) dif mu(y) $
  defines (for $mu$-a.e. $x$) an operator $T_k in cal(L)(L^2 (mu))$ which is Hilbert–Schmidt with
  $norm(T_k)_HS <= norm(k)_(L^2 (mu times.o mu))$, hence compact. If $L^2 (mu)$ is separable, then
  $norm(T_k)_HS = norm(k)_(L^2 (mu times.o mu))$. If $k(y, x) = overline(k(x, y))$ for
  $mu times.o mu$-a.e. $(x, y)$, then $T_k$ is self-adjoint.
] <prop:app-integral-operators>

#proof[
  By Tonelli, $integral (integral abs(k(x, y))^2 dif mu(y)) dif mu(x) = norm(k)_2^2 < oo$, so
  $k_x := k(x, dot) in cal(L)^2 (mu)$ for all $x$ outside a null set $N$. For such $x$,
  $(T_k g)(x) = ip(k_x, overline(g))_(L^2 (mu))$ is well defined and $abs((T_k g)(x)) <= norm(k_x)_2 norm(g)_2$;
  it is measurable in $x$ by @thm:app-fubini (i), applied to the positive and negative parts of the real
  and imaginary parts of $k(x, y) g(y)$ (all of which have finite integrals in $y$ for $x in.not N$). Moreover
  $norm(T_k g)_2^2 <= norm(g)_2^2 integral norm(k_x)_2^2 dif mu(x) = norm(k)_2^2 norm(g)_2^2$, and changing
  $g$ or $k$ on a null set changes $T_k g$ only on a null set.

  Let $(e_i)_(i in I)$ be an ONB of $L^2 (mu)$; then so is $(overline(e_i))_(i in I)$. For a finite set
  $I_0 subset.eq I$, Bessel's inequality gives, for $x in.not N$,
  $sum_(i in I_0) abs((T_k e_i)(x))^2 = sum_(i in I_0) abs(ip(k_x, overline(e_i)))^2 <= norm(k_x)_2^2$, and
  integrating over $x$ yields $sum_(i in I_0) norm(T_k e_i)_2^2 <= norm(k)_2^2$. Taking the supremum over
  $I_0$ proves $norm(T_k)_HS <= norm(k)_2$. If $I$ is countable, Parseval and monotone convergence give
  equality:
  $ sum_i norm(T_k e_i)_2^2 = integral sum_i abs(ip(k_x, overline(e_i)))^2 dif mu(x) = integral norm(k_x)_2^2 dif mu(x) = norm(k)_2^2. $
  Finally, let $k(y, x) = overline(k(x, y))$. Since
  $integral.double abs(k(x, y) g(y) h(x)) dif mu(y) dif mu(x) <= norm(k)_2 norm(g)_2 norm(h)_2$ by the
  Cauchy–Schwarz inequality in $L^2 (mu times.o mu)$, Fubini's theorem gives
  $ip(T_k g, h) = integral.double k(x, y) g(y) overline(h(x)) dif mu(y) dif mu(x) = ip(g, T_k h)$.
]

== Convex analysis <sec:app-convex>

Convexity is the property that makes regularized risk minimization well behaved. It gives existence and
uniqueness of minimizers (@thm:reg-existence, @prop:reg-uniqueness, @prop:stab-min-norm), local Lipschitz
continuity of convex losses (used for the growth estimates of @prop:loss-distance-risk-bounds and for bounds
on subgradients in @thm:stab-measure), and concavity and continuity of the approximation error function
(@prop:stab-approx-error). Subdifferentials are treated in @sec:reg. For the general theory see
@rockafellar1970 (finite dimensions), @bauschke2011 (Hilbert spaces), and @ekeland1976 and @phelps1993
(Banach spaces).

#definition(title: [Convex and lower semicontinuous functions])[
  Let $V$ be a vector space over $KK$ and $phi: V -> (-oo, oo]$. (Convexity only involves real scalars, so
  complex spaces are regarded as real ones here.)
  + $dom phi := {x in V : phi(x) < oo}$ is the *effective domain* of $phi$.
  + $phi$ is *convex* if $phi(t x + (1 - t) y) <= t phi(x) + (1 - t) phi(y)$ for all $x, y in V$ and
    $t in (0, 1)$ (with the conventions $a + oo = oo$ and $t dot oo = oo$ for $t > 0$). It is *strictly
    convex* if the inequality is strict whenever $x != y$ are in $dom phi$ and $t in (0, 1)$. A function
    $psi: V -> [-oo, oo)$ is *(strictly) concave* if $-psi$ is (strictly) convex.
  + Let $V$ be a normed space. $phi$ is *lower semicontinuous* (lsc) if $x_n -> x$ implies
    $phi(x) <= liminf_(n -> oo) phi(x_n)$; equivalently, every sublevel set ${x : phi(x) <= c}$,
    $c in RR$, is closed. $psi$ is *upper semicontinuous* (usc) if $-psi$ is lsc.
  + For a function $f: A -> KK$ on a subset $A$ of a normed space, the *Lipschitz constant* is
    $abs(f)_1 := sup_(x, y in A, x != y) abs(f(x) - f(y)) \/ norm(x - y) in [0, oo]$. For $f: RR -> RR$ we write
    $abs(f|_([a, b]))_1$ and $norm(f|_([a, b]))_oo := sup_(t in [a, b]) abs(f(t))$ for the Lipschitz constant
    and the supremum of the restriction to $[a, b]$. $f$ is *locally Lipschitz continuous* if
    $abs(f|_([a, b]))_1 < oo$ for all $a < b$.
] <def:app-convex>

The equivalence in (iii): if $phi$ is sequentially lsc and $x_n -> x$ with $phi(x_n) <= c$, then
$phi(x) <= c$. Conversely, if the sublevel sets are closed and $phi(x) > c > liminf phi(x_n)$ for some $c$,
then infinitely many $x_n$ lie in ${phi <= c}$, and so does their limit $x$, a contradiction.

=== Convex functions of one variable

#lemma(title: [Three-slope inequality])[
  Let $I subset.eq RR$ be an interval and $f: I -> RR$ convex. For $x < y < z$ in $I$,
  $ (f(y) - f(x))/(y - x) <= (f(z) - f(x))/(z - x) <= (f(z) - f(y))/(z - y). $
] <lem:app-three-slopes>

#proof[
  Write $y = (1 - theta) x + theta z$ with $theta = (y - x)\/(z - x) in (0, 1)$. Convexity gives
  $f(y) <= (1 - theta) f(x) + theta f(z)$. Subtracting $f(x)$ and dividing by $y - x = theta (z - x)$ gives
  the first inequality. Subtracting $f(z)$ gives $f(y) - f(z) <= (1 - theta)(f(x) - f(z))$; dividing by
  $-(z - y) = -(1 - theta)(z - x)$ gives the second.
]

#lemma(title: [Convex functions on $RR$ are locally Lipschitz])[
  Let $f: RR -> RR$ be convex.
  + For all $a <= b$ and $delta > 0$,
    $ abs(f|_([a, b]))_1 <= 2/delta norm(f|_([a - delta, b + delta]))_oo. $
    In particular, $f$ is locally Lipschitz continuous (hence continuous), and for every $t > 0$
    $ abs(f|_([-t, t]))_1 <= 2/t norm(f|_([-2t, 2t]))_oo. $
  + If $f(0) = 0$, then $r |-> f(r)\/r$ is non-decreasing on $RR without {0}$ (in particular on
    $(0, oo)$), and for every $t > 0$
    $ norm(f|_([-t, t]))_oo <= t abs(f|_([-t, t]))_1. $
  + If $a < r < b$ and $s in RR$ satisfies $f(u) >= f(r) + s (u - r)$ for all $u in [a, b]$ (for instance, if
    $s$ is a subgradient of $f$ at $r$, @def:reg-subdifferential), then $abs(s) <= abs(f|_([a, b]))_1$.
] <lem:app-convex-lipschitz>

#proof[
  (i) Let $M := norm(f|_([a - delta, b + delta]))_oo$ and $a <= x < y <= b$. The outer inequality of
  @lem:app-three-slopes (the slope of the left secant is at most the slope of the right one), applied to
  the points $x < y < b + delta$, gives
  $ (f(y) - f(x))/(y - x) <= (f(b + delta) - f(y))/(b + delta - y) <= (2 M)/delta, $
  because $b + delta - y >= delta$. Applied to $a - delta < x < y$, it gives
  $ (f(y) - f(x))/(y - x) >= (f(x) - f(a - delta))/(x - a + delta) >= -(2 M)/delta. $
  Hence $abs(f(y) - f(x)) <= (2M\/delta) abs(y - x)$. For the special case take $a = -t$, $b = t$, $delta = t$.

  (ii) For $r != 0$, $f(r)\/r = (f(r) - f(0))\/(r - 0)$ is the slope of the secant through $0$ and $r$. If
  $0 < r < s$, the first inequality of @lem:app-three-slopes for $0 < r < s$ gives $f(r)\/r <= f(s)\/s$. If
  $r < s < 0$, the second inequality for $r < s < 0$ gives $f(r)\/r <= f(s)\/s$. If $r < 0 < s$, the outer
  inequality for $r < 0 < s$ gives the same. For the last claim, $abs(f(r)) = abs(f(r) - f(0)) <= abs(f|_([-t, t]))_1 abs(r)$ for
  $abs(r) <= t$ (this part does not use convexity).

  (iii) For $u in (r, b]$ the assumption gives $s <= (f(u) - f(r))\/(u - r) <= abs(f|_([a, b]))_1$, and for
  $u in [a, r)$ it gives $s >= (f(r) - f(u))\/(r - u) >= -abs(f|_([a, b]))_1$.
]

#remark[
  The proofs of (i) and (iii) only use the values of $f$ on $[a - delta, b + delta]$ and on $[a, b]$,
  respectively. Hence they apply verbatim to convex functions defined on an interval containing these sets.
  In particular, a finite convex function on an *open* interval is locally Lipschitz continuous there.
  Combining (i) and (ii): if $f$ is convex with $f(0) = 0$, then
  $abs(f|_([-t, t]))_1 <= 2/t norm(f|_([-2t, 2t]))_oo <= 4 abs(f|_([-2t, 2t]))_1$.
  At the end points of a closed interval, a convex function need not be continuous: $f = ind_({0})$ on
  $[0, 1]$ is convex.
]

=== Suprema of affine functions

#lemma(title: [Suprema of affine functions])[
  Let $V$ be a real normed space and $(f_iota)_(iota in I)$, $I != emptyset$, a family of continuous affine
  functions $f_iota: V -> RR$ (i.e. $f_iota = ell_iota + c_iota$ with $ell_iota in V'$, $c_iota in RR$).
  + $f := sup_(iota in I) f_iota: V -> (-oo, oo]$ is convex and lower semicontinuous.
  + $g := inf_(iota in I) f_iota: V -> [-oo, oo)$ is concave and upper semicontinuous.
  + Let $V = RR$ and let $J subset.eq RR$ be an interval. If $f$ is finite on $J$, then $f|_J$ is continuous;
    if $g$ is finite on $J$, then $g|_J$ is continuous. This includes the end points of $J$ that belong to
    $J$; e.g., if $g$ is finite on $J = [0, oo)$, then $g$ is continuous on $[0, oo)$, in particular at $0$.
] <lem:app-sup-affine>

#proof[
  (i) For $x, y in V$, $t in (0, 1)$ and every $iota in I$,
  $ f_iota (t x + (1 - t) y) = t f_iota (x) + (1 - t) f_iota (y) <= t f(x) + (1 - t) f(y); $
  taking the supremum over $iota$ gives convexity. For $c in RR$ the sublevel set
  ${f <= c} = inter.big_iota {f_iota <= c}$ is an intersection of closed sets, hence closed.

  (ii) Apply (i) to the family $(-f_iota)$, since $-g = sup_iota (-f_iota)$.

  (iii) Since $-g$ is the supremum of the affine functions $-f_iota$, it suffices to treat $f$. Let $f$ be finite on $J$ and $t_0 in J$. If $t_0$ is an interior
  point of $J$, then $f$ is a finite convex function on the open interval $op("int") J$, hence continuous at
  $t_0$ by @lem:app-convex-lipschitz and the remark following it. Let $t_0$ be an end point, say the left
  one, and let $b in J$ with $b > t_0$ (if $J = {t_0}$ there is nothing to show). For $t in (t_0, b]$ write
  $t = (1 - theta) t_0 + theta b$ with $theta = (t - t_0)\/(b - t_0)$. By convexity
  $f(t) <= (1 - theta) f(t_0) + theta f(b) -> f(t_0)$ as $t -> t_0$, so $limsup_(t -> t_0) f(t) <= f(t_0)$,
  and lower semicontinuity gives $liminf_(t -> t_0) f(t) >= f(t_0)$.
]

The lemma is applied in @prop:stab-approx-error to the approximation error function
$A(lambda) = inf_(f in H) (risk(L, P)(f) + lambda norm(f)_H^2) - cal(R)^*_(L, P, H)$, which is an infimum of
affine functions of $lambda$. Conversely, every lsc convex function $V -> (-oo, oo]$ is the supremum of its
continuous affine minorants (Fenchel–Moreau); see @ekeland1976[Ch. I] and @bauschke2011.

=== Weak lower semicontinuity and existence of minimizers

#theorem(title: [Mazur])[
  Let $E$ be a normed space.
  + If $C subset.eq E$ is convex and closed, $x_n in C$ and $x_n weakto x$, then $x in C$.
  + If $phi: E -> (-oo, oo]$ is convex and lower semicontinuous and $x_n weakto x$, then
    $phi(x) <= liminf_(n -> oo) phi(x_n)$.
] <thm:app-mazur>

#proof[
  (i) If $x in.not C$ (so $C != emptyset$), @thm:app-hahn-banach (iv) gives $phi in E'$ and $gamma in RR$
  with $Re phi(x_n) <= gamma < Re phi(x)$ for all $n$; letting $n -> oo$ gives $Re phi(x) <= gamma$, a
  contradiction. In a Hilbert space one can avoid the Hahn–Banach theorem: with $p := P_C x$,
  @thm:app-projection (ii) gives $Re ip(x - p, x_n - p) <= 0$, and letting $n -> oo$ yields
  $norm(x - p)^2 <= 0$, so $x = p in C$.

  (ii) Let $ell := liminf_n phi(x_n)$; if $ell = oo$ there is nothing to prove. For every real $c > ell$,
  infinitely many $x_n$ lie in the sublevel set ${phi <= c}$, which is convex (by convexity of $phi$) and
  closed (by lower semicontinuity). The corresponding subsequence still converges weakly to $x$, so
  $phi(x) <= c$ by (i). Since $c > ell$ was arbitrary, $phi(x) <= ell$.
]

#lemma(title: [Existence of minimizers])[
  Let $E$ be a reflexive Banach space (for instance a Hilbert space) and let $phi: E -> (-oo, oo]$ be
  convex and lower semicontinuous. Suppose that there is $M in RR$ such that the sublevel set
  $ {x in E : phi(x) <= M} $
  is non-empty and bounded. Then $phi$ attains its infimum: there is $x^* in E$ with
  $phi(x^*) = inf_(x in E) phi(x) in RR$. The set of minimizers is convex, closed and bounded. If $phi$ is
  strictly convex, the minimizer is unique.
] <lem:app-existence-minimizer>

#proof[
  The idea is the "direct method of the calculus of variations": a minimizing sequence is bounded, hence has
  a weakly convergent subsequence, and the weak limit is a minimizer by weak lower semicontinuity. Let
  $S := {phi <= M}$ and $m := inf_E phi in [-oo, M]$. Points outside $S$ have $phi > M >= m$, so
  $m = inf_S phi$, and there are $x_n in S$ with $phi(x_n) -> m$. Since $S$ is bounded,
  @thm:app-weak-compactness (ii) (or (i) for Hilbert spaces) yields a subsequence $x_(n_k) weakto x^*$. By
  @thm:app-mazur (ii), $phi(x^*) <= liminf_k phi(x_(n_k)) = m$. As $phi(x^*) > -oo$, it follows that
  $m > -oo$ and $phi(x^*) = m$. The set of minimizers is the sublevel set ${phi <= m} subset.eq S$, which is
  convex, closed and bounded. If $phi$ is strictly convex and $x != y$ are minimizers, then $x, y in dom phi$
  and $phi((x + y)\/2) < (phi(x) + phi(y))\/2 = m$, which is impossible.
]

#remark(title: [On the hypotheses])[
  If $phi$ is *coercive*, i.e. $phi(x) -> oo$ as $norm(x) -> oo$, and $phi$ is not identically $+oo$, then
  every sublevel set is bounded and the lemma applies; this is the case for regularized risks
  $risk(L, P)(f) + lambda norm(f)_H^2$ with $lambda > 0$. None of the hypotheses can be dropped:
  + *Bounded sublevel set.* $phi(x) = e^x$ on $RR$ is convex and continuous, but has no minimizer.
  + *Lower semicontinuity.* $phi: RR -> (-oo, oo]$ with $phi(0) = 1$, $phi(x) = x$ for $x > 0$ and
    $phi(x) = oo$ for $x < 0$ is convex, and ${phi <= 1} = [0, 1]$, but $inf phi = 0$ is not attained.
  + *Convexity.* Let $(e_n)$ be an ONB of $ell^2$ and
    $phi(x) := sum_n abs(ip(x, e_n))^2 \/ n + (1 - norm(x)^2)^2$. Then $phi$ is continuous, ${phi <= 1}$ is
    bounded (it lies in the ball of radius $sqrt(2)$), and $phi(e_n) = 1\/n -> 0$; but $phi(x) = 0$ would require
    $x = 0$, where $phi(0) = 1$. So $inf phi = 0$ is not attained. (Here $e_n weakto 0$, but $phi$ is not weakly lsc.)
  + *Reflexivity.* On $c_0$ (null sequences with the supremum norm) let $phi(x) := -sum_n 2^(-n) x_n$ if
    $norm(x)_oo <= 1$ and $phi(x) := oo$ otherwise. Then $phi$ is convex and lsc with bounded sublevel sets,
    and $inf phi = -1$, but the infimum would require $x_n = 1$ for all $n$, which is not a null sequence.
]

== Approximation and compactness in spaces of continuous functions <sec:app-approximation>

Universal kernels (@sec:univ) are defined by a density property in $C(X)$, and the main tool to establish
density is the Stone–Weierstrass theorem (@thm:univ-criterion, @ex:univ-fourier). The Tietze extension
theorem allows passing to compact subsets (@prop:univ-properties), Dini's theorem upgrades the pointwise
convergence of Mercer's series on the diagonal to uniform convergence (@thm:mercer), and the Arzelà–Ascoli
theorem characterizes compact sets of continuous functions (@prop:rkhs-compact-embedding). Separability of
$C(X)$ is used in @sec:loss.

For a compact topological space $X$, $C(X) = C(X; KK)$ denotes the space of continuous functions
$X -> KK$ with the supremum norm $norm(f)_oo = sup_(x in X) abs(f(x))$; it is a Banach space. We write
$C(X; RR)$ and $C(X; CC)$ when the scalar field matters.

#theorem(title: [Stone–Weierstrass])[
  Let $X$ be a compact Hausdorff space (for instance a compact metric space).
  + (Real version) Let $cal(A) subset.eq C(X; RR)$ be a subalgebra (a linear subspace closed under
    pointwise multiplication) that *separates points* (for all $x != y$ in $X$ there is $f in cal(A)$ with
    $f(x) != f(y)$) and *vanishes nowhere* (for every $x in X$ there is $f in cal(A)$ with $f(x) != 0$). Then
    $cal(A)$ is dense in $C(X; RR)$.
  + (Complex version) Let $cal(A) subset.eq C(X; CC)$ be a subalgebra that separates points, vanishes
    nowhere and is *closed under complex conjugation* ($f in cal(A) => overline(f) in cal(A)$). Then
    $cal(A)$ is dense in $C(X; CC)$.
] <thm:app-stone-weierstrass>

#proof[
  See @dudley2002[Sect. 2.4] for the real version. For the complex version let
  $cal(A)_RR := {f in cal(A) : f "real-valued"}$, a real subalgebra of $C(X; RR)$. Because $cal(A)$ is closed
  under conjugation, $Re f = (f + overline(f))\/2$ and $Im f = Re(-i f)$ lie in $cal(A)_RR$ for every
  $f in cal(A)$. Hence $cal(A)_RR$ separates points and vanishes nowhere (if $f(x) != f(y)$, then
  $Re f$ or $Im f$ separates $x$ and $y$), so it is dense in $C(X; RR)$ by (i). Given $g in C(X; CC)$,
  approximate $Re g$ and $Im g$ by $u, v in cal(A)_RR$; then $u + i v in cal(A)$ approximates $g$.
]

If $cal(A)$ contains the constant functions, it vanishes nowhere automatically. The conjugation hypothesis in
(ii) cannot be dropped: the polynomials in $z$ separate the points of the closed unit disk
$overline(DD) subset.eq CC$ and contain the constants, but their uniform limits are holomorphic in the open
disk, so $z |-> overline(z)$ is not such a limit.

#example(title: [Polynomials and trigonometric polynomials])[
  + (Weierstrass) For compact $X subset.eq RR^d$ the polynomials in $x_1, ..., x_d$ with real coefficients
    are dense in $C(X; RR)$: they form an algebra containing the constants, and the coordinate functions
    separate points.
  + Let $TT^d := RR^d \/ (2 pi ZZ)^d$ be the $d$-dimensional torus (a compact metric space). The
    *trigonometric polynomials* $spn{x |-> e^(i k dot x) : k in ZZ^d}$ are dense in $C(TT^d; CC)$, and the
    real trigonometric polynomials $spn{cos(k dot x), sin(k dot x) : k in ZZ^d}$ are dense in
    $C(TT^d; RR)$.
] <ex:app-trig-polynomials>

#proof[
  (ii) The span of the functions $e_k (x) := e^(i k dot x)$ is an algebra since $e_k e_l = e_(k + l)$, it is
  closed under conjugation since $overline(e_k) = e_(-k)$, and it contains $e_0 = 1$. If $x != y$ in $TT^d$,
  then $x_m - y_m in.not 2 pi ZZ$ for some coordinate $m$, and $e_(u_m)$ with $u_m$ the $m$-th unit vector
  separates $x$ and $y$. Apply @thm:app-stone-weierstrass (ii). For the real statement, if $f in C(TT^d; RR)$
  and $p$ is a complex trigonometric polynomial with $norm(f - p)_oo < epsilon$, then $Re p$ is a real
  trigonometric polynomial with $norm(f - Re p)_oo < epsilon$.
]

#proposition(title: [Separability of $C(X)$])[
  If $X$ is a compact metric space, then $C(X)$ is separable.
] <prop:app-cx-separable>

#proof[
  Let ${x_1, x_2, ...}$ be dense in $X$ (@prop:app-polish (ii)) and $g_k := d(dot, x_k) in C(X; RR)$. The
  algebra $cal(A)$ generated by $1$ and the $g_k$ separates points: if $x != y$, choose $x_k$ with
  $d(x, x_k) < d(x, y)\/2$; then $g_k (y) >= d(x, y) - d(x, x_k) > d(x, y)\/2 > g_k (x)$. By
  @thm:app-stone-weierstrass (i), $cal(A)$ is dense in $C(X; RR)$. The polynomials in finitely many $g_k$ with
  rational coefficients form a countable set that is dense in $cal(A)$, hence in $C(X; RR)$. For
  $KK = CC$ use real and imaginary parts.
]

#theorem(title: [Arzelà–Ascoli])[
  Let $X$ be a compact metric space. A set $cal(F) subset.eq C(X)$ is relatively compact in
  $(C(X), norm(dot)_oo)$ if and only if it is bounded and *equicontinuous*, i.e. for every $epsilon > 0$
  there is $delta > 0$ such that $abs(f(x) - f(x')) < epsilon$ for all $f in cal(F)$ and all $x, x' in X$ with
  $d(x, x') < delta$.
] <thm:app-arzela-ascoli>

#proof[
  See @brezis2011[Thm. 4.25] for sufficiency and @dudley2002[Sect. 2.4] for the full statement. Necessity is
  elementary: a relatively compact set is bounded, and it is covered by finitely many $epsilon\/3$-balls
  whose centres $f_1, ..., f_m$ are uniformly continuous; a common $delta$ for $f_1, ..., f_m$ and
  $epsilon\/3$ works for all of $cal(F)$ and $epsilon$.
]

#theorem(title: [Dini])[
  Let $X$ be a compact topological space and let $f, f_1, f_2, ...: X -> RR$ be continuous functions such
  that $f_1 (x) <= f_2 (x) <= ...$ and $f_n (x) -> f(x)$ for every $x in X$. Then $f_n -> f$ uniformly on $X$.
  The same holds for non-increasing sequences.
] <thm:app-dini>

#proof[
  Let $g_n := f - f_n$. Then $g_n$ is continuous, $g_n >= g_(n + 1) >= 0$, and $g_n -> 0$ pointwise. Let
  $epsilon > 0$ and $U_n := {x : g_n (x) < epsilon}$. The sets $U_n$ are open, increasing in $n$ (since
  $g_n$ decreases), and cover $X$ (since $g_n (x) -> 0$ for each $x$). By compactness finitely many of them
  cover $X$, hence $U_N = X$ for some $N$. For $n >= N$ and all $x$, $0 <= g_n (x) <= g_N (x) < epsilon$.
  For non-increasing sequences apply this to $-f_n$.
]

In @thm:mercer the theorem is applied to the partial sums $sum_(j <= n) lambda_j abs(e_j (x))^2$ of a series
of non-negative continuous functions whose sum $K(x, x)$ is continuous. None of the hypotheses can be dropped:
$x^n -> 0$ on $[0, 1)$ is monotone with continuous limit, but $X$ is not compact; on $[0, 1]$ the limit is
discontinuous; and the "moving bumps" $f_n (x) = max{0, 1 - abs(n x - 2)}$ on $[0, 1]$ converge pointwise to $0$
with $norm(f_n)_oo = 1$ for $n >= 2$, but not monotonically.

#theorem(title: [Tietze extension theorem])[
  Let $X$ be a metric space, $A subset.eq X$ closed and $f: A -> KK$ continuous and bounded. Then there is a
  continuous $F: X -> KK$ with $F|_A = f$ and $sup_(x in X) abs(F(x)) = sup_(a in A) abs(f(a))$.
] <thm:app-tietze>

#proof[
  The theorem holds more generally for normal topological spaces (Urysohn–Tietze); we give the short
  proof for metric spaces. First, if $A_+, A_- subset.eq X$ are disjoint closed sets, then
  $ u(x) := (dist(x, A_-) - dist(x, A_+))/(dist(x, A_-) + dist(x, A_+)) $
  is continuous on $X$ (the denominator vanishes only on $A_+ inter A_- = emptyset$), $abs(u) <= 1$,
  $u = 1$ on $A_+$ and $u = -1$ on $A_-$. (If both sets are empty take $u equiv 0$; if only $A_+$ is empty
  take $u equiv -1$; if only $A_-$ is empty take $u equiv 1$.)

  Let $KK = RR$ and $c := sup_A abs(f)$; we may assume $c > 0$. *Step:* if $g: A -> RR$ is continuous with
  $abs(g) <= c'$, let $A_plus.minus := {a in A : plus.minus g(a) >= c'\/3}$ (closed in $A$, hence in $X$, and
  disjoint) and $h := (c'\/3) u$. Then $h in C(X; RR)$, $abs(h) <= c'\/3$ on $X$, and $abs(g - h) <= 2c'\/3$
  on $A$: on $A_+$ we have $g - h = g - c'\/3 in [0, 2c'\/3]$, on $A_-$ similarly, and elsewhere
  $abs(g) < c'\/3$ and $abs(h) <= c'\/3$. Starting from $g_0 := f$ and $c_0 := c$, the step produces
  $h_n in C(X; RR)$ with $abs(h_n) <= c_n \/ 3$ on $X$, where $c_n := (2\/3)^n c$, such that
  $g_(n+1) := g_n - h_n|_A$ satisfies $abs(g_(n+1)) <= c_(n+1)$. The series $F := sum_(n >= 0) h_n$ converges
  uniformly, so $F$ is continuous, and $abs(F) <= sum_n c_n\/3 = c$. On $A$,
  $f - sum_(n < m) h_n = g_m -> 0$, so $F|_A = f$. Since $F$ extends $f$, $sup_X abs(F) >= c$.

  If $KK = CC$, extend real and imaginary parts to a continuous $F_0: X -> CC$ with $F_0|_A = f$ and compose
  with the continuous radial retraction $rho(z) := z$ for $abs(z) <= c$, $rho(z) := c z\/abs(z)$ for $abs(z) > c$;
  then $F := rho compose F_0$ extends $f$ and $abs(F) <= c$.
]

== Notes and further reading <sec:app-notes>

The measure theory used in this book is covered by @rudin1987[Ch. 1–3, 6, 8] and, with more emphasis on
probability, by @dudley2002 and @kallenberg2002; the latter two also treat Polish spaces and regular
conditional distributions in detail. The functional analysis (Hahn–Banach, uniform boundedness, weak
topologies, reflexivity, compact operators and the spectral theorem) is covered by @brezis2011 and, in
German, by @werner2018, which also treats Hilbert–Schmidt and trace-class operators; for operators on
Hilbert spaces see also @conway1990 and @reed1980[Ch. VI]. Bochner integration and Pettis' theorem are
treated in @diestel1977 and @hytonen2016, and Carathéodory functions in @aliprantis2006. Vector-valued
integration and the functional-analytic and convex-analytic background specific to kernel methods are
collected in the appendix of @steinwart2008. For convex analysis see @rockafellar1970 in finite
dimensions and @bauschke2011 in Hilbert spaces; for infinite-dimensional convex analysis (lower
semicontinuity, subdifferentials, the direct method), see @ekeland1976 and @phelps1993; the latter also
studies differentiability of convex functions, which is related to the question of when a subdifferential
is a singleton (@prop:reg-subdifferential-calculus).
