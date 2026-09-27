#import "/template.typ": *

#set heading(numbering: none)
#set figure(numbering: none)

= Preface <sec:preface>

Suppose we are given finitely many examples $(x_1, y_1), dots, (x_N, y_N)$ of inputs together with the
outputs we would like to predict: images and the objects they show, patients' measurements and
diagnoses, or simply points in the plane with real numbers attached to them. We want to find a
function $f$ that predicts the output $y$ of a *new* input $x$ well. This is the basic problem of
supervised learning, and it is the subject of these notes.

Among the many algorithms that attack this problem, a particularly well-understood family consists of the
*regularized kernel methods*. They compute
$ f_(D, lambda) = argmin_(f in H) (1/N sum_(i=1)^N L(x_i, y_i, f(x_i)) + lambda norm(f)_H^2), $
where $L$ is a loss function that measures how bad the prediction $f(x_i)$ is when the truth is $y_i$,
$H$ is a Hilbert space of functions, and $lambda > 0$ trades off the fit to the data against the size of
$f$. Support vector machines and kernel ridge regression are the two best-known members of this
family. The formula looks innocent, but it raises many questions. Why does the first term alone lead to
nonsense? Which Hilbert spaces $H$ make sense? Does a minimizer exist, is it unique, and can we compute
it, given that $H$ is usually infinite-dimensional? How does it depend on $lambda$ and on the data? And
is it any good?

This book answers these questions with complete proofs. The answers use measure-theoretic
probability, functional analysis, convex analysis and approximation theory.
One of the pleasant aspects of the subject is how naturally these fields interact. The central
objects are *reproducing kernel Hilbert spaces*: Hilbert spaces of functions in which evaluating a
function at a point is a continuous operation. They turn out to be exactly the right hypothesis spaces.
They are rich enough to approximate any continuous function, yet structured enough that the infinite-dimensional
optimization problem above collapses to a finite-dimensional one.

== How the book is organized

@sec:learn formalizes the learning problem. It introduces data-generating distributions, loss functions,
risks and the Bayes risk, explains why minimizing the empirical risk over all functions fails, and
motivates regularization in reproducing kernel Hilbert spaces. It ends with the list of guiding
questions that the rest of the book answers.

@sec:loss studies loss functions and the risk functional $f |-> risk(L, P)(f)$ that they induce. We
ask when the risk is measurable, convex, continuous, Lipschitz continuous or differentiable, and we
survey the losses used in practice.

@sec:rkhs, @sec:mercer and @sec:univ develop the theory of reproducing kernel Hilbert spaces.
@sec:rkhs establishes the correspondence between positive definite kernels and such spaces, introduces
feature maps and the kernel trick, and studies the regularity of the functions in the space. @sec:mercer
views the space from the perspective of an integral operator on $L^2$ and proves Mercer's theorem,
which describes the space as a space of "smooth" functions in terms of the eigenvalues of the kernel.
@sec:univ asks when a kernel is *universal*, that is, when its functions can approximate every continuous function.

@sec:reg brings the two threads together. It proves existence and uniqueness of the regularized
minimizers and derives the representer theorems, which describe the minimizers explicitly. Along the way
it introduces the subdifferential calculus needed for non-smooth losses such as the hinge loss of support
vector machines. @sec:stab studies how the minimizer depends on the regularization parameter and on
the underlying distribution. It closes by combining this stability with a law of large numbers in the
Hilbert space. This proves that, for convex Lipschitz losses and a suitable choice of $lambda = lambda_N$,
the risk of $f_(D, lambda)$ converges to the smallest risk attainable in $H$, and, for universal
kernels, to the Bayes risk.

@sec:app collects the background from measure theory, functional analysis and convex analysis that is
used throughout. Readers can consult it as needed. The dependencies between the chapters are shown
below; the two branches after @sec:learn can be read in either order.

#figure(
  cetz.canvas(length: 1cm, {
    import cetz.draw: *
    let node(pos, name, body) = {
      rect(
        (pos.at(0) - 1.55, pos.at(1) - 0.42),
        (pos.at(0) + 1.55, pos.at(1) + 0.42),
        radius: 0.12,
        stroke: 0.6pt + luma(80),
        fill: luma(245),
        name: name,
      )
      content(pos, text(size: 9pt, body))
    }
    node((4.5, 4), "c1", [1 #h(0.3em) Learning problem])
    node((1.2, 2.6), "c2", [2 #h(0.3em) Loss functions])
    node((6.5, 2.6), "c3", [3 #h(0.3em) RKHS])
    node((5.6, 1.2), "c4", [4 #h(0.3em) Mercer])
    node((9, 1.2), "c5", [5 #h(0.3em) Universal kernels])
    node((1.2, 0.9), "c6", [6 #h(0.3em) Regularization])
    node((1.2, -0.5), "c7", [7 #h(0.3em) Stability])
    set-style(mark: (end: ">", fill: luma(60), scale: 0.8), stroke: 0.6pt + luma(60))
    line("c1.south", "c2.north")
    line("c1.south", "c3.north")
    line("c3.south", "c4.north")
    line("c3.south", "c5.north")
    line("c2.south", "c6.north")
    line("c3.south-west", "c6.north-east")
    line("c6.south", "c7.north")
    set-style(stroke: (dash: "dashed", paint: luma(120), thickness: 0.6pt))
    line("c5.south", "c7.east")
  }),
  caption: [Dependencies between the chapters. The dashed arrow indicates that universality is only
    needed for the consistency results at the end of @sec:stab.],
) <fig:preface-dependencies>

== Prerequisites

We assume familiarity with measure-theoretic probability: σ-algebras, measures, integrals, the
convergence theorems, product measures and Fubini–Tonelli, and $L^p$ spaces. We also assume basic
functional analysis: Banach and Hilbert spaces, bounded linear operators, dual spaces, orthonormal bases,
and the Riesz representation theorem. More specialized results, such as the Bochner integral, compact and Hilbert–Schmidt
operators, the spectral theorem, weak compactness and the Stone–Weierstrass theorem, are stated in
@sec:app with proofs or precise references.

== Conventions

Results are numbered consecutively within each chapter: Definition 3.4 is followed by Theorem 3.5.
Only equations that are referred to later carry numbers. Blocks labelled _Intuition_ give informal
explanations; they are never a substitute for the proofs, which are always given in full or referenced
precisely. Blocks labelled _Context_ place the material in the wider landscape of statistics, machine
learning and analysis, and can be skipped without loss of continuity.

The most important notation is summarized in the following table. It is introduced properly when it first
appears.

#figure(
  table(
    columns: (auto, 1fr),
    align: (left, left),
    stroke: (x, y) => (top: if y == 0 { 0.8pt } else if y == 1 { 0.5pt } else { 0pt }, bottom: 0.8pt * int(y == 17)),
    inset: (x: 6pt, y: 4pt),
    table.header([*Symbol*], [*Meaning*]),
    [$(X, cal(A))$, $Y subset.eq RR$], [input space (a measurable space), closed output space],
    [$P$, $P_X$, $P(dot | x)$], [distribution on $X times Y$, its marginal on $X$, conditional distribution of $y$ given $x$],
    [$D = ((x_i, y_i))_(i=1)^N$], [data set; also the empirical measure $1/N sum_i delta_((x_i, y_i))$],
    [$L(x, y, t)$], [loss function, $L: X times Y times RR -> [0, oo)$],
    [$risk(L, P)(f)$, $risk(L, D)(f)$], [risk and empirical risk of a measurable $f: X -> RR$],
    [$bayes(L, P)$, $f^*_(L, P)$], [Bayes risk and Bayes decision function],
    [$meas(X)$], [measurable functions $X -> RR$],
    [$KK$], [the scalar field $RR$ or $CC$],
    [$H$, $H_K$], [a reproducing kernel Hilbert space; the one with kernel $K$],
    [$K$, $K_x = K(dot, x)$], [kernel and kernel section, $f(x) = ip(f, K_x)_H$],
    [$Phi$], [feature map, $K(x, x') = ip(Phi(x'), Phi(x))$; canonical $Phi(x) = K_x$],
    [$abs(K)_oo$], [$sup_(x in X) sqrt(K(x, x))$],
    [$S_K$, $T_K$, $(lambda_j, e_j)$], [integral operators of $K$ and the eigenpairs of $T_K$],
    [$risk(L, P, lambda)(f)$], [regularized risk $risk(L, P)(f) + lambda norm(f)_H^2$],
    [$f_(P, lambda)$, $f_(D, lambda)$], [minimizers of the regularized (empirical) risk],
    [$A(lambda)$], [approximation error function],
    [$E'$, $A'$, $A^*$], [dual space, Banach space adjoint, Hilbert space adjoint],
  ),
  kind: table,
  caption: [Frequently used notation.],
) <tab:preface-notation>

== About these notes

These notes grew out of the lecture _Mathematical Data Analysis_ at the Technical University of Munich.
They follow the structure of the lecture, but they fill in the arguments that were only
sketched there, correct the mistakes of the original lecture notes, and add examples, motivation and
context. The presentation of loss functions, reproducing kernel Hilbert spaces and regularized risk
minimization owes a great deal to the monograph of Steinwart and Christmann @steinwart2008. It is the
natural next step for readers who want to go deeper, in particular into the statistical analysis of
support vector machines (learning rates, oracle inequalities, concentration inequalities), of which the
final section of these notes gives only a first taste.
