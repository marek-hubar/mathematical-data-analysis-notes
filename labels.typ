// Registry of labels that may be referenced ACROSS chapters.
//
// Rules (see WRITING_GUIDE.md):
// - Each chapter MUST define every label listed under its slug (exactly once).
// - A chapter may reference labels of OTHER chapters only if they are listed here.
// - Chapter-internal labels are free, but must contain the chapter slug,
//   e.g. <prop:rkhs-sum-of-kernels>, <eq:reg-krr-system>.
//
// In partial builds (`--input only=<slug>`), main.typ emits invisible stubs for the
// labels of all other chapters, so cross-references still compile.

#let registry = (
  learn: (
    "sec:learn",                      // Chapter 1 heading
    "sec:learn-overfitting",          // section on overfitting / why restrict the hypothesis class
    "sec:learn-roadmap",              // section listing the guiding questions (Q1-Q8) and the plan of the book
    "sec:learn-remedies",             // section: restriction and regularization; error decompositions
    "eq:learn-error-decomposition",   // excess risk = estimation error + approximation error
    "lem:learn-regular-conditional",  // existence of regular conditional probabilities P(.|x)
    "def:learn-loss",                 // (supervised / unsupervised) loss function
    "def:learn-risk",                 // L-risk R_{L,P}
    "def:learn-empirical-risk",       // empirical measure D and empirical risk R_{L,D}
    "def:learn-bayes",                // Bayes risk R*_{L,P} and Bayes decision function f*_{L,P}
    "def:learn-inner-risk",           // inner risk C_{L,P}(x, t)
    "lem:learn-inner-risk",           // pointwise minimization of the inner risk
    "def:learn-consistency",          // learning method; (universal) consistency
    "ex:learn-least-squares",         // least squares: Bayes function = conditional mean
    "eq:learn-ls-decomposition",      // R(f) = ||f - f_P||^2_{L2(P_X)} + sigma_P^2
    "ex:learn-classification",        // binary classification loss, Bayes classifier
    "ex:learn-density-level",         // density level detection (unsupervised)
  ),
  loss: (
    "sec:loss",
    "def:loss-dominates-pointwise",   // metric dominating pointwise convergence
    "prop:loss-measurability",        // (f,x) -> f(x) and f -> R(f) measurable
    "def:loss-convex-continuous",     // convex / strictly convex / continuous loss
    "prop:loss-convex-risk",          // L convex => R_{L,P} convex
    "prop:loss-lsc",                  // continuous L => R lower semicontinuous under conv. in probability
    "def:loss-nemitski",              // (P-integrable) Nemitski loss, of order p
    "prop:loss-risk-continuity",      // continuity of R on L^inf and L^p (with full proof)
    "def:loss-lipschitz",             // (locally) Lipschitz loss, |L|_{r,1}, |L|_1
    "prop:loss-lipschitz-risk",       // |R(f)-R(g)| <= |L|_{B,1} ||f-g||_{L1}
    "def:loss-frechet",               // Frechet differentiability
    "prop:loss-frechet",              // R Frechet differentiable on L^inf, formula for derivative
    "def:loss-distance",              // distance-based loss psi(y-t)
    "def:loss-margin",                // margin-based loss phi(yt)
    "prop:loss-margin-properties",    // properties of margin-based losses
    "def:loss-growth",                // p-upper/lower bounded, growth type p
    "prop:loss-distance-risk-bounds", // bounds on R_{L,P} for distance-based losses in terms of |P|_p
    "ex:loss-catalogue",              // catalogue of standard losses (least squares, hinge, logistic, L_p, Huber, eps-insensitive, pinball ...)
  ),
  rkhs: (
    "sec:rkhs",
    "prop:rkhs-sobolev",              // warm-up: Sobolev-type space on [0,1] with kernel min(x, y)
    "def:rkhs",                       // RKHS: point evaluations continuous
    "def:rkhs-kernel",                // reproducing kernel, K_x = K(., x), reproducing property
    "eq:rkhs-reproducing",            // f(x) = <f, K_x>
    "def:rkhs-pd",                    // positive definite kernel (and strictly positive definite)
    "prop:rkhs-kernel-properties",    // K(x,x')=<K_x',K_x>, Hermitian, |K|^2 <= K K, pd, uniqueness
    "prop:rkhs-norm-convergence",     // norm convergence => pointwise / locally uniform convergence
    "thm:rkhs-completion",            // RKHS completion of a pre-RKHS
    "thm:rkhs-moore-aronszajn",       // every pd kernel has a unique RKHS; 1-1 correspondence
    "def:rkhs-feature-map",           // feature map / feature space, canonical feature map Phi_K
    "prop:rkhs-feature-representation", // H_K = { <w, Phi(.)>_H : w in H }, with norm formula
    "ex:rkhs-kernels",                // examples: linear, polynomial, orthonormal-series kernels
    "prop:rkhs-sum-restriction",      // sums of kernels, closed subspaces, restrictions
    "prop:rkhs-measurable",           // all f in H_K measurable iff K(., y) measurable
    "prop:rkhs-bounded",              // H_K subset l^inf(X) iff K bounded; ||f||_inf <= |K|_inf ||f||_H
    "def:rkhs-kernel-norms",          // |K|_p and |K|_inf := sup_x sqrt(K(x,x))
    "prop:rkhs-continuous",           // K bounded and separately continuous iff H_K subset C_b(X)
    "prop:rkhs-continuity-equivalences", // K continuous <=> ... <=> Phi continuous
    "prop:rkhs-compact-embedding",    // Phi(X) compact => H_K -> l^inf compact
    "prop:rkhs-separable",            // X separable, K continuous => H_K separable
    "cor:rkhs-onb-expansion",         // uniformly convergent ONB expansion of K(., x)
    "prop:rkhs-strict-pd",            // invertible Gram matrix <=> independence of K_(x_i) <=> interpolation
    "prop:rkhs-kernel-operations",    // sums, limits, products, g K g-bar, pullbacks, power series of kernels
    "prop:rkhs-series",               // series kernels sum w_k e_k(x) conj(e_k(x')) and their RKHS
    "lem:rkhs-kernel-metric",         // kernel pseudometric d_Phi via K; f is ||f||-Lipschitz w.r.t. d_Phi
    "ex:rkhs-gaussian",               // Gaussian kernel is positive definite
  ),
  mercer: (
    "sec:mercer",
    "thm:mercer-lp-embedding",        // H_K -> L^p(mu) continuous, adjoint, density criteria
    "thm:mercer-integral-operator",   // S_K Hilbert-Schmidt, T_K = S_K^* S_K compact positive self-adjoint trace class
    "thm:mercer",                     // Mercer's theorem
    "prop:mercer-rkhs-spectral",      // H_K = { sum a_j sqrt(lambda_j) e_j }, T_K^{1/2} isometric iso
    "ex:mercer-torus",                // translation-invariant kernels on the torus, trigonometric polynomials
    "ex:mercer-sphere",               // zonal kernels on the sphere, spherical harmonics
  ),
  univ: (
    "sec:univ",
    "def:univ-universal",             // universal kernel; separation of sets
    "prop:univ-separation",           // universal => separates disjoint compact sets
    "prop:univ-properties",           // injective feature maps, K(x,x)>0, restrictions, normalization
    "thm:univ-criterion",             // Stone-Weierstrass criterion via feature map into l^2
    "ex:univ-taylor",                 // Taylor kernels: exponential, Gaussian, binomial are universal
    "ex:univ-fourier",                // Fourier-type kernels on the torus are universal
    "thm:univ-bayes",                 // universal kernel + continuous P-integrable Nemitski loss => inf_H R = Bayes risk
    "lem:univ-continuous-dense",      // C(X) dense in L^p(mu) for finite Borel mu on compact metric X
  ),
  reg: (
    "sec:reg",
    "def:reg-regularized-risk",       // R_{L,P,lambda}, R_{L,D,lambda}, minimizers f_{P,lambda}, f_{D,lambda}
    "def:reg-kernel-mean",            // kernel mean E_Q[h Phi] (weak/Riesz definition)
    "lem:reg-kernel-mean",            // properties of the kernel mean
    "sec:reg-questions",              // section stating Q1-Q8 (or recalling them)
    "prop:reg-norm-bound",            // ||f_{P,lambda}||_H <= sqrt(R(0)/lambda)
    "prop:reg-uniqueness",            // at most one minimizer for convex L
    "thm:reg-existence",              // existence of f_{P,lambda}
    "thm:reg-representer",            // representer theorem for f_{D,lambda}
    "prop:reg-nonzero",               // f_{P,lambda} != 0 under inf_H R < R(0)
    "eq:reg-integral-equation",       // f_{P,lambda} = -1/(2 lambda) E_P[L'(x,y,f(x)) Phi(x)]
    "ex:reg-krr",                     // kernel ridge regression: (K + lambda N I) a = y
    "def:reg-subdifferential",        // subdifferential
    "prop:reg-subdifferential-calculus", // sum rule, chain rule, optimality 0 in df, Gateaux, monotone
    "prop:reg-subdifferential-integral", // subdifferential of integral functional on L^p
    "thm:reg-general-representer",    // f_{P,lambda} = -1/(2 lambda) E_P[h Phi], h in dL
  ),
  stab: (
    "sec:stab",
    "def:stab-approx-error",          // approximation error function A(lambda)
    "prop:stab-approx-error",         // properties of A
    "prop:stab-min-norm",             // unique minimal-norm minimizer f_{P,H}
    "thm:stab-lambda",                // continuity of lambda -> f_{P,lambda}
    "cor:stab-equivalences",          // minimizer exists <=> ||f_lambda|| bounded <=> A(lambda) <= c lambda
    "thm:stab-measure",               // ||f_{P,lambda} - f_{Pbar,lambda}|| <= 1/lambda ||E_P h Phi - E_Pbar h Phi||
    "ex:stab-spectral",               // least squares with a series kernel: explicit f_{P,lambda}, A(lambda)
    "sec:stab-outlook",               // outlook: from stability to consistency
  ),
  app: (
    "sec:app",
    "thm:app-caratheodory",           // Caratheodory functions on X x Z (Z Polish) are jointly measurable
    "thm:app-convergence",            // Fatou, dominated convergence, subsequence a.s. convergence
    "thm:app-fubini",                 // Fubini-Tonelli
    "sec:app-lp",                     // L^p spaces, duality L^p' = (L^p)', non-normability for p < 1
    "thm:app-holder",                 // Hoelder inequality
    "thm:app-lp-duality",             // (L^p)' = L^p' for 1 <= p < oo, sigma-finite
    "def:app-bochner",                // Bochner integral and commuting with bounded operators
    "thm:app-bochner-properties",     // properties of the Bochner integral (Pettis, commuting with operators, DCT)
    "prop:app-bochner-feature-map",   // Bochner integrals of g Phi in an RKHS
    "thm:app-riesz",                  // Riesz representation theorem in Hilbert spaces
    "thm:app-projection",             // projection theorem, orthogonal complements, polarization identity
    "thm:app-uniform-boundedness",    // uniform boundedness principle
    "thm:app-hahn-banach",            // Hahn-Banach
    "prop:app-adjoint-kernel-range",  // ker A* = (ran A)^perp etc.
    "def:app-compact-operators",      // compact, Hilbert-Schmidt, trace-class operators, Schauder
    "thm:app-operator-facts",         // facts on compact, Hilbert-Schmidt and trace-class operators
    "prop:app-integral-operators",    // integral operators with L^2 kernels are Hilbert-Schmidt
    "thm:app-spectral",               // spectral theorem for compact self-adjoint operators
    "thm:app-weak-compactness",       // bounded sequences in Hilbert spaces have weakly convergent subsequences; lsc of norm
    "thm:app-radon-riesz",            // weak convergence + convergence of norms => norm convergence (Hilbert space)
    "lem:app-sup-affine",             // pointwise sup of affine functions is convex and lsc; concave inf of affine
    "lem:app-existence-minimizer",    // convex lsc functional with bounded nonempty sublevel set on reflexive space attains min
    "thm:app-mazur",                  // Mazur: convex closed sets are weakly closed
    "lem:app-convex-lipschitz",       // convex functions on R are locally Lipschitz, |f|_{[-t,t]}|_1 <= 2/t ||f|_{[-2t,2t]}||_inf
    "lem:app-three-slopes",           // three-slopes inequality for convex functions on R
    "thm:app-stone-weierstrass",      // Stone-Weierstrass (real and complex)
    "thm:app-arzela-ascoli",          // Arzela-Ascoli
    "thm:app-dini",                   // Dini's theorem
    "thm:app-tietze",                 // Tietze extension theorem
  ),
)

// Invisible targets for labels of chapters that are not part of a partial build.
#let stubs(included) = {
  hide(block(height: 0pt, {
    for (slug, labels) in registry {
      if slug == included { continue }
      for l in labels {
        if l.starts-with("eq:") [
          #math.equation(block: true, numbering: "(1)", $0$) #label(l)
        ] else [
          #figure(kind: "stub", supplement: [Stub], numbering: "1", []) #label(l)
        ]
      }
    }
  }))
}
