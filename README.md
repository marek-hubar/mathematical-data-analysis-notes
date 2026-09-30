# Mathematical Data Analysis — Lecture Notes

Lecture notes for the course *Mathematical Data Analysis* at the Technical University of Munich,
written in [Typst](https://typst.app). The notes cover loss functions, reproducing kernel Hilbert
spaces, and regularized risk minimization, with complete proofs and motivation for each concept.

**📄 [Download the latest PDF](https://github.com/marek-hubar/mathematical-data-analysis-notes/releases/latest/download/mathematical-data-analysis-notes.pdf)**
(rebuilt automatically on every push to `main`).

## Contents

1. The Statistical Learning Problem
2. Loss Functions and Their Risks
3. Reproducing Kernel Hilbert Spaces
4. Integral Operators and Mercer's Theorem
5. Universal Kernels
6. Regularized Risk Minimization
7. Stability of Regularized Solutions

A. Mathematical Background

Readers should know measure-theoretic probability, basic functional analysis (Banach and Hilbert
spaces, bounded operators, $L^p$ spaces) and linear algebra. Everything beyond that is either
developed in the text or collected in Appendix A.

## Building

Requires [Typst](https://github.com/typst/typst#installation). Packages (`theorion`, `cetz`,
`cetz-plot`) are downloaded automatically from Typst Universe.

```sh
typst compile main.typ notes.pdf                     # full book
typst compile main.typ rkhs.pdf --input only=rkhs    # a single chapter
```

Chapter slugs for `--input only=`: `preface`, `learn`, `loss`, `rkhs`, `mercer`, `univ`, `reg`,
`stab`, `app`.

## Repository layout

| Path           | Contents                                              |
| -------------- | ----------------------------------------------------- |
| `main.typ`     | Title page, table of contents, chapter includes       |
| `chapters/`    | One file per chapter                                  |
| `template.typ` | Page layout, theorem environments, notation macros    |
| `labels.typ`   | Registry of labels referenced across chapters         |
| `refs.bib`     | Bibliography                                          |
| `images/`      | Figures                                               |

## Contributing

Found a mistake or an unclear explanation? Please open an issue or a pull request.
