#import "/template.typ": *
#import "/labels.typ": registry, stubs

#show: book.with(
  title: "Mathematical Data Analysis",
  author: "Marek Hubař",
)

// ---------------------------------------------------------------------------
// Title page
// ---------------------------------------------------------------------------
#set page(numbering: "i")
#if only == none {
  page(numbering: none, header: none, footer: none, {
    v(1fr)
    align(center)[
      #text(size: 30pt, weight: "bold")[Mathematical Data Analysis]
      #v(0.8em)
      #text(size: 15pt)[Loss Functions, Reproducing Kernel Hilbert Spaces, \ and Regularized Risk Minimization]
      #v(3em)
      #text(size: 12pt)[Lecture notes based on the course _Mathematical Data Analysis_ \ Technical University of Munich]
      #v(1.5em)
      #text(size: 12pt)[Marek Hubař]
    ]
    v(2fr)
  })

  counter(page).update(1)
  outline(depth: 2, indent: auto)
}
#set page(numbering: "1")
#counter(page).update(1)

// ---------------------------------------------------------------------------
// Chapters. Slugs must match labels.typ; `--input only=<slug>` builds a single chapter.
// ---------------------------------------------------------------------------
#let chapters = (
  ("preface", "/chapters/00-preface.typ"),
  ("learn", "/chapters/01-learning-problem.typ"),
  ("loss", "/chapters/02-loss-functions.typ"),
  ("rkhs", "/chapters/03-rkhs.typ"),
  ("mercer", "/chapters/04-mercer.typ"),
  ("univ", "/chapters/05-universal-kernels.typ"),
  ("reg", "/chapters/06-regularization.typ"),
  ("stab", "/chapters/07-stability.typ"),
)

#for (i, (slug, path)) in chapters.enumerate() {
  if only == none { include path } else if only == slug {
    // Keep the real chapter number in partial builds (the preface is unnumbered).
    counter(heading).update(calc.max(i - 1, 0))
    include path
  }
}

#show: appendix
#if only == none or only == "app" { include "/chapters/A-background.typ" }

#bibliography("/refs.bib", title: [Bibliography], style: "ieee")
#if only != none { stubs(only) }
