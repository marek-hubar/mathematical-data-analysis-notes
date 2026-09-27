// Shared setup for the lecture notes.
// Every chapter file starts with `#import "/template.typ": *`, which provides the theorem
// environments (theorion), the notation helpers (moremath + the macros below), and cetz for figures.

#import "@preview/theorion:0.6.0": *
#import "@local/moremath:0.1.0": *
#import "@preview/cetz:0.4.2"
#import "@preview/cetz-plot:0.1.3": plot

// ---------------------------------------------------------------------------
// Notation macros (use these instead of ad-hoc spellings; see WRITING_GUIDE.md)
// ---------------------------------------------------------------------------

// Inner product: $ip(f, g)_H$
#let ip(a, b) = $lr(chevron.l #a, #b chevron.r)$
// Risk functionals: $risk(L, P)(f)$, $risk(L, D)(f)$, $risk(L, P, lambda)(f)$
#let risk(..args) = $cal(R)_(#args.pos().join(","))$
// Bayes risk: $bayes(L, P)$ = inf over all measurable f
#let bayes(..args) = $cal(R)^*_(#args.pos().join(","))$
// Measurable functions X -> R, integrable function spaces
#let meas = $cal(L)_0$
// Borel sigma-algebra
#let borel = $cal(B)$
// Expectation, support, span, closure, trace, kernel/range of operators
#let supp = math.op("supp")
#let spn = math.op("span")
#let cl = math.op("cl")
#let tr = math.op("tr")
#let Ker = math.op("ker")
#let Ran = math.op("ran")
#let esssup = math.op("ess sup", limits: true)
#let dom = math.op("dom")
#let id = math.op("id")
// The field of scalars (R or C)
#let KK = math.bb("K")
// Expectation
#let EE = math.bb("E")
// "defined as"
#let defeq = $:=$

// theorion numbers corollaries as sub-items of theorems ("Corollary 3.4.1"). Put them on the shared
// counter instead, like every other theorem-like environment ("Corollary 3.5").
#let (corollary-counter, corollary-box, corollary, show-corollary) = make-frame(
  "corollary",
  theorion-i18n-map.at("corollary"),
  counter: theorem-counter,
  render: render-fn,
)

// Small helper for "Motivation", "Intuition", "Outlook" paragraphs set in a lighter style.
#let intuition(body) = note-block(title: [Intuition], body)
#let context-note(body) = remark-block(title: [Context], body)

// ---------------------------------------------------------------------------
// Partial builds: `typst compile main.typ out.pdf --input only=rkhs` compiles only the
// chapter with that slug. Cross-chapter references to labels from labels.typ are then
// resolved against invisible stubs so that the build still succeeds.
// ---------------------------------------------------------------------------
#let only = sys.inputs.at("only", default: none)

#let appendix-state = state("appendix", false)

#let eq-numbering(n) = context {
  let h = counter(heading).get().first()
  let chap = if appendix-state.get() { numbering("A", h) } else { str(h) }
  "(" + chap + "." + str(n) + ")"
}

#let book(title: none, author: none, body) = {
  set document(title: title, author: author)
  set page(
    paper: "a4",
    margin: (x: 2.8cm, top: 3cm, bottom: 3cm),
    numbering: "1",
    header: context {
      let p = here().page()
      let chapters = query(heading.where(level: 1))
      let current = chapters.filter(h => h.location().page() <= p)
      if current.len() > 0 and not chapters.any(h => h.location().page() == p) {
        let hd = current.last()
        set text(size: 9pt, fill: luma(90))
        if hd.numbering != none [
          #smallcaps[#numbering(hd.numbering, ..counter(heading).at(hd.location()).slice(0, 1)) #hd.body]
        ] else [#smallcaps(hd.body)]
        h(1fr)
        counter(page).display()
        v(-6pt)
        line(length: 100%, stroke: 0.4pt + luma(150))
      }
    },
    footer: context {
      let p = here().page()
      if query(heading.where(level: 1)).any(h => h.location().page() == p) {
        align(center, text(size: 9pt, counter(page).display()))
      }
    },
  )
  set text(font: "New Computer Modern", size: 11pt, lang: "en")
  set par(justify: true, leading: 0.62em, spacing: 1.1em)
  set heading(numbering: "1.1")
  set enum(numbering: "(i)")
  set math.equation(numbering: eq-numbering)
  set figure(numbering: n => context {
    let h = counter(heading).get().first()
    let chap = if appendix-state.get() { numbering("A", h) } else { str(h) }
    chap + "." + str(n)
  })

  // Only equations that carry a label are numbered.
  show math.equation.where(block: true): it => {
    if it.has("label") or it.numbering == none { it } else {
      counter(math.equation).update(v => v - 1)
      math.equation(it.body, block: true, numbering: none)
    }
  }
  // Prevent line breaks inside inline math.
  show math.equation.where(block: false): box
  show link: set text(fill: rgb("#2e5a8a"))
  show ref: set text(fill: rgb("#2e5a8a"))
  // References to chapter headings read "Chapter 3" / "Appendix A" instead of "Section 3".
  show ref: it => {
    let el = it.element
    if el != none and el.func() == heading and el.level == 1 and el.numbering != none {
      let loc = el.location()
      let word = if appendix-state.at(loc) [Appendix] else [Chapter]
      link(loc, [#word~#numbering(el.numbering, ..counter(heading).at(loc).slice(0, 1))])
    } else { it }
  }

  show: show-theorion
  show: show-corollary
  set-inherited-levels(1)

  // Chapters start on a new page with a large heading; per-chapter counters reset.
  show heading.where(level: 1): it => {
    pagebreak(weak: true)
    counter(math.equation).update(0)
    counter(figure.where(kind: image)).update(0)
    counter(figure.where(kind: table)).update(0)
    v(3.5cm)
    set text(size: 22pt, weight: "bold")
    if it.numbering != none {
      block(text(size: 14pt, fill: luma(90))[
        #if appendix-state.get() [Appendix] else [Chapter] #counter(heading).display(it.numbering)
      ])
    }
    block(it.body)
    v(1.5cm)
  }
  show outline.entry.where(level: 1): it => {
    v(0.6em, weak: true)
    strong(it)
  }
  show heading.where(level: 2): set block(above: 2em, below: 1em)
  show heading.where(level: 3): set block(above: 1.6em, below: 0.9em)

  body
}

// Starts the appendix: headings become A, B, ... and theorem numbers A.1, A.2, ...
#let appendix(body) = {
  appendix-state.update(true)
  counter(heading).update(0)
  set heading(numbering: "A.1")
  set-theorion-numbering("A.1")
  body
}
