# Isabelle proving project - Semantics of functional programming languages

![Build](https://github.com/jvanbruegge/isabelle-lambda-calculus/workflows/Build/badge.svg)

In this project I want to start with a simply typed lambda calculus, prove type soundness and then extend it step by step until I am at the [latest version of System F](https://repository.brynmawr.edu/cgi/viewcontent.cgi?article=1014&context=compsci_pubs) used in GHC.

## Roadmap

-   [x] Start with a simply typed lambda calculus
    -   [x] Define system
    -   [x] Prove Progress
    -   [x] Prove Preservation
-   [x] Add let bindings
    -   [x] Extend definition
    -   [x] Prove Progress
    -   [x] Prove Preservation
-   [x] Use the Nominal2 framework to reason about alpha-equated terms
-   [ ] Add datatypes and `case` expressions
    -   [ ] Extend definition
    -   [ ] Prove Progress
    -   [ ] Prove Preservation
-   [ ] Extend to System F (ie introduce polymorphic variables)
    -   [ ] Extend definition
    -   [ ] Prove Progress
    -   [ ] Prove Preservation
-   [ ] Extend System F with Coercions
    -   [ ] Extend definition
    -   [ ] Prove Progress
    -   [ ] Prove Preservation
-   [ ] TBD

## Used literature

Up until now, I mainly used [Software Foundations: Programming Language Foundations](https://softwarefoundations.cis.upenn.edu/current/plf-current/toc.html).
