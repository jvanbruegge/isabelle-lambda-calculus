# Isabelle proving project - Semantics of functional programming languages

In this project I want to start with a simply typed lambda calculus, prove type soundness and then extend it step by step until I am at the [latest version of System F](https://repository.brynmawr.edu/cgi/viewcontent.cgi?article=1014&context=compsci_pubs) used in GHC.

I am using [ott](https://github.com/ott-lang/ott) to generate Isabelle code for the definitions of the systems

## Roadmap

-   [x] Start with a simply typed lambda calculus
    -   [x] Define system
    -   [x] Prove Progress
    -   [x] Prove Preservation
-   [ ] Add let bindings
    -   [x] Extend definition
    -   [x] Prove Progress
    -   [ ] Prove Preservation
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
