# Isabelle proving project - Semantics of functional programming languages

In this project I want to start with a simply typed lambda calculus, prove type soundness and then extend it step by step until I am at the [latest version of System F](https://repository.brynmawr.edu/cgi/viewcontent.cgi?article=1014&context=compsci_pubs) used in GHC.

I am using [ott](https://github.com/ott-lang/ott) to generate Isabelle code for the definitions of the systems

## Roadmap

-   [ ] Start with a simply typed lambda calculus with the help of
    -   [x] Define system
    -   [x] Prove Progress
    -   [ ] Prove Preservation
-   [ ] Extend calculus with datatypes and `case` expressions
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
