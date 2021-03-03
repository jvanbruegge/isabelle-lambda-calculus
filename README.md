# Isabelle proving project - Semantics of functional programming languages

![Build](https://github.com/jvanbruegge/isabelle-lambda-calculus/workflows/Build/badge.svg)

In this project I want to start with a simply typed lambda calculus, prove type soundness and then extend it step by step until I am at the [latest version of System F](https://repository.brynmawr.edu/cgi/viewcontent.cgi?article=1014&context=compsci_pubs) used in GHC.

## Results

You can find the proof of type safety in [Soundness.thy](./Soundness.thy), the proof of confluence in [Confluence.thy](./Confluence.thy) and the determinancy proofs of tying and kinding in [Determinancy.thy](./Determinancy.thy).

## Roadmap

-   [x] Start with a simply typed lambda calculus ([v1.0](https://github.com/jvanbruegge/isabelle-lambda-calculus/tree/v1.0))
-   [x] Add let bindings ([v1.1](https://github.com/jvanbruegge/isabelle-lambda-calculus/tree/v1.0))
-   [x] Use the Nominal2 framework to reason about alpha-equated terms ([v2.0](https://github.com/jvanbruegge/isabelle-lambda-calculus/tree/v2.0))
-   [x] Extend to System F (ie introduce polymorphic variables) ([v3.0](https://github.com/jvanbruegge/isabelle-lambda-calculus/tree/v3.0))
-   [x] Use a context validity judgement ([v3.1](https://github.com/jvanbruegge/isabelle-lambda-calculus/tree/v3.1))
-   [x] Add arbitrary user-defined datatypes ([v3.6](https://github.com/jvanbruegge/isabelle-lambda-calculus/tree/v3.6))
-   [ ] Add `case` expressions
-   [ ] Extend to System Fc (ie introduce type equality coercions)
-   [ ] Extend to System FcPro (ie introduce kind abstractions)

## Used literature

-   [Software Foundations: Programming Language Foundations](https://softwarefoundations.cis.upenn.edu/current/plf-current/toc.html)
-   [System F with type equality coercions](https://www.microsoft.com/en-us/research/wp-content/uploads/2007/01/tldi22-sulzmann-with-appendix.pdf?from=https%3A%2F%2Fresearch.microsoft.com%2Fen-us%2Fum%2Fpeople%2Fsimonpj%2Fpapers%2Fext-f%2Ftldi22-sulzmann-with-appendix.pdf).
-   [Safe zero-cost coercions for Haskell](https://richarde.dev/papers/2016/coercible-jfp/coercible-jfp.pdf)
