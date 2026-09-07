# v2 — Factorial-residue hypergraphs and covering congruences

**When the manuscript has been fully edited and revised by humans, it will be marked "Final Version".**
This version is a working draft, not a final version.
Last updated: 7 September 2026.

- [Read the PDF](factorial_residue_covers_expanded.pdf).
- [TeX source](factorial_residue_covers_expanded.tex).
- [Finite examples, checkers, and recorded results](verification/).

The draft has no author byline. Its acknowledgments and AI disclosure are
retained; the repository README records the project's provenance.

The registered Lean formalization covers the original quantitative
auxiliary theorem, conditional on the explicitly stated standard
dimension-one upper-bound sieve theorem. The additional results in this
expanded draft, including the stronger counting bound in prescribed
progressions, are not covered by that registration and require separate
mathematical review. No new Lean verification is claimed for this draft.
The completed machine checks of the registered formalization remain a
separate record and do not cover these additional results.

The original manuscript is available in [`v1`](../v1/).
The registered source commit remains unchanged.

## Build the PDF

From this directory, run twice:

```sh
pdflatex -interaction=nonstopmode -halt-on-error factorial_residue_covers_expanded.tex
```

The source uses standard AMS LaTeX packages, microtype, hyperref, and booktabs.

## Replay the finite checks

From this directory:

```sh
cd verification
python3 verify_extensions.py --output replay_extensions.json
python3 verify_resultants_and_covers.py --certificates certificates --output replay_resultants.json
```

The checkers use Python 3.10 or later; the second also requires SymPy.
The committed JSON reports are previously recorded finite computations.
They do not replace mathematical proofs or establish an asymptotic theorem.
