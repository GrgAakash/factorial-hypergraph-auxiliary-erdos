# v1 — Factorial-residue hypergraphs and an auxiliary problem of Erdős

**When the manuscript has been fully edited and revised by humans, it will be marked "Final Version".**
This version is not marked final.

- [Read the PDF](factorial_residue_hypergraphs.pdf).
- [TeX source](factorial_residue_hypergraphs.tex).
- [Palomar record: PALOMAR-2026-08-27-000003 v1](https://palomar-registry.org/entry.html?id=PALOMAR-2026-08-27-000003&version=1).

This is the original manuscript underlying the Palomar registration. The
registered Lean declaration covers its quantitative auxiliary theorem,
conditional on the explicit standard dimension-one upper-bound sieve
hypothesis. It does not prove the original prime problem.

The mathematical text of this copy is unchanged from the registered source.
Its AI-disclosure paragraph has been corrected to remove a claim of completed
human verification. The byline, affiliation, and PDF author metadata have
also been removed from this draft copy, as in the expanded [v2](../v2/).
For the exact historical snapshot, see the
[source at registered commit `67b4088`](https://github.com/GrgAakash/factorial-hypergraph-auxiliary-erdos/blob/67b4088fc84422c84f7e5e205552757c3c0c9a71/paper/factorial_residue_hypergraphs.tex).
Moving this copy into `Papers/v1` does not change that pinned record.

## Build the PDF

From this directory, run twice:

```sh
pdflatex -interaction=nonstopmode -halt-on-error factorial_residue_hypergraphs.tex
```
