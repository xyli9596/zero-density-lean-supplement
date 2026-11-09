# Partial Lean formalization: manuscript supplement

This is a source supplement for selected results, not a full formalization of the paper.
Publication-scope alignment: 2026-11-09.
Repository: https://github.com/xyli9596/zero-density-lean-supplement

This repository is intentionally private until the manuscript has appeared on arXiv. Public release is a separate later step.
Coverage snapshot SHA-256: 5f47ff7a69af6a55cb2b610f8157689d34fe9e8d7504cab9b146608ee285e184.
Rechecked against the later source 8131d9037823438b6af40c6164912a27b9ed3ba2a6322ebd7a8498d4867d05f7: all ten complete numbered statements and their assumptions are unchanged.

## Exact scope

Complete machine-checked counterparts, with statement and assumption correspondence reviewed:
- Lemmas 2.1 and 2.2;
- Proposition 3.1;
- Lemmas 3.2, 3.3, 3.4 and 3.6;
- Corollary 3.8;
- Lemmas 4.1 and 4.3.

COVERAGE.csv and COVERAGE.json enumerate all 25 current numbered results, including
all 15 without complete certificates. They provide exact Lean declarations, source
locations, source hashes, and necessary qualifications. The five main Theorems
1.1--1.5 are not fully formalized. Corollary 1.6 now states type < 2a;
Propositions 7.2 and 7.3 are respectively the periodic exception and osculating
hyperplane results. These are the current manuscript numbers.

Lemma 3.4 is a conditional transfer lemma: the phase-plane count law and uniform
inverse-radius asymptotics are its original hypotheses. It does not construct
those inputs. Lemma 3.6 uses two listed endpoints. Lemma 4.1 has an alternative
Cauchy/Gronwall/Jensen proof; the cited Yakovenko theorem is not claimed formalized.
Target : Prop definitions in the legacy sources are not proof certificates.
The formalization need not follow every line of the manuscript's informal proofs.

## Reproduction

Lean: 4.33.0.
Mathlib: db584cd6d46c92f209a44c0f1c829460d327499d.
With the pinned Lean installed, obtain the packages and mathlib cache:

    lake update
    lake exe cache get
    python3 check.py -j 3

Alternatively, set V10_DEPENDENCY_CACHE to a Lake project containing these exact
pinned packages. check.py builds this supplement's own proofs and rejects sorry,
admit, native_decide and additional axioms. V10.Audit checks transitive axiom
usage and accepts only propext, Classical.choice and Quot.sound.

The 462 Lean sources included here are byte-identical to the successful full
kernel build of 2026-11-08, whose source hashes and audit output are in evidence/.
The current-manuscript correspondence was separately reviewed on 2026-11-09.
No new proof was added during this packaging step. No compiled proof objects or
large dependency cache are included. Vendored Ray and Physlib licenses are retained.

## Publication and maintenance

When publishing this supplement, cite one fixed release and its exact commit
hash in the manuscript. Keep that submission snapshot available. The repository
homepage can be linked separately for subsequent work. Later releases should
carry an updated coverage table and a short change log. A moving main branch
alone does not identify the version assessed during review.

formalization-note.tex supplies an optional manuscript paragraph. Insert the
actual fixed-version reference only after the repository or attachment exists.
