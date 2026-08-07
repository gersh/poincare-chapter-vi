# Poincaré Chapter VI in Lean

This repository is a source-faithful reconstruction of the decisive argument in Chapter VI of
volume I of Poincaré's *Les méthodes nouvelles de la mécanique céleste*. It is intentionally
separate from Lean Pool while the historical proof is still research-level mathematics.

The classical planar restricted-three-body theorem is already formalized in
[Lean Pool PR #329](https://github.com/Vilin97/lean-pool/pull/329). This project pins that merge
commit and re-exports its final theorem, while pursuing Poincaré's original route through Fourier
coefficients, complex singularities, Darboux asymptotics, and projective curves.

## Current result

The strongest newly completed component is the finite algebra in §103:

- exact rational spatial Kepler ellipses produce Poincaré's degree-six polynomial;
- Lean derives all 25 coefficients of `50700 · P(x,y,1)` from those ellipses;
- the resulting `64 × 35` Ruppert matrix is constructed in Lean;
- a `35 × 35` inverse modulo 29 is checked by LeanCompCert's kernel-backed
  `verified_decide`;
- the nonzero minor is lifted through Gaussian integers to `ℂ`, proving full column rank;
- Lean expands the bounded-degree polynomial differential expression and proves that its 35
  selected coefficients are exactly the certified minor applied to the coefficient vector;
- every polynomial pair in Ruppert's `(3,4)` and `(4,2)` bidegree boxes is reconstructed from
  that encoding, so the bounded differential equation has only the zero solution;
- the factor-derived solution is normalized by `deg_y(a)/4`; a univariate-in-`y` calculation
  formally verifies cancellation of its top coefficient and the sharp `(4,2)` bound;
- a separate exact determinant proves that no nonzero infinitesimal relative rotation preserves
  the projective curve, even up to scale.

This does **not** yet complete Poincaré's proof. The main remaining obligations are the genuine
complex contour-pinch theorem in §§95–100, exclusion of the squarefree/perfect-power exception
needed to finish Ruppert's irreducibility consequence, and the projective Bézout/local-intersection
argument in §103. The detailed
[research map](docs/PoincareChapterVI.md) distinguishes checked results from open reconstruction.

## Build

The project pins Lean 4.33.0-rc2, Mathlib, LeanCompCert, and the exact Lean Pool merge commit.

```sh
lake update
lake build
python3 research/chapter_vi_section_103_audit.py
lake env lean PoincareChapterVI/AxiomAudit.lean
```

The Python/SymPy audit discovers and independently cross-checks certificates; it is not in the
trusted proof path. The theorem `chapterVIRuppertInverse_mul_minor` recomputes all 1,225 entries
inside Lean's kernel. No `native_decide`, generated axiom, or external computation is used to
prove the rank result.

## Layout

- `PoincareChapterVI/ChapterVI*.lean`: formal reductions corresponding to §§90–103.
- `PoincareChapterVI/Section103/`: ellipse geometry, Ruppert machinery, finite certificate, and
  its exact polynomial-kernel interpretation.
- `PoincareChapterVI/ClassicalLeanPool.lean`: pinned bridge to the already-merged classical result.
- `docs/PoincareChapterVI.md`: passage-by-passage source audit and open mathematical gaps.
- `research/chapter_vi_section_103_audit.py`: exact untrusted research audit.

Released under Apache 2.0.
