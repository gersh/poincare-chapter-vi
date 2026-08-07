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
- an explicit Bézout identity after specialization to `ZMod 17` proves that the quartic is
  squarefree over `ℂ(x)`; this excludes the repeated-factor exception and proves that the exact
  affine polynomial is irreducible over `ℂ`;
- the affine certificate is transferred to the exact homogeneous sextic: homogeneous factors are
  recovered through a scaling-variable argument, and the nonzero `x⁴y²` coefficient rules out a
  factor hidden on the line `z = 0`, proving projective irreducibility over `ℂ`;
- the cleared degree-seven reduced curve is formalized, proved homogeneous, and proved to share no
  component with the sextic by an exact restriction to the line `x = 0`;
- a sparse `ℚ[i]` evaluator, checked through LeanCompCert and proved correct with respect to
  `MvPolynomial`, derives every coefficient of that septic directly from Poincaré's reduced
  source formula and the physical cubic vectors;
- the affine-origin tangent cone and tangent line are derived from the source curves and proved
  transverse; both points at infinity are placed in explicit affine charts with initial degrees
  `(2,3)`; LeanCompCert checks the corresponding sparse Sylvester determinants, and a
  coefficientwise sound jet implementation linked to Mathlib's verified Bird determinant proves
  that the genuine polynomial resultants have trailing degree exactly eight; the certificates are
  then mapped into `ℂ` and identified with the exact iterated-polynomial forms of the two
  dehomogenized projective chart pairs;
- local intersection multiplicity is defined intrinsically as the module length of the quotient
  by the two curve equations in the plane's local ring, with named specializations for the affine
  origin and both points at infinity; the affine-origin length is proved to be two, and the
  eight-dimensional triangular quotient model needed at infinity is constructed explicitly;
- a separate exact determinant proves that no nonzero infinitesimal relative rotation preserves
  the projective curve, even up to scale.

This does **not** yet complete Poincaré's proof. The main remaining obligations are the genuine
complex contour-pinch theorem in §§95–100 and the geometric local-intersection/projective-Bézout
bridge in §103. The finite determinant/resultant correctness gap is now closed. The detailed
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
  its exact polynomial-kernel, irreducibility, resultant, and local-algebra consequences.  The
  infinity-chart standard basis is represented by an explicit eight-dimensional algebra with
  basis `1, z, z^2, z^3, z^4, z^5, y, yz`.
- `PoincareChapterVI/ClassicalLeanPool.lean`: pinned bridge to the already-merged classical result.
- `docs/PoincareChapterVI.md`: passage-by-passage source audit and open mathematical gaps.
- `research/chapter_vi_section_103_audit.py`: exact untrusted research audit.

Released under Apache 2.0.
