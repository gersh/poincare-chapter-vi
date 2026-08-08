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
  origin and both points at infinity; the affine-origin length is proved to be two; exact sparse
  normal-form certificates identify both infinity-chart ideals with their triangular local-model
  ideals after localization; and both intrinsic infinity multiplicities are proved to be eight
  using an explicit eight-step composition series;
- a separate exact determinant proves that no nonzero infinitesimal relative rotation preserves
  the projective curve, even up to scale.
- an exact bidirectional affine-elimination certificate identifies the common-zero ideal with
  `x + h(y), y² q(y)`; a mod-53 coefficient-list Bézout certificate proves that the degree-24
  residual polynomial `q` is separable, and Lean concludes that the origin plus exactly 24
  distinct non-origin points are all affine intersections of the source sextic and septic;
- the three source-level infinitesimal rotation sextics are reduced in the radical coordinate
  algebra of those 24 points; their degree-at-most-23 univariate remainders have a nonsingular
  three-coefficient minor, certified by an inverse modulo 53, so Lean proves that a rotation whose
  derivative vanishes at all 24 points must be zero. A separate LeanCompCert check identifies the
  cleared sextics with the finite convolution derived from the physical ellipse rotations;
- Poincaré's §103 chain-rule step is now formalized: a persistent singular zero with fixed
  singular value, stationary in the ellipse parameter, has zero derivative in the varying
  orbital parameter. An explicit rational Cayley family gives genuine complex-orthogonal
  rotations of the second ellipse; Lean differentiates its axes, cubic coordinate vector, and
  squared-distance sextic, and proves that the result is exactly the source polynomial used by
  the finite certificate. A rank-nullity theorem then joins this statement to the finite certificate:
  a three-parameter rotation family whose singular values factor locally through two essential
  coordinates is impossible once every kernel direction supplies the stated persistent
  singular deformation.
- the formerly assumed local singular branch is now constructed by Mathlib's complex
  implicit-function theorem from the coupled equations `(Δ, ∂Δ/∂t) = (0,0)`. Lean proves that
  both equations persist, computes the branch derivative, and derives `dz/dγ₃ = 0` from
  first-order stationarity of Poincaré's singular value. An explicit inverse proves that the
  fiber Jacobian is invertible as soon as `∂Δ/∂z ≠ 0` and `∂²Δ/∂t² ≠ 0`. The resulting branch is
  packaged directly into the physical §103 endgame, rather than supplied as an arbitrary
  persistence hypothesis.
- the existing shape-basis and separability certificates are now differentiated to prove that
  the exact affine sextic and reduced septic meet transversely at all 24 finite non-origin
  points. Lean constructs an explicit inverse for each two-gradient Jacobian, giving an
  IFT-ready nondegeneracy theorem for the algebraic `(x,y)` curve pair without a new certificate.
- a second LeanCompCert coefficient-cube certificate now proves directly that
  `50700 · ∑ᵢ Uᵢ²` is the certified projective sextic. After dehomogenization, Lean joins
  this with the reduced-septic certificate and Poincaré's differentiation identity. It proves
  that at each of the 24 finite points the sextic derivative vanishes in his explicit
  polynomial constant-`z` direction.
- Poincaré's displayed transcendental singularity parameter is differentiated in Lean. Its
  logarithmic differential is proved to annihilate that same polynomial direction, and local
  constancy along a differentiable path is proved as a sufficient, but stronger, hypothesis for
  the exact first-order `dz = 0` covector equation used in §103.
- the moving sextic and reduced septic are constructed directly from the genuine Cayley rotation
  family. Their joint analyticity is proved, their base Jacobian is identified with the certified
  transverse `(P,R)` Jacobian, and the complex implicit-function theorem constructs a branch
  through each of the 24 points. Their root derivatives are assembled into one canonical linear
  map from the three rotation parameters. If §102 supplies Poincaré's asserted rank-at-most-two
  bound for this map, Lean finds a nonzero stationary direction, derives equation (2), invokes
  the compiled LeanCompCert restriction certificate, and obtains a contradiction.
- Poincaré's omitted coefficient-recovery step on p. 326 is now a theorem: if `Dₙ` has an
  isolated Darboux leading term `λⁿ E₁/(n+1)`, then `Dₙ₊₁/Dₙ → λ`. Thus the coefficient sequence
  uniquely determines the inverse singularity even when its leading coefficient varies. A
  two-essential-coordinate factorization of the isolated coefficient sequences now implies the
  canonical root-differential rank bound and contradicts the compiled §103 calculation.
- equally dominant singularities no longer require a convergent consecutive-coefficient ratio.
  For a normalized leading spectrum `∑ⱼ Eⱼ λⱼⁿ`, Lean constructs the annihilator
  `∏ⱼ (X-λⱼ)`, proves its recurrence, and uses Vandermonde invertibility to recover the complete
  unit-circle spectrum from coefficients modulo `o(1)`. Continuity prevents local permutation of
  the recovered roots, yielding the same compiled §103 contradiction.
- for a finite sum of constant leading boundary logarithms, equality of analytic germs now gives
  the exact Taylor-coefficient decomposition. A remainder analytic on a strictly larger disk is
  proved to vanish after `(n+1)R^(n+1)` normalization. The common radius `R` remains explicit,
  and this source-facing data now feeds the finite-spectrum and compiled §103 contradiction.
- multiplication by any positive power of the vanishing factor `1-z/z₀` is proved to preserve
  normalized decay. Consequently every finite Taylor jet of Poincaré's analytic logarithmic
  amplitude contributes the same leading spectrum as its value at `z₀`; all higher jet terms are
  formally subleading.
- Tannery's dominated-convergence theorem now extends the same conclusion to a full infinite
  analytic-amplitude series, provided its normalized positive-order terms admit a summable bound
  uniform in all sufficiently large coefficient indices. This hypothesis is exposed in the
  source-facing §102 interface rather than silently replacing the analytic amplitude by a
  polynomial.
- a second, source-faithful route writes `G(z)=G(z₀)+(1-z/z₀)H(z)`. Lean proves the exact
  first-vanishing logarithmic coefficients, an `ℓ¹ * c₀` weighted convolution theorem, and the
  required first-moment summability from analyticity of `H` on a disk larger than the boundary
  circle. Mathlib's holomorphic divided difference now constructs `H` and its scalar power series
  automatically whenever `G` is analytic beyond `z₀`. Thus this route no longer postulates either
  a Tannery majorant or the removable factorization separately.
- scalar analytic germs now have a proved Cauchy-product coefficient rule. Consequently a
  function-level finite sum of actual varying amplitudes times logarithms, plus an analytic
  remainder, determines all coefficients by analytic-germ uniqueness and feeds §102 directly.
- the prepared real symmetric pinch is stable under a nonconstant analytic unit: for every
  continuous Lipschitz amplitude, Lean extracts its value at the collision, uniformly bounds the
  varying-amplitude integral, and proves that the integral divided by `-log k` converges to that
  value. A stronger parameter-dependent theorem works in any complete real normed space, hence
  for complex amplitudes, and allows the center value to vary while converging at the pinch. The
  moving-center theorem exactly transports the affine local cycle
  `[h(k)-L,h(k)+L]` to the symmetric model and identifies the leading coefficient with the
  amplitude at that moving center. The
  prepared-factor module also constructs a compatible holomorphic complex square-root product and
  inverse whenever the quadratic and unit factors remain in a common slit-plane chart. It works
  on a joint parameter-contour domain such as `ℂ × ℂ`; continuity automatically constructs an open
  common chart from slit-plane values along the whole cycle family. The still-open transport is
  verifying those values for Poincaré's actual moving cycle and carrying that cycle to the
  controlled symmetric model. The non-affine transport theorem itself is now formalized: a
  relative `C²` path homotopy inside the branch chart preserves the prepared inverse-square-root
  contour integral, with closedness of the holomorphic one-form proved automatically.

This does **not** yet complete Poincaré's proof. The main remaining obligations are the genuine
complex contour-pinch theorem in §§95–100 and the source-specific analytic input in §102. The
concrete moving algebraic branches, physical derivative identification, formal chain rule,
identification of the reduced curve with the constant-`z` tangent derivative, and the
three-versus-two rank contradiction are now established. What remains in §§102–103 is to derive
the finite boundary-logarithm germ decomposition from Poincaré's actual contour integral,
including the function-level logarithmic decomposition and larger-disk analyticity for its
varying analytic amplitudes, and
to derive the coefficient family and common radius from the Chapter V uniform-integral relation.
The infinite-tail transfer is now handled both under an explicit summable majorant and directly
from a regular factor analytic beyond the boundary circle. The remaining reduction must derive
that larger-disk amplitude statement uniformly from the contour germ and combine it with the contour
remainder. Once that source-level estimate and the
two-coordinate coefficient germ are supplied, coefficient extraction, normalization,
equal-modulus separation, and the §103 contradiction are formalized. The
specialized finite-intersection count, chart-to-local-length gap, and finite determinant/resultant
correctness gap are now closed; the final rotation-rank implication is also closed once vanishing
at the 24 points is supplied, and a general projective Bézout theorem is no longer needed for this
exact example. The detailed
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
  basis `1, z, z^2, z^3, z^4, z^5, y, yz`, and exact generated membership certificates prove
  that it presents each source chart's localized intersection algebra.
  `RotationFamily.lean` constructs and differentiates the genuine Cayley rotation family and
  identifies its squared-distance derivative with the certified source sextic.
  `SingularBranches.lean` constructs persistent roots of `(Δ, ∂Δ/∂t)` by the complex implicit
  function theorem; `SingularJacobian.lean` reduces its invertibility condition to two scalar
  nonvanishing conditions; and `ImplicitDeformation.lean` feeds the constructed branch into the
  physical endgame.
  `AffineTransversality.lean` differentiates the shape-basis identities and proves an invertible
  Jacobian for the exact sextic–septic pair at every certified finite point.
  `SingularityParameterTangent.lean` proves the exact logarithmic differential of Poincaré's
  `z(x,y)`, while `ReducedCurveTangent.lean` uses compiled coefficient certificates to identify
  the reduced septic with the corresponding constant-`z` derivative at all 24 points.
  `DeformationBridge.lean` formalizes Poincaré's differential equation (2), simultaneous
  vanishing at the 24 points, and the final three-parameter versus two-coordinate contradiction.
- `PoincareChapterVI/ClassicalLeanPool.lean`: pinned bridge to the already-merged classical result.
- `docs/PoincareChapterVI.md`: passage-by-passage source audit and open mathematical gaps.
- `research/chapter_vi_section_103_audit.py`: exact untrusted research audit.

Released under Apache 2.0.
