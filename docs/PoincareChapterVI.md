# Research map for Poincaré's Chapter VI

Status: standalone exploratory research, not a claim that Poincaré's complete proof has been
formalized and not intended for a Lean Pool pull request in its present form.

This note separates three questions that are easy to conflate:

1. What is proved in Chapter VI of volume I of *Les méthodes nouvelles de la mécanique
   céleste*?
2. Which individual reductions have been checked in this Lean repository?
3. What would be required for a faithful modern proof of the decisive argument?

The primary text is [Chapter VI, §§90–103][chapter-vi]. The page-level facsimiles are linked
below where the printed formula matters.

## Bottom line

The repository does **not yet** formalize Poincaré's complete Chapter VI proof. It verifies several exact algebraic
and formal-series subarguments. The central analytic and geometric steps remain open:

- constructing Poincaré's actual two-variable perturbing function as a holomorphic or
  multivalued analytic object;
- proving which candidate singularities pinch the integration cycle and are genuine rather than
  apparent;
- deriving the local logarithmic expansion from a convergent Weierstrass preparation and a
  parameter-dependent contour;
- proving a Darboux remainder estimate strong enough to give eventual nonvanishing;
- justifying the parameter-rank and projective intersection argument in §§102–103, including
  multiplicities, points at infinity, and no-common-component hypotheses.

This is not merely a matter of filling routine Lean library gaps. At the end of §98 Poincaré says
that he has only sketched the discussion and calls for a complete analytic study of the different
branches of `Φ(z)`. A faithful completion therefore contains mathematical reconstruction beyond
transcription of the 1892 text.

## Passage-to-formalization inventory

| Source | Role in the printed argument | Current repository | What is still needed |
| --- | --- | --- | --- |
| §90 | Full three-body Hamiltonian `F = F₀ + μF₁`; isolate the principal mutual-distance term | The existing project has a restricted circular problem and a first mass derivative, not this full Hamiltonian | Decide whether the target is the full problem in Poincaré's variables or the circular restricted theorem; define the exact source Hamiltonian and prove the coordinate/mass expansion |
| §§91–92 | Osculating variables, the first homological equation, and invariance under a coordinate change | The product-rule/homological algebra has restricted analogues | Formalize the source coordinate maps, domains, symplecticity, and the precise notion of a uniform first integral used in Chapter V–VI |
| §93 | Darboux's one-variable coefficient estimates | `eventually_ne_zero_of_tendsto_div_one` proves only the final elementary nonvanishing implication | A singularity-analysis theorem with explicit hypotheses, competing boundary singularities, and a controlled analytic remainder |
| §94 | Convert coefficients on `(m₁,m₂)=(an+b,cn+d)` to coefficients of one Laurent series `Φ(z)` | `ChapterVILatticeReduction.lean` proves the affine-lattice reindexing; `ChapterVIContour.lean` proves finite and absolutely summable Laurent coefficient extraction | Define the actual Fourier series and prove its holomorphic convergence on an annulus, allowing all substitutions, sum/integral interchanges, and branch choices |
| §95 | Candidate singularities arise when moving singularities of the integrand obstruct contour deformation | No source-level analytic theorem | A parameterized contour-deformation theorem for multivalued algebraic integrands; modern language suggests vanishing cycles and Picard–Lefschetz theory |
| §96 | Algebraic equations for candidate singularities | `ChapterVISingularityAlgebra.lean` checks selected half-angle factorizations, reciprocal symmetries, a discriminant, and `z ↦ z⁻¹` | Formalize all collision equations from the actual Kepler parametrization and prove equivalence without losing roots while clearing denominators |
| §§97–98 | Decide which candidates are admissible and which singularity lies on the boundary of the Laurent annulus | Not formalized | Construct the relevant Riemann surface/cycle, compute monodromy or vanishing-cycle intersection, and prove the required parameter regions. Poincaré explicitly says this discussion is only sketched |
| §99 | Localize at a pinch and prepare the double zero as `ψ=((t-h)²+k)ψ₁` | `ChapterVIWeierstrass.lean` proves the analogous statement for nested **formal** power series; `ChapterVIPinchModel.lean` exactly integrates the real symmetric quadratic model and proves its logarithmic asymptotic | Analytic Weierstrass preparation for the actual convergent germ, nondegeneracy, compatible complex square-root branches, transport of the contour, the analytic unit, and the remainder |
| §100 | Integrate the prepared local model to obtain `Φ₂+Φ₃ log(z-z₀)` and apply Darboux | `ChapterVIDarboux.lean` proves the exact coefficients of a model logarithm and an abstract asymptotic-to-nonvanishing step | Derive the logarithmic expansion of the actual integral; prove the leading factor is nonzero; bound the holomorphic and higher-order terms, including all equally dominant singularities |
| §101 | Astronomical example (the Pallas inequality) | Not formalized | Optional for nonintegrability; relevant only if the project also verifies the numerical application |
| §102 | A uniform integral would constrain the singular points to depend on too few parameters | `ChapterVIJacobian.lean` verifies the displayed rescaling of the six-by-six Jacobian to the five ratio derivatives, including the factor `-z₁⁶/ζ⁷`; `ChapterVI.lean` supplies only a conditional restricted-problem interface | Formalize the Chapter V input, analytic dependence/enumeration of singular roots, prove the required ratio Jacobian is nonzero, and justify the passage from coefficient relations to singular-locus relations |
| §103 | Count 24 finite singular points and contradict the rank constraint using two degree-six curves with 44 counted intersections | `ChapterVICurveAlgebra.lean` checks the source identities; `Section103/Geometry.lean` derives the curve from exact ellipses; the Ruppert modules prove the exact affine polynomial irreducible over `ℂ`; `Section103/ProjectiveIrreducibility.lean` proves the homogeneous sextic irreducible; `Section103/ReducedCurve.lean` records the exact cleared septic and proves the two curves have no common component; `Section103/ReducedCurveSource.lean` uses LeanCompCert to prove the displayed source formula clears to that septic; `LocalIntersection.lean` proves the origin transversality and exact initial forms in both infinity charts; `IntersectionResultant.lean` checks both sparse Sylvester determinants through order eight; the rotation minor excludes infinitesimal projective invariance | Prove the subset-determinant/resultant semantic bridge, formalize local intersection multiplicities and projective Bézout, then prove persistence under deformation and the final parameter-rank contradiction |

## What the current Lean files actually establish

The source-facing files added after the standalone-project commit are deliberately small lemmas:

- `ChapterVILatticeReduction.lean`: exact lattice/shear identities for finite tables and summable
  series.
- `ChapterVIContour.lean`: normalized circle integrals extract finite Laurent coefficients, and
  extract an infinite Laurent coefficient under an explicit weighted summability hypothesis.
- `ChapterVISingularityAlgebra.lean`: selected polynomial identities from §96 and the reciprocal
  symmetries that they imply.
- `ChapterVIWeierstrass.lean`: formal Weierstrass preparation over `ℂ⟦z-z₀⟧` followed by completing
  a monic quadratic square.
- `ChapterVIDarboux.lean`: the model logarithm's coefficients and the conditional implication from
  a nonzero Darboux asymptotic to eventual coefficient nonvanishing.
- `ChapterVIJacobian.lean`: the exact determinant row reduction in §102 from the six scaled
  singularities to five singularity ratios, without assuming the missing analytic/rank input.
- `ChapterVICurveAlgebra.lean`: the five-term cubic-form simplification in §103, the corrected
  derivative identity for `P = ∑ Uᵢ²`, the exact derivative-equation reduction modulo `P`, and
  the degree-seven estimate for the reduced curve.
- `ChapterVIPinchModel.lean`: exact integration of the real symmetric quadratic-pinch model,
  decomposition into `-log k` plus a regular term, and the regular term's limit as `k → 0⁺`.
- `Section103/Geometry.lean`, `Section103/RuppertCertificate.lean`,
  `Section103/RuppertKernel.lean`, `Section103/RuppertBounds.lean`,
  `Section103/RuppertNormalization.lean`, `Section103/RuppertIrreducibility.lean`, and
  `Section103/ProjectiveIrreducibility.lean`: exact derivation of the affine coefficient table,
  kernel-checked modular inverse, lift of the nonzero minor through Gaussian integers to full
  column rank over `ℂ`, and a symbolic proof that the matrix is the coefficient map of the
  bounded Ruppert differential expression; completeness of the coefficient encoding; the
  sharp top-degree cancellation in the normalized solution associated to a factorization; and
  an exact mod-17 Bézout/resultant certificate that closes the exceptional case and proves
  irreducibility of the affine polynomial over `ℂ`; and a source-facing homogenization proof
  that transfers this result to the projective sextic while excluding a factor at infinity.
- `Section103/ReducedCurve.lean` and `Section103/ReducedCurveSource.lean`: the reduced septic's
  exact cleared Gaussian coefficient table, homogeneity, and no-common-component theorem, together
  with a LeanCompCert-backed sparse computation proving that `438750` times Poincaré's displayed
  source formula is exactly that projective polynomial. The coefficient table is also connected
  to the cubic vectors derived from the physical ellipse data in `Geometry.lean`.
- `Section103/LocalIntersection.lean` and `Section103/IntersectionResultant.lean`: exact
  dehomogenizations at the affine origin and the two projective axis points; initial degrees
  `(2,1)` at the origin and `(2,3)` at each infinity point; non-divisibility of the origin tangent
  line in the sextic tangent cone; and LeanCompCert certificates that the two sparse `8 × 8`
  Sylvester determinants have zero coefficients below degree eight and nonzero degree-eight
  coefficients. A generic proof relating the subset dynamic program to Mathlib's polynomial
  resultant is still required before calling these local intersection multiplicities.
- `ChapterVI.lean`: a passage-by-passage status statement and a conditional interface from the
  missing Darboux nonvanishing result to the project's restricted nonintegrability theorem.

None of these files constructs Poincaré's `Φ`, identifies its genuine boundary singularity, or
proves the missing asymptotic hypothesis.

## Source problems found in the facsimile

These should be settled in a mathematical note, with expert review, before Lean is asked to choose
a corrected statement.

### Equation (10), p. 290

The [facsimile of p. 290][page-290] prints

```text
2x - sin(φ)(x² - 1) = -2βx.
```

But the immediately preceding equation `1 - sin(φ) cos(u) = ±β`, together with the same
half-angle substitution used throughout the section, gives an `x² + 1` term. The printed
`x² - 1` equation is also not reciprocal, while the next paragraph explicitly says that equations
(1), (9), and (10) are reciprocal. The branch formalizes the `x² + 1` correction. This is strong
internal evidence of a typographical error, but it should be described as a correction rather than
silently attributed to the printed source.

### The leading factor `θ₀,₀`, p. 323

The [facsimile of p. 323][page-323] first states

```text
θ / sqrt((t-h)²+k) = t^(ad-bc-1) z^(-d/c) / sqrt(Δ)
```

and then prints `θ₀,₀` as the monomial factor times `(1/2) ∂²Δ/∂t²`. If
`Δ = (1/2)Δ_tt(t-t₀)² + …` and the prepared monic factor begins with `(t-t₀)²`, the displayed
identity instead makes `θ₀,₀` proportional to `sqrt(2/Δ_tt)`, up to the chosen square-root branch.
Thus the printed formula appears dimensionally and algebraically inconsistent with its preceding
line. This needs an independent derivation and a search for corrigenda or later treatments; it is
not yet encoded in Lean.

### The derivative of `P = ∑ Uᵢ²`, p. 331

The [facsimile of p. 331][page-331] defines `V = x ∂U/∂x - U` and then prints

```text
x ∂P/∂x = 2 ∑ VU + P.
```

Since `P = ∑ U²`, substituting `x ∂U/∂x = V + U` gives
`x ∂P/∂x = 2 ∑ VU + 2P`. The branch verifies the corrected identity in
`chapterVI_curvePolynomial_derivative`. Poincaré immediately restricts to `P=0`, so this typo
does not change the following reduced equation, which
`chapterVI_curvePolynomial_derivative_on_curve` also verifies.

## The hard mathematical core

### 1. Genuine versus apparent pinches (§§95–99)

Solving `ψ=∂ψ/∂t=0` only locates a discriminant. It does not prove that the original integration
cycle is pinched. Poincaré distinguishes genuine and apparent singularities by how sheets of the
Riemann surface and the contour behave. A modern reconstruction should state:

1. a family of algebraic or analytic curves over the parameter `z`;
2. the cycle representing the coefficient integral;
3. the discriminant and its simple points;
4. the local vanishing cycle at each discriminant point;
5. a criterion, normally an intersection number, for whether monodromy changes the integration
   cycle and hence produces an actual logarithmic singularity.

This is the conceptual bottleneck. The local quadratic factorization by itself does not establish
the nonzero logarithmic coefficient. `ChapterVIPinchModel.lean` now proves that the bare real
symmetric model has the expected logarithm; the missing theorem must transport that calculation
through the complex cycle, branch choice, analytic unit, and remaining contour contribution.

### 2. From a local logarithm to a coefficient theorem (§100)

The needed statement is more precise than “a logarithm has coefficients `-z₀⁻ⁿ/n`.” One must
prove that on the relevant annulus:

```text
Φ(z) = H(z) + G(z) log(1-z/z₀),    G(z₀) ≠ 0,
```

with all other singularities on the same modulus either absent or included in the asymptotic, and
with a remainder smaller than the leading term. Multiple boundary singularities can cancel on a
subsequence, so eventual nonvanishing does not follow from a single local calculation unless the
global boundary-singularity statement rules this out.

### 3. The intersection count (§103)

Poincaré takes `P=x²y²Δ` of degree six, reduces the derivative equation on `P=0` to a degree-seven
curve `R=0`, and counts `6·7=42` intersections. He subtracts multiplicities `2` at the origin and
`8+8` in the two directions at infinity to obtain 24 finite singular points. He then compares `P`
with an infinitesimally varied degree-six curve `P'`: the claimed common intersections have total
multiplicity `24+4+8+8=44>36`, so Bézout would force a common component (the text says the curves
coincide), contradicting relative motion of the ellipses.

A rigorous version must make explicit:

- the base field and projective homogenizations;
- generic parameter assumptions and exclusions caused by cleared denominators;
- why `P` and `R` have no common component;
- each local intersection multiplicity, not merely a branch count;
- why the 24 finite points are distinct or how their multiplicities are tracked;
- why the infinitesimal deformation may be replaced by an actual neighboring algebraic curve;
- why a common component implies the stronger invariance conclusion used geometrically.

The arithmetic `42-2-8-8=24` and `44>36` is easy to formalize. The mathematical content lies in
proving that those numbers are the correct local intersection multiplicities.

## A second primary-source route: Poincaré 1897

Poincaré's later paper [*Sur les périodes des intégrales doubles et le développement de la
fonction perturbatrice*][poincare-1897] deserves its own branch of the roadmap. It treats Fourier
coefficients as periods of algebraic double integrals, proves finite reduction relations, and
argues that the period functions satisfy linear differential equations with rational (after
clearing denominators, polynomial) coefficients. For zero eccentricities it reduces the
coefficients to at most five transcendental functions.

This suggests a Picard–Fuchs or holonomic formalization:

```text
algebraic family → finite de Rham/period module → rational differential system
                 → coefficient recurrences → certified nonvanishing question
```

It may be better suited to finite computation than reconstructing every contour drawing in
§§97–98. It is **not yet a replacement proof**: finite recurrences do not automatically prove the
specific nonvanishing or parameter-rank statement needed for nonintegrability, and Poincaré notes
that the exponential factor for mean anomalies prevents immediate application of the algebraic
case. The research task is to determine whether the 1897 differential system can supply a
checkable certificate for the needed coefficients.

## Relation to modern results

Yagasaki's [new proof of Poincaré's restricted result][yagasaki-classical] explicitly describes
the original proof as complicated and unclear and replaces the perturbing-function calculation
with a modern meromorphic nonintegrability criterion near resonant periodic orbits. His
[stronger fixed-mass result][yagasaki-fixed-mass] uses Morales–Ramis type differential-Galois
obstructions and has a different conclusion and proof architecture.

These should be separate roadmap milestones:

1. a precisely scoped classical, small-mass, real-analytic result;
2. an optional reconstruction of Chapter VI as a historical/mathematical verification project;
3. the modern fixed-nonzero-mass meromorphic nonintegrability result.

Formalizing milestone 1 does not require claiming that milestone 2 is complete. Conversely,
verifying scattered Chapter VI calculations is valuable research but should not be marketed as a
proof of milestone 1 until the pinch, asymptotic, and rank arguments are closed.

## Recommended next steps in this repository

1. Use merged [Lean Pool PR #329][lean-pool-pr] as the pinned classical foundation; keep the
   source-faithful Chapter VI reconstruction here until expert review.
2. Write a precise theorem statement for the missing pinch-to-logarithm result, independent of
   celestial-mechanics notation. Compare it against modern vanishing-cycle results before coding.
3. Re-derive the local factor `θ₀,₀` and ask a complex-analysis/celestial-mechanics expert to check
   both identified source corrections.
4. Use the now-formalized Jacobian rescaling identity in §102 to state the remaining analytic and
   rank input precisely; do not infer the nonzero determinant from the algebraic identity alone.
5. Starting from the now-formalized §103 reduction and degree-seven bound, prototype the
   projective curves in a computer algebra system to verify homogenizations, exceptional factors,
   and local multiplicities before choosing Lean intersection-theory statements.
6. Study whether the 1897 Picard–Fuchs relations yield finite certificates compatible with the
   finite-computation infrastructure. Treat this as an alternative research route, not as a
   completed bridge.
7. Ask reviewers to evaluate the mathematical reconstruction document first. Open a formalization
   PR only when a self-contained theorem and its source correspondence are stable.

## Faithful-completion decision

The research target is now a completion of Poincaré's own route, rather than a proof of a similar
nonintegrability statement by the collision-band or Morales--Ramis routes. Modern results may be
used to justify a step that Poincaré describes informally, but the completed proof must retain the
following chain:

```text
Fourier ray -> Phi(z) -> collision discriminant -> admissible contour pinch
            -> logarithmic branch -> Darboux coefficients -> singular-locus rank
            -> degree-six/seven intersection count -> nonintegrability
```

In particular, a direct validated quadrature certificate is not a substitute for the singularity
analysis. Validated computation may certify root separation, continuation, intersection
multiplicity, or a nonzero determinant inside that chain.

### First exact audit of §103

The script `chapter_vi_section_103_audit.py` constructs an exact spatial example from two genuine
Kepler ellipses. It uses eccentricities `3/5` and `5/13`, minor-axis factors `4/5` and `12/13`,
semimajor-axis ratio `2`, and the rational rotation obtained from the quaternion `(1,2,3,4)`.
All calculations take place over `Q(i)`.

For this example the audit establishes computationally, with exact rational arithmetic:

- `deg P = 6`, `deg R = 7`, and `gcd(P,R)=1`;
- the affine-origin contribution is `2`, by transversality of the tangent line of `R` to the
  quadratic tangent cone of `P`;
- the resultant orders in the two projective axis charts are both `8`, matching Poincaré's two
  claimed contributions at infinity;
- the differential of the map from the three relative-rotation directions to the projective
  coefficient vector of `P` is injective. A four-by-four coefficient minor has determinant
  `(90576 - 340992 i) / 6865625`, which is nonzero.
- after dehomogenizing to `f = P(x,y,1)`, the exact `64 x 35` Ruppert matrix has rank `35` over
  `Q(i)`. By Ruppert's characteristic-zero criterion, this is the finite certificate needed to
  prove that `f`, and hence the projective curve `P`, is absolutely irreducible.

The rotation item gives a precise repair of the final geometric paragraph: no nonzero infinitesimal
relative rotation can preserve the curve `P = 0`, even up to rescaling. It does not yet prove the
preceding Bézout implication. Lean now reconstructs the 25 cleared Gaussian coefficients from the
ellipse convolution, checks a modular inverse for a 35-row minor with LeanCompCert's
`verified_decide`, proves that the Gaussian determinant is nonzero, and lifts full column rank to
`ℂ`. The Ruppert files verify the quotient-rule identity, sharp factor bounds, a mod-17 Bézout
certificate for squarefreeness over `ℂ(x)`, and the conclusion that the exact affine polynomial is
irreducible over `ℂ`; the projective module transfers that theorem to the homogeneous sextic.
Lean also proves the cleared septic table has no common component with the sextic, and a
LeanCompCert-backed sparse certificate now derives that table from the displayed source formula.
The remaining algebraic-geometric tasks are the subset-determinant/resultant correctness bridge,
projective Bézout and local intersection-multiplicity theorems, followed by the deformation/rank implication. Those steps now
form the gap in the repair of Poincaré's jump from "more than 36 intersections" to "the curves
coincide."

## LeanCompCert trust boundary

The exact audit first found a rank-35 matrix over `Q(i)`. The formal certificate does not trust that
answer. Lean reconstructs the matrix from the ellipse coefficients, reduces Gaussian integers via
`i ↦ 12` in `ZMod 29`, and checks all entries of a proposed inverse in the kernel. The external
Python/SymPy script is therefore a certificate generator and cross-check only. The resulting
theorems contain no `native_decide` or externally admitted run result.

## Sources

- Henri Poincaré, [*Les méthodes nouvelles de la mécanique céleste*, volume I, Chapter VI
  (§§90–103)][chapter-vi], 1892.
- Henri Poincaré, [facsimiles p. 290][page-290], [p. 323][page-323], and [p. 331][page-331].
- Henri Poincaré, [*Sur les périodes des intégrales doubles et le développement de la fonction
  perturbatrice*][poincare-1897], *Journal de mathématiques pures et appliquées* 5e série, 3
  (1897), 203–276.
- Kazuyuki Yagasaki, [*A new proof of Poincaré's result on the restricted three-body
  problem*][yagasaki-classical], arXiv:2111.11031.
- Kazuyuki Yagasaki, [*Nonintegrability of the restricted three-body
  problem*][yagasaki-fixed-mass], arXiv:2106.04925.
- Shuhong Gao, [*Factoring multivariate polynomials via partial differential
  equations*][gao-ruppert], *Mathematics of Computation* 72 (2003), 801–822. Theorem 2.1 states
  the Ruppert characteristic-zero criterion used in the §103 repair.

[chapter-vi]: https://fr.wikisource.org/wiki/Les_m%C3%A9thodes_nouvelles_de_la_m%C3%A9canique_c%C3%A9leste/Chap.06
[page-290]: https://fr.wikisource.org/wiki/Page:Henri_Poincar%C3%A9_-_Les_m%C3%A9thodes_nouvelles_de_la_m%C3%A9canique_c%C3%A9leste,_Tome_1,_1892.djvu/302
[page-323]: https://fr.wikisource.org/wiki/Page:Henri_Poincar%C3%A9_-_Les_m%C3%A9thodes_nouvelles_de_la_m%C3%A9canique_c%C3%A9leste,_Tome_1,_1892.djvu/335
[page-331]: https://fr.wikisource.org/wiki/Page:Henri_Poincar%C3%A9_-_Les_m%C3%A9thodes_nouvelles_de_la_m%C3%A9canique_c%C3%A9leste,_Tome_1,_1892.djvu/343
[poincare-1897]: https://www.numdam.org/item/JMPA_1897_5_3__203_0.pdf
[yagasaki-classical]: https://arxiv.org/abs/2111.11031
[yagasaki-fixed-mass]: https://arxiv.org/abs/2106.04925
[gao-ruppert]: https://www.ams.org/journals/mcom/2003-72-242/S0025-5718-02-01428-9/
[lean-pool-pr]: https://github.com/Vilin97/lean-pool/pull/329
