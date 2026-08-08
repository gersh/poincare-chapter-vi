# Research map for Poincaré's Chapter VI

Status: standalone exploratory research, not a claim that Poincaré's complete proof has been
formalized and not intended for a Lean Pool pull request in its present form.

This note separates three questions that are easy to conflate:

1. What is proved in Chapter VI of volume I of *Les méthodes nouvelles de la mécanique
   céleste*?
2. Which individual reductions have been checked in this Lean repository?
3. What would be required for a faithful modern proof of the decisive argument?

The primary text is [Chapter VI, §§90–103][chapter-vi]. For the §102 dependency argument, see
especially [p. 326][page-326], [p. 327][page-327], [p. 328][page-328], and [p. 329][page-329].
The page-level facsimiles are linked below where the printed formula matters.

## Bottom line

The repository does **not yet** formalize Poincaré's complete Chapter VI proof. It verifies several exact algebraic
and formal-series subarguments. The central analytic and geometric steps remain open:

- proving that the selected algebraic candidate is an admissible, nondegenerate double pinch for
  the now-constructed analytic radicand `ψ(z,t)` and the actual integration cycle;
- proving which candidate singularities pinch the integration cycle and are genuine rather than
  apparent;
- carrying the actual parameter-dependent source contour into the now-constructed local prepared
  branch and proving that the resulting logarithmic term has the required nonzero coefficient;
- deriving the logarithmic decomposition from the contour pinch and proving that its amplitudes
  extend analytically beyond the common boundary circle;
- deriving Poincaré's §102 rank-at-most-two conclusion for the singular-root differential from
  the Chapter V input. The actual moving algebraic equations, their analytic branches at all 24
  certified points, and the ensuing §103 rank contradiction are now formalized.

This is not merely a matter of filling routine Lean library gaps. At the end of §98 Poincaré says
that he has only sketched the discussion and calls for a complete analytic study of the different
branches of `Φ(z)`. A faithful completion therefore contains mathematical reconstruction beyond
transcription of the 1892 text.

## Passage-to-formalization inventory

| Source | Role in the printed argument | Current repository | What is still needed |
| --- | --- | --- | --- |
| §90 | Full three-body Hamiltonian `F = F₀ + μF₁`; isolate the principal mutual-distance term | The existing project has a restricted circular problem and a first mass derivative, not this full Hamiltonian | Decide whether the target is the full problem in Poincaré's variables or the circular restricted theorem; define the exact source Hamiltonian and prove the coordinate/mass expansion |
| §§91–92 | Osculating variables, the first homological equation, and invariance under a coordinate change | The product-rule/homological algebra has restricted analogues | Formalize the source coordinate maps, domains, symplecticity, and the precise notion of a uniform first integral used in Chapter V–VI |
| §93 | Darboux's one-variable coefficient estimates | `ChapterVIDarbouxTransfer.lean` proves coefficient extraction, larger-disk remainder decay, finite-jet decay, conditional Tannery transfer, and a weighted-convolution transfer whose summability follows from larger-disk analyticity; `ChapterVIDarbouxSpectrum.lean` separates competing equal-modulus bases | Derive the regular-factor analytic decomposition from the actual contour singularities, uniformly in the parameters |
| §94 | Convert coefficients on `(m₁,m₂)=(an+b,cn+d)` to coefficients of one Laurent series `Φ(z)` | `ChapterVILatticeReduction.lean` proves the affine-lattice reindexing; `ChapterVIContour.lean` proves finite and absolutely summable Laurent coefficient extraction; `ChapterVIPhi.lean` defines the literal normalized `Φ`, proves its finite contour value is exactly Poincaré's affine-ray Laurent polynomial, and keeps the selected `c`-th root explicit | Define the complete physical perturbing Fourier series and prove its holomorphic convergence on an annulus, allowing all substitutions, infinite sum/integral interchanges, and branch choices |
| §95 | Candidate singularities arise when moving singularities of the integrand obstruct contour deformation | `ChapterVIContourTransport.lean` proves equality for a relative `C²` homotopy, derives closedness automatically, and supplies a direct prepared-inverse-root theorem on convex branch subdomains; `ChapterVIPhi.lean` constructs the positively oriented unit-circle path, proves its curve integral is the literal §94 circle integral, and transports the normalized `Φ` along a checked deformation | Lift that explicit circle to the source branch sheet and construct its admissible deformation up to the collision; then prove when deformation is obstructed, likely using vanishing-cycle/Picard–Lefschetz methods |
| §96 | Algebraic equations for candidate singularities | `ChapterVISingularityAlgebra.lean` identifies the concrete Laurent radicand with `(ξ-βη)(ξ₀-β₀η₀)`, proves that clearing `2xy` gives the product of the general collision cubics, and verifies both-eccentricity half-angle reductions. `ChapterVISourceCoordinates.lean` constructs the literal analytic germ `ψ(z,t)`. `ChapterVIDCandidate.lean` and `ChapterVIDFiberDerivative.lean` certify a concrete point `D`, prove both inverse-coordinate ODEs on a neighborhood, and prove the complete literal radicand has fiber order exactly two | Extend the concrete instance to Poincaré's parameter region and connect it to the global admissibility deformation |
| §§97–98 | Decide which candidates are admissible and which singularity lies on the boundary of the Laurent annulus | Not formalized | Construct the relevant Riemann surface/cycle, compute monodromy or vanishing-cycle intersection, and prove the required parameter regions. Poincaré explicitly says this discussion is only sketched |
| §99 | Localize at a pinch and prepare the double zero as `ψ=((t-h)²+k)ψ₁` | `ChapterVISourceCoordinates.lean` constructs Poincaré's literal convergent `ψ(z,t)` and splits it as `H H₀`. `ChapterVIDoubleZero.lean` reduces exact fiber order two to four source checks, all discharged for the certified point D by `ChapterVIDFiberDerivative.lean`. `ChapterVIAnalyticCriticalCenter.lean` constructs the analytic critical center. `FiberHadamard.lean` and `ChapterVIAnalyticCentering.lean` divide `ψ(z,h(z)+u)-ψ(z,h(z))` twice and produce a jointly analytic nonvanishing unit. `ChapterVIParametricMorse.lean` restores the unsubtracted critical value: the analytic coordinate `v=u√U(z,u)` has an analytic local inverse and gives exactly `ψ(z,h(z)+u(z,v))=ψ(z,h(z))+v²`. `ChapterVIMorseAmplitude.lean` proves that the inverse Jacobian is analytic and nonzero and pulls the full analytic numerator and differential into Poincaré's `θ(z,v)dv/root(k(z)+v²)` form. `ChapterVICriticalParameter.lean` shows, conditional on the isolated finite check `k'(z_D)≠0`, that `k` is an analytic coordinate and the literal source radicand is exactly `k+v²`. `ChapterVIJointPreparation.lean` identifies the singular-fiber primitive `A(0) log u+Q(u)` with `A(0)≠0`. | Certify `k'(z_D)≠0`; transport the actual source cycle through the chart, relate its local arc to the selected square-root sheet, and control the nonlocal contour remainder |
| §100 | Integrate the prepared local model to obtain `Φ₂+Φ₃ log(z-z₀)` and apply Darboux | `ChapterVIJointPreparation.lean` proves the exact integral of the prepared inverse branch along every admissible straight local arc is `A(0)(log u₁-log u₀)+Q(u₁)-Q(u₀)`, with `A(0)≠0`. `ChapterVIDarbouxTransfer.lean` proves scalar Cauchy-product coefficients, derives coefficients from a function-level varying-log germ, constructs `G(z)=G(z₀)+(1-z/z₀)H(z)` by holomorphic divided difference, and applies a weighted-convolution estimate; `ChapterVIDarbouxSpectrum.lean` recovers all equal-modulus bases | Identify such an arc inside the actual continued source cycle, control the complementary contour contribution, and prove larger-disk analyticity uniformly in the orbital parameters |
| §101 | Astronomical example (the Pallas inequality) | Not formalized | Optional for nonintegrability; relevant only if the project also verifies the numerical application |
| §102 | A uniform integral would constrain the singular points to depend on too few parameters | `ChapterVIJacobian.lean` verifies the displayed rescaling. `ChapterVISection102DarbouxTransfer.lean` keeps the common radius explicit (`R z₀⁻¹`), supports constant, finite-jet, Tannery-controlled, and regular-factor analytic amplitudes, prevents root-label permutation, and reaches the compiled §103 contradiction | Derive the two-coordinate coefficient germ, its finite singular enumeration, common radius, and regular-factor analyticity from the Chapter V uniform-integral relation and the actual contour integral |
| §103 | Count 24 finite singular points and contradict the rank constraint using the sextic and reduced septic | The exact curve, irreducibility, local multiplicities, 24-point affine locus, transversality, rotation source, and finite restriction calculation are formalized under `Section103/`. `MovingAlgebraicBranches.lean` constructs the moving sextic and septic from the Cayley rotation, proves joint analyticity, applies the complex IFT at every certified point, computes the canonical root differential, derives equation (2) from first-order stationarity, and completes the contradiction through the LeanCompCert certificate | No additional finite calculation or source-identification interface remains in the §103 endgame |

## What the current Lean files actually establish

Update to the §103 row: `MovingAlgebraicBranches.lean` closes the formerly missing direct bridge.
It constructs the moving `(P,R)` equations from `RotationFamily.lean`, proves their analyticity,
uses `AffineTransversality.lean` to obtain IFT branches at all 24 points, and identifies the
parameter derivative with the certified rotation source.
`SingularityParameterTangent.lean` and `ReducedCurveTangent.lean` now close the intermediate
coordinate calculation: the explicit singularity parameter has Poincaré's displayed
logarithmic differential, its polynomial kernel direction is exactly the direction defining the
reduced septic, and the certified sextic derivative vanishes in that direction at all 24 points.
The still-open bridge is now narrower. The current source-facing interfaces
`TwoCoordinateFiniteLogarithmicFactorization` and
`TwoCoordinateFiniteLogAmplitudeJetFactorization` cover constant amplitudes and polynomial
amplitude jets respectively. `TwoCoordinateAnalyticLogAmplitudeFactorization` now covers the full
infinite amplitude series under explicit Tannery domination. Reaching it from the actual contour
requires a uniform summable majorant. The newer
`TwoCoordinateRegularAnalyticLogAmplitudeFactorization` instead records
`G(z)=G(z₀)+(1-z/z₀)H(z)` and derives that majorant internally from larger-disk analyticity of
`H`. The divided-difference theorem constructs this factorization and `H`'s scalar power series
from larger-disk analyticity of `G`. `TwoCoordinateAnalyticLogGermFactorization` goes further: it
starts from the function-level logarithmic decomposition and derives its Cauchy-product
coefficients and all tail estimates internally. Reaching it therefore requires proving that
decomposition, nonzero leading amplitudes, common boundary radius, two-coordinate dependence,
and the larger-disk analyticity of `G`.
Analytic-germ uniqueness, every finite amplitude jet, full regular-factor tail transfer,
coefficient extraction, common-radius normalization, finite equal-modulus spectrum recovery,
prevention of local root permutation, and the §103 contradiction are formalized.

The source-facing files added after the standalone-project commit are deliberately small lemmas:

- `ChapterVILatticeReduction.lean`: exact lattice/shear identities for finite tables and summable
  series.
- `ChapterVIContour.lean`: normalized circle integrals extract finite Laurent coefficients, and
  extract an infinite Laurent coefficient under an explicit weighted summability hypothesis.
- `ChapterVIPhi.lean`: the literal normalized function `Φ(z)`, its exact finite affine-ray
  Laurent value with the `c`-th-root choice exposed, the explicit positively oriented unit-circle
  path and its equality with the circle-integral definition, and a path-valued version whose
  invariance follows from a checked holomorphic relative contour homotopy.
- `ChapterVISingularityAlgebra.lean`: Poincaré's concrete planar source radicand, its exact
  Laurent/trigonometric correspondence, the general cleared collision cubics, both-eccentricity
  half-angle reductions, and the reciprocal symmetries from §96.
- `ChapterVISourceCoordinates.lean`: the exact exponential Kepler map and derivative, canonical
  local analytic inverse branches, the identity between Poincaré's `z` and the monomial in the two
  mean-anomaly exponentials, and complete convergent power-series realizations of the actual
  radicand in mean-anomaly, `(z,s)`, and literal `(z,t)` coordinates. It records every nonzero
  denominator and critical-point exclusion explicitly. It also names the complete inverse map
  from `(z,t)` to `(x,y)`, proves that map and both collision factors analytic, and proves the
  exact product identity `ψ=H H₀`.
- `ChapterVIDoubleZero.lean`: the exact analytic-order interface for a double collision factor.
  It reduces the order-two premise on Poincaré's complete convergent radicand to four finite
  source-point checks, providing the boundary at which a LeanCompCert certificate can be used
  without replacing an infinite analytic germ by a finite truncation.
- `ChapterVIDCandidate.lean`: a concrete rational instance of Poincaré's point `D`, with
  `a=-1`, `c=3`, `τ=1/100`, and `β=2`. A LeanCompCert endpoint certificate and the
  intermediate-value theorem isolate the unique small negative equation-(7) root in
  `[-27/1000,-26/1000]`; the file proves that root simple, places the resulting `(x,y)` exactly
  on collision curve (3), and proves the companion factor nonzero. This is a rigorous local
  algebraic instance, not yet a verification of Poincaré's global admissibility deformation.
- `ChapterVIDFiberDerivative.lean`: the exact differential-ideal identity behind equation (7),
  neighborhood-valid ODEs for both actual inverse-coordinate anomaly functions on the fixed-`z`
  fiber, and the resulting proofs that Poincaré's literal collision factor has zero first and
  nonzero second derivative at the certified `D` point. After selecting a cubic lift `t_D`, it
  proves that the complete convergent literal radicand has analytic order exactly two there. The
  equation-(7) root is supplied by the compiled certificate; the local inverse and differentiation
  steps are kernel-checked analytic arguments.
- `ChapterVIAnalyticCriticalCenter.lean`: the complex implicit-function step at D. It proves that
  the partial derivative of the exact convergent two-variable radicand has an invertible fiber
  derivative, constructs an analytic moving center through `t_D`, and proves the ordinary
  fixed-parameter derivative vanishes at that center throughout a neighborhood. This is
  Poincaré's translation-to-the-critical-point step, not yet the convergent Weierstrass
  factorization that follows it.
- `ChapterVIAnalyticCentering.lean`: a named choice of that analytic center, its analytic critical
  value, and the exact translated radicand after subtracting that value. The complete centered
  germ is represented by a convergent multivariable power series, vanishes identically on the
  parameter axis, has first fiber derivative zero there near D, and has exact fiber order two at
  D. A reusable convergent Hadamard-division construction then divides the full two-variable germ
  twice by the fiber coordinate. It produces a jointly analytic `U(z,u)` satisfying
  `ψ(z,u)=u²U(z,u)` on a neighborhood, and comparison with the singular-fiber factorization proves
  that `U(D,0)` is nonzero. The same exact order-two and convergent one-variable factorization is
  also proved for every sufficiently nearby parameter fiber. On the singular fiber the chosen unit
  is given a local
  holomorphic square root, producing a holomorphic inverse-square-root branch off the pinch that
  is proved algebraically correct for the actual centered source radicand. This actual branch is
  then decomposed exactly as `A(0)/u + R(u)`, with `A(0) ≠ 0` and `R` analytic at the pinch.
  On a small disk intersected with the principal slit plane, a local primitive is constructed
  explicitly as `A(0) log u + Q(u)`, where `Q′ = R`. Thus the singular fiber now supplies the
  actual nonzero logarithmic term, not only its formal pole. The canonical joint unit is defined
  as `ψ(z,u)/u²` off the centered axis and `∂²ᵤψ(z,0)/2` on it; Lean proves the exact
  factorization everywhere, nonvanishing at D, and analyticity off the axis. Identifying that
  particular axis normalization with the constructed joint analytic unit remains open; placement
  of the source cycle also remains open.
- `ChapterVIJointPreparation.lean`: packages the twice-divided centered source germ as a
  `ChapterVIConvergentPreparedGerm` whose center and kappa are identically zero and whose
  quadratic factor is exactly `u²`. The generic local square-root machinery therefore gives a
  holomorphic two-variable inverse branch certified against the actual centered radicand. The
  joint unit and its automatically selected root are proved to restrict to the singular-fiber
  unit and root as germs. On the sheet `sqrt(u²)=u`, the explicit singular-fiber primitive
  `A(0) log u + Q(u)` is consequently a primitive of the prepared inverse branch itself. A
  straight-segment fundamental theorem then gives the exact logarithmic endpoint jump for every
  local arc contained in that chart and sheet.
- `ChapterVIParametricMorse.lean`: corrects the centered-versus-unsubtracted distinction. The
  selected analytic square root defines `v=u√U(z,u)`; Lean proves its joint derivative is
  invertible, constructs and proves analyticity of the local inverse, and obtains the convergent
  normal form `ψ(z,h(z)+u(z,v))=ψ(z,h(z))+v²` for the original source radicand. This is a stated
  analytic coordinate change, rather than an unproved convergence claim for the formal
  Weierstrass factors in the original `t` coordinate.
- `ChapterVIMorseAmplitude.lean`: differentiates the inverse Morse coordinate in the vertical
  direction, proves the Jacobian is analytic and nonzero near D, reconstructs the original source
  point, and proves the exact pullback of an arbitrary analytic inverse-root one-form. This adds
  the `dt` factor needed for Poincaré's local `θ(z,v)/root(k(z)+v²)` integrand, while leaving the
  compatible local square-root sheet explicit.
- `ChapterVICriticalParameter.lean`: isolates the finite transversality premise
  `deriv k z_D ≠ 0`, constructs the analytic inverse `z(k)`, and proves that the actual source
  radicand in `(k,v)` coordinates equals `k+v²`. This is the exact interface between a prospective
  compiled source-algebra certificate and the ordinary Lean proof of the analytic local model.
- `ChapterVIWeierstrass.lean`: formal Weierstrass preparation over `ℂ⟦z-z₀⟧` followed by completing
  a monic quadratic square.
- `ChapterVIAnalyticPreparation.lean`: uniqueness of convergent multivariable-series
  realizations, and the resulting neighborhood factorization and nonvanishing-unit conclusions
  for a convergent prepared germ. From local analyticity it constructs the unit root, the open
  punctured quadratic chart, and a holomorphic inverse branch proved correct for the original
  radicand. Its fixed-parameter slice theorem plugs this actual branch into contour invariance and
  derives closure continuity from containment in the chart. It deliberately leaves existence and
  convergence of the realization separate from finite coefficient certification.
- `ChapterVIDarboux.lean`: the model logarithm's coefficients, the conditional implication from
  a nonzero Darboux asymptotic to eventual coefficient nonvanishing, convergence of consecutive
  coefficient ratios to the inverse singularity, and uniqueness of that recovered singularity.
- `ChapterVIDarbouxSpectrum.lean`: the annihilating recurrence and Vandermonde moment map for a
  finite exponential spectrum, uniqueness of normalized unit-circle spectra modulo `o(1)`, and
  local label stability for continuously moving roots.
- `ChapterVIDarbouxTransfer.lean`: Taylor coefficients of the logarithmic germ, finite weighted
  log sums, coefficient uniqueness from equality of analytic germs, normalized decay of a
  larger-disk analytic remainder, normalized decay of every positive-order
  logarithmic-amplitude jet, and Tannery summation of an infinite amplitude tail under a
  summable uniform majorant. It also proves the exact first-vanishing kernel, a weighted
  convolution theorem, and the needed first-moment summability from larger-disk analyticity.
  It also constructs the regular factor and its scalar power series using a removable holomorphic
  divided difference, and proves the scalar Cauchy-product rule needed to extract coefficients
  from the full varying-log germ.
- `ChapterVIJacobian.lean`: the exact determinant row reduction in §102 from the six scaled
  singularities to five singularity ratios and the resulting equivalence of determinant
  vanishing, without assuming the missing analytic/rank input.
- `ChapterVISection102.lean`: the p. 329 block-triangular determinant factorization, the canonical
  differential of all 24 constructed second-kind roots, rank-nullity extraction of a nonzero
  common stationary direction, both isolated and equal-modulus coefficient-to-root Darboux
  recovery bridges, and the contradiction with the compiled §103 restriction certificate.
- `ChapterVISection102DarbouxTransfer.lean`: the correctly scaled equal-modulus interface and its
  construction from either a finite constant-leading-logarithm germ decomposition or finite
  analytic log-amplitude jets, plus the full analytic-amplitude interface with explicit Tannery
  control, the regular-factor interface that derives this control from analyticity, and the
  function-level analytic-log interface that also derives the coefficient identity.
- `ChapterVICurveAlgebra.lean`: the five-term cubic-form simplification in §103, the corrected
  derivative identity for `P = ∑ Uᵢ²`, the exact derivative-equation reduction modulo `P`, and
  the degree-seven estimate for the reduced curve.
- `ChapterVIPinchModel.lean`: exact integration of the real symmetric quadratic-pinch model,
  decomposition into `-log k` plus a regular term, and stability of the leading logarithmic
  coefficient under a continuous Lipschitz amplitude. Its source-facing theorem accepts a
  parameter-dependent amplitude in any complete real normed space, including `ℂ`: the varying
  part is uniformly bounded and inverse `-log k` times the weighted integral tends to the limiting
  center value. `C¹` regularity on a compact parameter-contour rectangle now supplies the required
  uniform Lipschitz constant automatically. A further theorem performs the exact moving-center substitution from
  `[h(k)-L,h(k)+L]` and obtains the amplitude's limit at `h(k)`.
- `ChapterVIComplexBranch.lean`: a compatible holomorphic square-root branch for a prepared
  product `quadratic * unit` on any domain mapped factorwise into `Complex.slitPlane`, including
  pointwise square correctness, nonvanishing, and holomorphicity of the inverse branch used by the
  contour integrand. The domain may be a joint parameter-contour space; continuity constructs an
  open common chart containing a prescribed point or entire cycle family. An additional
  construction gives every holomorphic unit nonzero at a base point a local root germ without any
  principal-slit assumption, then combines it with the quadratic factor.
- `ChapterVIContourTransport.lean`: a genuine non-affine contour-deformation theorem using
  Mathlib's formalized Poincaré/Stokes theorem. It constructs the closed one-form associated with
  any holomorphic scalar integrand, proves derivative symmetry, handles relative endpoint
  boundaries, and specializes to the prepared inverse square-root branch. It also constructs the
  pointwise affine homotopy of two paths and proves containment automatically on convex branch
  subdomains. `C²` extensions of the paths automatically imply `C²` regularity of the homotopy,
  giving a direct convex-domain transport theorem for both the principal prepared inverse root and
  the automatically selected arbitrary-unit root germ.
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
  source formula is exactly that projective polynomial. A second compiled coefficient-cube
  certificate proves `50700 · ∑ᵢ Uᵢ²` is the certified projective sextic. The coefficient tables
  are connected to the cubic vectors derived from the physical ellipse data in `Geometry.lean`.
- `Section103/SingularityParameterTangent.lean` and
  `Section103/ReducedCurveTangent.lean`: direct differentiation of Poincaré's transcendental
  singularity parameter, the exact `dz = 0` chain-rule consequence, dehomogenization of both
  compiled source certificates, and the theorem that the certified sextic has zero derivative
  in the constant-singularity-value direction at every one of the 24 finite intersections.
- `Section103/LocalIntersection.lean`, `Section103/IntersectionResultant.lean`,
  `Section103/ResultantSoundness.lean`, `Section103/ChartResultant.lean`, and
  `Section103/LocalAlgebra.lean`: exact
  dehomogenizations at the affine origin and the two projective axis points; initial degrees
  `(2,1)` at the origin and `(2,3)` at each infinity point; non-divisibility of the origin tangent
  line in the sextic tangent cone; and LeanCompCert certificates that the two sparse `8 × 8`
  Sylvester determinants have zero coefficients below degree eight and nonzero degree-eight
  coefficients. A coefficientwise jet proof linked to Mathlib's verified Bird determinant
  identifies the genuine polynomial resultants and proves that both have trailing degree eight.
  The final bridge maps the certificates through the injective embedding `ℚ[i] → ℂ`, proves
  that their inputs are exactly the iterated-polynomial forms of the source chart equations, and
  proves trailing degree eight for those geometric resultants. Local multiplicity itself is now
  defined as the length of the quotient by the curve equations in the local ring, and the three
  source instances are named. `OriginMultiplicity.lean` proves intrinsically that the affine
  origin has length two. `TriangularAlgebra.lean` constructs the finite local normal form shared
  by the two infinity charts, proves its relations
  `y² + a z⁴ + b z⁵ = 0`, `y z² + c z⁴ + d z⁵ = 0`, `z⁶ = 0`, and proves that its displayed
  basis `1,z,z²,z³,z⁴,z⁵,y,yz` has dimension eight. `InfinityLocalModel.lean` proves the model's
  augmentation ideal is nilpotent, characterizes its units by nonzero constant coordinate, and
  consequently extends polynomial evaluation to the plane local ring; all three triangular
  relations lie in the kernel of that local map. It also constructs an eight-step socle
  filtration from the triangular ideal to the maximal ideal and proves that the actual localized
  quotient has module length eight. `InfinityNormalFormCertificate.lean` and its generated data
  give exact `ℚ(i)` polynomial membership witnesses in both directions for both source charts;
  the executable normalizer checks all ten identities and its soundness proof transports them to
  `MvPolynomial (Fin 2) ℂ`. `InfinityChartNormalForm.lean` proves each common cofactor is a unit in
  the chart local ring, identifies each two-generator source ideal with its triangular model, and
  concludes that both intrinsic infinity multiplicities equal eight.
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
the nonzero logarithmic coefficient. `ChapterVIPinchModel.lean` now proves that the real symmetric
model has the expected logarithm even after multiplication by a continuous Lipschitz unit: the
coefficient is exactly the unit's value at the pinch. This has now been proved for complex-valued,
parameter-dependent amplitudes; `C¹` regularity on the compact local rectangle now derives the
uniform contour-coordinate Lipschitz estimate. The missing
branch algebra is now formalized on a joint common slit-plane chart, and continuity constructs the
open chart once factorwise slit-plane values on the cycle are known. The missing theorem must
verify those values for the actual complex moving cycle, transport that cycle to the symmetric
local model by constructing the relative `C²` homotopy required by the now-formalized transport
theorem, and control the remaining contour contribution.

### 2. From a local logarithm to a coefficient theorem (§100)

`ChapterVIDarbouxTransfer.lean` now closes the coefficient calculation once the following
constant-leading-logarithm decomposition is available on the relevant disk:

```text
Φ(z) = H(z) + ∑ⱼ Aⱼ log(1-z/zⱼ),    Aⱼ ≠ 0,
```

where all `zⱼ` have the common boundary radius and `H` is analytic on a strictly larger disk.
Lean proves the exact Taylor coefficients from equality of analytic germs, proves the normalized
coefficients of `H` tend to zero, and separates all equal-modulus bases. The remaining source
work is to obtain this form from Poincaré's actual `Φ₂(z)+Φ₃(z) log(z-z₀)` expressions. In
particular, the nonconstant part of each analytic factor `Φ₃` produces subleading logarithmic
terms rather than a larger-disk analytic function. Every Taylor order is now proved individually
subleading, and Tannery's theorem sums the infinite tail under an explicit summable majorant.
More directly, Lean now writes the nonconstant part as `(1-z/z₀)H(z)`, proves the corresponding
kernel is `O(1/n²)`, and derives the required convolution decay whenever `H` is analytic beyond
the boundary circle. It also constructs `H` automatically from any `G` analytic beyond `z₀`.
The scalar Cauchy-product theorem now derives the coefficient identity from the function-level
germ. What remains is to establish that germ and its larger-disk amplitude analyticity for the
actual contour integral with the uniform parameter control used by §102. Multiple
boundary singularities can also cancel on a subsequence, which is why the formal theorem recovers
the entire finite spectrum rather than asserting eventual nonvanishing of the combined sequence.

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
The two order-eight resultant certificates are formally identified with the exact complex
dehomogenized chart pairs, rather than only with parallel coefficient tables.
The affine-origin local multiplicity is proved to be two. Exact normal-form membership
certificates identify both infinity chart ideals with their triangular local ideals, proving that
both intrinsic infinity multiplicities are eight. A separate bidirectional affine-elimination
certificate proves directly, without requiring a general projective Bézout library theorem, that
the source sextic and septic have exactly 24 distinct non-origin affine common zeros.
`RotationRestriction.lean` then reduces the three exact rotation derivatives modulo the radical
shape ideal. Their remainders have degree at most 23, while a checked three-by-three coefficient
minor is nonsingular modulo 53; hence a derivative combination vanishing at all 24 roots has zero
rotation vector. `RotationSource.lean` proves that the certified cleared sextics are exactly the
source derivatives obtained from rotating the physical second ellipse.
`RotationFamily.lean` integrates those infinitesimal generators to an explicit rational Cayley
family. It proves complex orthogonality wherever the Cayley denominators are nonzero,
differentiates the moving axes and all cubic coefficients, and proves that the derivative of the
actual affine squared-distance sextic is evaluation of the certified source polynomial.
`DeformationBridge.lean` now proves the differential passage that Poincaré writes as equation
(2). For a differentiable persistent zero `Δ(t(γ₃),z(γ₃),γ₃)=0`, its exact chain rule uses
`∂Δ/∂t=0` and `dz/dγ₃=0` to conclude `∂Δ/∂γ₃=0`. The file applies this simultaneously to the
24 certified points and then proves the final rank-nullity contradiction: a continuous linear
map from three rotation directions to two essential singular coordinates has a nonzero kernel,
while the exact rotation certificate forces every kernel direction admitting those local
deformations to be zero. Its physical deformation structure derives the coefficient-level
parameter derivative from local agreement with the genuine rotation family; it no longer assumes
that derivative equality. `SingularBranches.lean` now constructs the persistent branch by the
complex implicit-function theorem and proves persistence of both `Δ=0` and `Δₜ=0`.
`SingularJacobian.lean` supplies an explicit inverse for the generic fiber Jacobian under
`Δ_z ≠ 0` and `Δ_tt ≠ 0`. `MovingAlgebraicBranches.lean` now gives the direct source-level route
needed here: it proves that the moving Cayley sextic and reduced septic have the certified base
equations and Jacobian, constructs all 24 analytic branches, computes their derivatives as a
linear map of the rotation parameters, and derives the certified rotation-source vanishing from
first-order stationarity of Poincaré's singularity parameter. Thus the remaining source-level
task in §§102–103 is the substantive analytic proof of the rank-at-most-two bound, not another
finite computation or coordinate-identification layer.

## LeanCompCert trust boundary

The exact audit first found a rank-35 matrix over `Q(i)`. The formal certificate does not trust that
answer. Lean reconstructs the matrix from the ellipse coefficients, reduces Gaussian integers via
`i ↦ 12` in `ZMod 29`, and checks all entries of a proposed inverse in the kernel. The external
Python/SymPy script is therefore a certificate generator and cross-check only. The resulting
theorems contain no `native_decide` or externally admitted run result.

The merged Lean Pool classical restricted-three-body development is consumed as the pinned
`lean-pool` dependency ([PR #329][lean-pool-pr]). It supplies the restricted Hamiltonian,
homological equation, resonant disturbing average, joint eccentric-anomaly analyticity, and the
classical nonintegrability endpoint. Those results are useful infrastructure, but they do not
replace the complex two-variable Chapter VI construction. LeanCompCert is used for the large
finite polynomial and matrix identities in the §103 endgame and for the rational endpoint signs
isolating the concrete equation-(7) root at `D`; it cannot certify the infinite
convergence, local inverse, Weierstrass-preparation, or contour-cycle claims merely from a finite
coefficient cutoff.

## Sources

- Henri Poincaré, [*Les méthodes nouvelles de la mécanique céleste*, volume I, Chapter VI
  (§§90–103)][chapter-vi], 1892.
- Henri Poincaré, [facsimiles p. 290][page-290], [p. 323][page-323], and [p. 331][page-331].
- Henri Poincaré, §102 facsimiles [p. 326][page-326], [p. 327][page-327],
  [p. 328][page-328], and [p. 329][page-329].
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
[page-326]: https://fr.wikisource.org/wiki/Page:Henri_Poincar%C3%A9_-_Les_m%C3%A9thodes_nouvelles_de_la_m%C3%A9canique_c%C3%A9leste,_Tome_1,_1892.djvu/338
[page-327]: https://fr.wikisource.org/wiki/Page:Henri_Poincar%C3%A9_-_Les_m%C3%A9thodes_nouvelles_de_la_m%C3%A9canique_c%C3%A9leste,_Tome_1,_1892.djvu/339
[page-328]: https://fr.wikisource.org/wiki/Page:Henri_Poincar%C3%A9_-_Les_m%C3%A9thodes_nouvelles_de_la_m%C3%A9canique_c%C3%A9leste,_Tome_1,_1892.djvu/340
[page-329]: https://fr.wikisource.org/wiki/Page:Henri_Poincar%C3%A9_-_Les_m%C3%A9thodes_nouvelles_de_la_m%C3%A9canique_c%C3%A9leste,_Tome_1,_1892.djvu/341
[page-331]: https://fr.wikisource.org/wiki/Page:Henri_Poincar%C3%A9_-_Les_m%C3%A9thodes_nouvelles_de_la_m%C3%A9canique_c%C3%A9leste,_Tome_1,_1892.djvu/343
[poincare-1897]: https://www.numdam.org/item/JMPA_1897_5_3__203_0.pdf
[yagasaki-classical]: https://arxiv.org/abs/2111.11031
[yagasaki-fixed-mass]: https://arxiv.org/abs/2106.04925
[gao-ruppert]: https://www.ams.org/journals/mcom/2003-72-242/S0025-5718-02-01428-9/
[lean-pool-pr]: https://github.com/Vilin97/lean-pool/pull/329
