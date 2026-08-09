# Research map for Poincaré's Chapter VI

Status: standalone source-reconstruction research.  The finite connector arithmetic and the
printed differential-rank chain are now closed, but the two source-level implications identified
below are not consequences of those computations.

Large connector batches now have a concrete LeanCompCert receipt interface in
`ChapterVILeanCompCertAttestation.lean`: Lean derives the emitted C artifact from the same batch
used by the semantic theorem, and a bound receipt yields the required zero verdict through the
explicit `RunAdmission` trust boundary. The passing `1024 / 261` reference campaign is now literal
Lean data and is split into 64 independently compiled 32-cell bulk artifacts plus two exact
endpoint-anchor artifacts. Generated kernel proofs check each shard's 64-bit admissibility,
receipts reconstruct every interval certificate,
and the results assemble into the factor-bulk continuation interface without a monolithic kernel
evaluation. A second 41-shard campaign checks the literal affine-connector derivative on 492
terminal cells. Its artifacts include the line-map operations, and Lean turns every accepted row
into a `HasDerivAt` theorem plus strict derivative positivity for the actual model connector.
This resolves compiled-result ingestion and removes the old fixed-cutoff premise, but not the
scale-dependent endpoint issue: 30 endpoint-adjacent cells still contain the double zero because
the Morse length is selected noncomputably. The obstruction is now checked symbolically as well:
the literal first-factor derivative at the collapsed D endpoint is exactly zero, by reduction to
the certified cubic equation defining D. The exact second derivative and its differentiation
theorem are now formalized too. A compiled width-`10⁻¹²` root isolation check, followed by exact
reduction modulo the cubic, proves that its real part is strictly negative. A sound compiled
completion therefore needs to retain this second-order scale-normalized data or supply a
constructive quantitative Morse witness; a receipt alone cannot supply the missing analytic
relation.

That second-order finite campaign is now present. `f''(u)Δ²` has the certified negative
imaginary orientation on all 21 omitted initial cells and positive imaginary orientation on all
9 omitted final cells. Ten three-cell LeanCompCert artifacts pass with zero failed claims, and
Lean identifies each enclosed value with the derivative of the actual path derivative. What
remains is the analytic join to a first-derivative anchor at the selected inverse-Morse endpoint;
the compiled curvature cannot determine that noncomputable endpoint relation by itself.

The calculus portion of that join is now formalized in
`ChapterVIDConnectorFactorTerminal.lean`. The 30 closed mesh cells cover their two complete real
terminal intervals, their certified curvature makes the first path derivative strictly
antitone/monotone on the respective sides, and a nonnegative endpoint derivative implies strict
positivity at every punctured terminal point. `ChapterVIDEndpointOrientation.lean` proves the
global coordinate's exact derivative is positive real and proves reciprocal strict-derivative
formulas for both inverse maps. It now also closes the phase calculation: the certified negative
second derivative of the literal root-coordinate radicand is transported through Poincare's exact
`u -> t` map, proving that the centered Hadamard unit and the prepared Weierstrass unit are
negative real at D. Consequently the selected Morse square root is positive imaginary and the
inverse-Morse contour derivative points strictly downward at D. That phase is now propagated
uniformly after shrinking the `(k,v)` model: the zero section maps to the real root axis, every
selected real fiber is strictly downward-oriented, and the two local endpoints have strict
upper/lower half-plane signs. `ChapterVIDEndpointAnchor.lean` now makes the remaining connection
to the literal affine-connector derivative. It computes both zero-length endpoint derivatives,
proves them strictly positive from the certified collision curvature and the exact D geometry,
then selects a small positive Morse length and shrinks the critical-value interval by continuity.
This constructs both endpoint anchors internally. The ten LeanCompCert curvature shards therefore
prove strict first-factor path-derivative positivity throughout all 30 punctured terminal cells.
Those same shards also check a positive-real separation for the companion factor throughout the
closed terminal intervals, and Lean reconstructs the literal model factor from each accepted row.
`ChapterVIDConnectorFactorMonotonicity.lean` now joins all 492 first-order rows, all 30 curvature
rows, the endpoint anchors, and the direct factor boundary rows. The literal first-factor
imaginary part is strictly increasing throughout each complete 261-cell collar, its outer collar
boundary has the expected imaginary sign, and the companion factor remains in the positive real
half-plane. Hence the first factor has at most one real-axis crossing in a collar. The analytic
selection complements rather than replaces the compiled campaign: a receipt alone cannot encode
the noncomputable inverse-Morse scale. `ChapterVIDConnectorFactorCrossing.lean` now makes the
remaining scale-aware statement an explicit `PositiveCrossingCertificate`: at a collar point
where the first factor has zero imaginary part, its real part is nonnegative. It proves that this
single statement, connector nonvanishing, and the three existing compiled campaigns construct a
continuous factor-root sheet with the correct outer and local values. The two crossing statements
therefore imply the seam-compatible connector pair and the complete five-piece logarithmic limit.
`CompiledCrossingData` and `CompiledCrossingRunVerdict` expose the exact LeanCompCert computation
and receipt interface. The same file now supplies a stronger preferred target,
`OrientedRealDerivativeCertificate`. If the first factor's real derivative is nonpositive on the
initial collar and nonnegative on the final collar, Lean's derivative monotonicity theorem compares
every collar point with the exact positive Morse endpoint and proves both crossing statements.
The inverse-Morse selection now proves the missing strict real derivative signs at the two local
endpoints as exact analytic theorems. `NonnegativeRealCurvatureCertificate` records a sufficient
calculus reduction from those anchors and has an optional compiled interface, but the actual
endpoint curvature is also scale-sensitive, so no passing campaign of that stronger shape is
claimed. The practical target is now the explicit
`CompiledNormalizedRealDerivativeData`: Lean divides the oriented derivative by the strictly
positive scale `L + distance²`, proves that a nonnegative normalized certificate recovers the raw
derivative orientation, and feeds the result directly into the completed seam theorem. The
strengthened `exists_chapterVIDAnchoredConnectorModel_bounded` also selects the analytic model
below any prescribed positive upper bounds for `L` and `κ`, enforces `κ ≤ L²`, and bounds the
actual relative cubic-root parameter perturbation by `L²`. The exact base-centered derivative is
now reconstructed by a 24-subtrace LeanCompCert evaluator. A second compiled trace evaluates the
factored relative exponent `A(u)-A(D)` and obtains `exp(A(u)-A(D))-1` from mathlib's rigorous
complex Taylor remainder, so no transcendental floating-point answer is trusted. The finite-cell
table layer proves that checked arithmetic plus one terminal oriented sign per cell yields the
normalized derivative certificate accepted by the seam theorem. The inverse-Morse big-O estimate
is now turned into a selector below every requested endpoint radius. At any fixed-point precision,
both `local-D` and the relative parameter-root perturbation therefore inhabit the static raw-unit
box `[-1,1]×[-1,1]`. Each cell derives its coordinate and direction from the checked identity
`u-D=(local-D)+distance*(outer-local)`, so those are no longer independent semantic premises.
The already certified terminal radial box supplies the required `outer-local` enclosure. Checked
subtraces derive the collision reciprocal and powers, and proved fixed boxes supply `Y(D)` and the
rational coefficients. The resulting executable 261-cell campaign contains 42,282 operations per
side. All arithmetic claims pass; exactly 171 endpoint-adjacent cells per side fail only the final
oriented-sign claim (initial indices 90--260 and final 0--170). Lean now proves that
`(local-D)/v` tends to the exact purely imaginary, downward inverse-Morse derivative and is
eventually inside an explicit cone with half its imaginary margin. The selector now retains this
cone at the actual positive critical parameter, so Lean obtains both strict endpoint half-plane
signs and a lower imaginary margin proportional to `L`. Retaining only that sign in a one-sided
absolute raw-unit box does not improve the 171 failing cells because zero remains in the closed
box. An injectable LeanCompCert diagnostic isolates the numerical issue: raw imaginary
displacement `1024` fails 94 cells per side, whereas every tested value from `2048` through
`262144` passes all 84,564 operations. The fixed trace therefore works at a resolved absolute
scale but cannot be uniform as the noncomputable `L` shrinks. This is why the completed campaign
below uses a genuinely homogeneous certificate in `(local-D)/L` and endpoint distance relative
to `L`.

Testing boxes obtained by multiplying the proved normalized endpoint rectangle by four sample
dyadic lengths (`1/16`, `1/32`, `1/64`, and `1/128`) makes the diagnosis sharper: all 261 cells on
both sides fail. The already compiled second-derivative rectangles also straddle zero in their
real components on all 30 terminal cells. Consequently neither finite scale bands nor the old
curvature shortcut can close the real-orientation claim; the compiled expression itself must
retain the homogeneous dependencies.

The center and radius of the scale-free endpoint box are now finite-certified rather than left
opaque. `ChapterVIDMorseSlopeCompiled.lean` proves
`(du/dv|_D)^2 = 2/R″(D)`, evaluates the literal `R″(D)` with a 168-operation LeanCompCert batch,
and obtains `-120 ≤ Re R″(D) ≤ -95` with zero failed claims. The exact phase selects the negative
square root, giving `-3/20 < Im(du/dv|_D) < -1/8`. Combining this interval with the retained cone
proves that the true normalized endpoint displacement lies in the fixed dyadic rectangle
`[-83887,83887]×[-262144,-65536]` at precision 20, uniformly in the selected `L`. This closes the
finite input problem for `(local-D)/L`. The same module now proves the exact reconstruction
`local-D=(±L)q` before rounding and places
`(ζ/ζ_D-1)/L²` in the fixed unit square from the selector's proved norm inequality. Thus both
primitive moving inputs are scale-free. The selector additionally retains the outer endpoint
motion as `O(L²)`; Lean places its normalized quotient in the same unit square and proves the
exact connector-vector decomposition into the collapsed direction, an `L²` outer perturbation,
and the `Lq` local perturbation. `ChapterVIDHomogeneousDerivative.lean` preserves those
dependencies through the exact identity
`orientedDerivative = L * endpointCoefficient + distance² * distanceCoefficient`.
`ChapterVIDHomogeneousCompiledTable.lean` evaluates the two scale-free coefficients on 160
distance cells per side at precision 20, including checked coordinate powers and the rigorous
relative-exponential remainder. The 320 rows form 32 ten-row LeanCompCert artifacts. Generated
kernel theorems prove each artifact's 64-bit admissibility and all signed claims; LeanCompCert's
verified denotation theorem supplies an unconditional reference run verdict. The semantic proof
then reconstructs strict positivity of both literal coefficients. It follows in Lean that both
collars have the required oriented real derivative and hence the positive crossing certificates.
The table result is connected directly to the existing seam-compatible five-piece logarithmic
limit. Hash-bound receipts remain available only for optional independently compiled reruns of
this table.

The same kernel-side closure is now applied to the pre-existing outer-polar, connector-factor,
first-derivative, and second-derivative tables.  Their exported reference verdicts no longer take
external execution or receipt premises.  The receipt APIs remain available for reproducible
CompCert reruns, but the trusted reference seam theorem uses only kernel-proved comparisons.

This note separates three questions that are easy to conflate:

1. What is proved in Chapter VI of volume I of *Les méthodes nouvelles de la mécanique
   céleste*?
2. Which individual reductions have been checked in this Lean repository?
3. What would be required for a faithful modern proof of the decisive argument?

The primary text is [Chapter VI, §§90–103][chapter-vi]. The dependency invoked in §102 is
Chapter V, no. 85: equation (13 bis) is on [p. 247][page-247], and its Jacobian/parameter-count
conclusion is on [p. 248][page-248]. For §102 itself, see [p. 325][page-325], [p. 326][page-326],
[p. 327][page-327], [p. 328][page-328], and [p. 329][page-329].
The page-level facsimiles are linked below where the printed formula matters.

## Bottom line

The repository does **not** formalize Poincaré's complete Chapter VI proof. It now proves that
two literal source obligations are misstated, rather than merely absent from Lean:

- no. 85 prints `-ζH=S`, but substituting `Dλ=Bλζ^λ` into (13) requires `H=-ζS` to obtain
  (13 bis); `chapterVNo85_printed_normalization_counterexample` checks a rational counterexample
  to the printed normalization, and the corrected cancellation is formalized;
- near D, the pole that began outside has crossed strictly inside the literal unit circle.
  `eventually_chapterVID_no_fixedUnitCircleContinuation` uses winding invariance to prove that a
  pole-avoiding continuation cannot keep using that fixed circle. The historical object must be
  a jointly moving lifted cycle, not the literal unit-circle integral re-evaluated at the current
  parameter.

After those corrections, the central source-level analytic and geometric steps still open are:

- transporting the original §94 source-sheet integration cycle over the final `27/2744` of the
  chosen radial parameter and deforming it into the now-certified near-D five-piece family while
  avoiding every moving zero. The preceding interval is no longer open:
  `ChapterVIDGlobalLiftedPrefix.lean` gives a principal lift of the ordinary angular
  root-coordinate circle from zero through the exact cutoff `2717/2744`.
  `ChapterVIDCircleReparametrization.lean` now closes the initial link: the exact `u -> t` map on
  the unit circle is the strictly increasing angular warp
  `θ - (200/30003) sin(3θ)`, and the certified initial principal sheet is transported through
  its continuous inverse. `ChapterVIDRadialTailReduction.lean` reduces the remaining tail to a
  nonnegative endpoint-circle table and a strictly negative radial-derivative table.
  `ChapterVIDRadialTailDerivative.lean` and `ChapterVIDRadialTailPathDerivative.lean` prove the
  exact total derivative, specialize it to the sixth-root radial path, and turn a negative table
  into strict antitonicity. The signed-dyadic trace and six-row cover are implemented in
  `ChapterVILeanCompCertRadialTailDerivativeTrace.lean` and
  `ChapterVIDRadialTailDerivativeCompiledGrid.lean`, but no unconditional verdict is claimed:
  the first direct 20-bit layout loses radial dependency across large cancelling Laurent terms.
  `ChapterVILeanCompCertHighOrderAnomalyTrace.lean` proves a degree-five Taylor enclosure with
  `|a|^6/512` remainder and the derivative trace now uses it. The failed verdict is essentially
  unchanged, which rules out the exponential remainder as the main loss. A cell-centered radial
  Taylor model (or equivalent dependency-preserving factorization), the endpoint table, and the
  deformation to the five-piece family are still required;
- proving which candidate singularities pinch the integration cycle and are genuine rather than
  apparent;
- controlling the complementary regular arcs during the long-range transport;
- deriving the logarithmic decomposition from the contour pinch and proving that its amplitudes
  extend analytically beyond the common boundary circle;
- deriving the standard Fourier multiplier, orbital differentiation/interchange, resonance, and
  independence fields from a full Chapter V uniform-integral model and identifying those
  coefficient observables with the singularity ratios recovered from the actual contour. Lean
  now extracts the six coefficient equations from one torus-level identity, then performs the
  resonance elimination, corrected (13 bis) construction, and rank chain `6 → 5 → 4 → 2`.

The formerly separate connector nonvanishing item is closed on the domain actually used by the
continuation.  `ChapterVIDConnectorFullBulk.lean` proves the literal radicand nonzero on both
`[0,1) × [0,1]` connector rectangles by combining the existing full two-dimensional bulk rows
with the homogeneous endpoint argument fiber by fiber, and constructs continuous square-root
sheets there by covering-space lifting.

The terminal branch-identification item is also closed. `ChapterVIDJointLiftedContour.lean`
constructs one closed near-D source contour from the five certified pieces, proves the literal
radicand nonzero on its positive half-open parameter family, constructs a principal-base-
normalized square-root sheet, and proves its restriction is exactly every compiled outer,
connector, and positive Morse branch. This is the terminal part of the continuation, not the
still-unprinted global homotopy beginning at the §94 circle.

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
| §95 | Candidate singularities arise when moving singularities of the integrand obstruct contour deformation | `ChapterVIContourTransport.lean` proves equality for relative and free closed `C²` homotopies and derives closedness automatically. `ChapterVIWindingObstruction.lean` evaluates the unit-circle winding integral inside and outside and proves that a smoothly transported closed contour cannot avoid two translated poles with winding numbers one and zero as they coalesce. `ChapterVIDRadialContour.lean` applies this to the concrete branches: the outside pole eventually lies strictly inside the fixed circle, so the old fixed-unit-circle continuation premise is impossible. `ChapterVIPhi.lean` supplies the initial literal unit circle, while `ChapterVICycleDecomposition.lean` splits a deformed `C₀=C₀' * C₀'' * C₀'''` exactly. `ChapterVIDJointLiftedContour.lean` constructs and lifts the terminal near-D five-piece source cycle and identifies all five branches | Construct the preceding **jointly moving lifted cycle** from the §94 circle into that terminal family in the complement of all source-radicand zeros, and control the complementary regular arcs |
| §96 | Algebraic equations for candidate singularities | `ChapterVISingularityAlgebra.lean` identifies the concrete Laurent radicand with `(ξ-βη)(ξ₀-β₀η₀)`, proves that clearing `2xy` gives the product of the general collision cubics, and verifies both-eccentricity half-angle reductions. `ChapterVISourceCoordinates.lean` constructs the literal analytic germ `ψ(z,t)`. `ChapterVIDCandidate.lean` and `ChapterVIDFiberDerivative.lean` certify a concrete point `D`, prove both inverse-coordinate ODEs on a neighborhood, and prove the complete literal radicand has fiber order exactly two | Extend the concrete instance to Poincaré's parameter region and connect it to the global admissibility deformation |
| §§97–98 | Decide which candidates are admissible and which singularity lies on the boundary of the Laurent annulus | The concrete descendants, common parameter, transformed literal-radicand zeros, winding obstruction, and a pole-weighted radial contour are proved. `ChapterVIDRadialContour.lean` proves that the exact `u ↦ t` map carries the `u`-unit circle to the literal §94 `t`-unit circle and constructs an explicit homotopy of parametrizations at a fixed parameter. It also proves why re-evaluating this same circle near D is not the analytic continuation: the initially outside pole has crossed inside. A second certificate-friendly contour uses the explicit sixth-root radius `q(s)^(1/6)(r_D/q_D^(1/6))^s`; its endpoint geometry and compiled positive-real-part certificates on both outer quarters are proved. `ChapterVIDGlobalMorseBridge.lean` handles the local germ. `ChapterVIDRealCriticalParameter.lean` proves exact local/global real-ray synchronization. `ChapterVIDRootConnectors.lean` defines both concrete connector rectangles. The full bulk and homogeneous tables prove literal-radicand nonvanishing on every positive critical-value fiber, and Lean constructs square-root sheets on both half-open rectangles. `ChapterVIDConnectorIntegral.lean` proves that each transformed connector integral is literally the source curve integral. `ChapterVIDJointLiftedContour.lean` assembles the terminal closed source cycle, lifts one joint square-root sheet, and identifies every certified piece. | Lift the original §94 germ through the earlier parameter range into the near-D family in the complement of all moving zeros; prove uniform regular-remainder control |
| §99 | Localize at a pinch and prepare the double zero as `ψ=((t-h)²+k)ψ₁` | The exact source germ, double-zero checks, analytic center, joint division, Morse coordinate, critical-value coordinate, transversality, and literal nonzero §94 amplitude are formalized. `ChapterVILocalVanishingCycle.lean` extracts one rectangle where the literal radicand is exactly `k+v²` and proves that the actual symmetric middle integral has the nonzero `-log k` coefficient. `ChapterVICycleDecomposition.lean` proves exact three-arc localization, and `ChapterVIThreeArcAsymptotic.lean` transfers the local coefficient to the full contour. The compiled outer quarters and connectors now assemble with compatible sheets into the five-piece logarithmic limit; `ChapterVIDJointLiftedContour.lean` proves that these are restrictions of one terminal joint sheet. | Join the analytic continuation of the original §94 source germ to this terminal family and control the complementary regular arcs |
| §100 | Integrate the prepared local model to obtain `Φ₂+Φ₃ log(z-z₀)` and apply Darboux | `ChapterVIJointPreparation.lean` proves the exact logarithmic primitive on the singular fiber. `ChapterVILocalVanishingCycle.lean` proves the parameter-dependent logarithmic asymptotic for the literal principal source term, and `ChapterVIThreeArcAsymptotic.lean` isolates the exact global continuation/regular-remainder premise. `ChapterVIDarbouxTransfer.lean` and `ChapterVIDarbouxSpectrum.lean` prove the downstream coefficient machinery. | Discharge the source-sheet and regular-remainder premise, then prove the larger-disk analyticity needed by Darboux uniformly in orbital parameters |
| §101 | Astronomical example (the Pallas inequality) | Not formalized | Optional for nonintegrability; relevant only if the project also verifies the numerical application |
| §102 | A uniform integral would constrain the singular points to depend on too few parameters | `ChapterVIJacobian.lean` verifies the displayed rescaling. `ChapterVNo85FourierExtraction.lean` applies actual Haar Fourier coefficients on the two-torus to one pointwise first-order Poisson identity and derives the head plus five tail equations. `ChapterVISection102.lean` imposes resonance (12 bis), derives equation (13), corrects the printed normalization in (13 bis), proves the characteristic direction is nonzero from independence, and obtains the exact rank chain `6 → 5 → 4 → 2`, ending in the certified §103 contradiction. It also proves by an exact rational counterexample that the printed `-ζH=S` cannot yield (13 bis); the required relation is `H=-ζS`. `ChapterVISection102DarbouxTransfer.lean` keeps the common radius explicit (`R z₀⁻¹`), supports constant, finite-jet, Tannery-controlled, and regular-factor analytic amplitudes, and prevents root-label permutation. | Derive the torus model's multiplier/interchange, resonance, and independence fields from the full source Hamiltonian and putative uniform integral, then identify the six rescaled Fourier coefficients with the singularity observables of the actual continued contour, including common-radius and regular-factor estimates |
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
  on collision curve (3), and proves the companion factor nonzero.
- `ChapterVIDAdmissibility.lean`: the concrete real-analytic reconstruction of Poincaré's figure
  4 at D. It proves the exact (3)/(4) intersection at B, differentiates the literal branch
  modulus, constructs both `|z|=1` descendants through B with `|x|<1`, and isolates the unique
  other descendant with `|x|>1`. The resulting inside/inside/outside terminal configuration is a
  theorem, not a plot or floating-point computation. It additionally inverts the two monotone
  branches against their common parameter, constructs their continuous negative-real cubic
  lifts, proves the two source singularity parameters agree at every time, and verifies that both
  paths annihilate Poincaré's literal factor `H=ξ-βη` before coalescing at D.
- `ChapterVIDRootCoordinates.lean`: Poincaré's exact §97 change of variable from
  `u=x^(1/3)` to the original contour variable
  `t=u exp((100/30003)((u^3)⁻¹-u^3))`. It proves `t³` is the first Kepler exponential,
  reconstructs the second anomaly as `y=ζt`, and verifies pointwise that the synchronized inside
  and outside paths are zeros of the literal transformed source radicand with source parameter
  `z=ζ³`. It then proves the source-facing admissibility conclusion: no smooth closed contour
  family beginning at the unit circle can keep this radicand nonzero all the way to D.
- `ChapterVIDGlobalLocalBridge.lean`: identifies the global branch parameter at D with the local
  `z_D`, maps the explicit global collision endpoint back to the original `(z,t)` anomaly pair,
  and constructs the cube-root deck multiplier relating it to the local germ's selected lift. It
  proves the explicit endpoint has fiber order exactly two and reaches the local prepared model
  whose logarithmic coefficient is nonzero.
- `ChapterVIDGlobalMorseBridge.lean`: strengthens the endpoint bridge to an analytic-germ
  correspondence. It proves the deck-transformed global `u -> t` coordinate is unramified at D,
  shows its Morse fiber derivative is nonzero, constructs the local inverse `v -> u`, and proves
  that pulling a straight Morse segment back through this inverse reconstructs exactly the same
  centered inverse-Morse point and original `(z,t)` source point near D.
- `ChapterVISquareRootSheet.lean`: packages the covering-space lift through `w -> w^2` and fixes
  the sheet by a chosen base root. Its `ChapterVIFiniteNonvanishingCover` is the compiled-
  certificate boundary: finitely many sample lower bounds plus a cover and Lipschitz estimate
  prove continuum nonvanishing and construct the sheet without adding an analytic axiom. The D
  contour also has a stronger `ChapterVIFinitePositiveRealPartCover`; this lets the compiled
  artifact check one signed real lower bound per sample instead of a complex norm. It also
  proves that continuous numerator, sheet, and path-velocity data make each outer-arc integral
  converge to a finite endpoint value.
- `ChapterVIDCertificateContour.lean` and `ChapterVIDOuterArcs.lean`: define the explicit
  sixth-root-scaled contour selected for finite verification, prove its exact endpoints, and
  specialize the finite nonvanishing interface to the two compact outer quarters. Their exact
  rational parametrization `((1-t²)+2ti)/(1+t²)` removes trigonometric constants from the compiled
  grid; norm one, endpoints, and the relevant quadrants are proved algebraically. The companion
  Python scan is exploratory only; the formal milestone is the future LeanCompCert-checked
  positive-real-part certificate, not the sampled minimum. An exact source-identity theorem also
  rewrites the literal radicand to the sparse checker formula with squared binomials, circular
  coordinates `y,y⁻¹`, rational complex arithmetic, and one complex exponential.
- `ChapterVIIntervalCertificate.lean` formalizes the semantic side of the compiled interval
  artifact: eight signed-integer corner comparisons certify each dyadic multiplication, two
  cross-products certify a positive reciprocal, and four real certificates produce a complex
  rectangle product. `ChapterVIDOuterArcInterval.lean` proves that the coordinate-change
  exponential is within its first-order polynomial by an explicit norm error throughout the
  coarse contour annulus. Thus no unverified floating-point or transcendental evaluation is part
  of the eventual compiled sample sweep.
- `ChapterVILeanCompCertRealBridge.lean`: closes one concrete encoding gap in that certificate.
  It turns LeanCompCert's natural-number power inequalities into genuine `Real.rpow` bounds, so a
  compiled fixed-point result can be used by the analytic contour proof without treating the
  integer scale convention as an assumption.
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
  particular axis normalization with the constructed joint analytic unit remains open; the
  terminal source cycle is placed, while its long-range transport from §94 remains open.
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
  radicand in `(k,v)` coordinates equals `k+v²`.
- `ChapterVIDTransversality.lean`: discharges that premise exactly. It differentiates the selected
  cubic-root and circular-Kepler inverse branches along the external parameter, proves the
  vanishing collision factor has derivative `-2y'(z_D)≠0`, multiplies by the nonzero companion
  factor, and obtains `deriv k z_D≠0`. The resulting source chart and `k+v²` identity are exported
  without hypotheses.
- `ChapterVIPrincipalIntegrand.lean`: constructs a local cubic-root determination of `z` at D,
  defines Poincaré's actual monomial numerator
  `massProduct * t^(ad-bc-1) * (z^(1/c))^(-d)`, and proves it is analytic and nonzero. It pulls
  that numerator through the unconditional Morse chart and proves the leading amplitude is
  nonzero, with the exact inverse-Morse-root factor dictated by Poincaré's preceding identity.
- `ChapterVICycleDecomposition.lean`: formalizes `C₀=C₀' * C₀'' * C₀'''`, proves the normalized
  curve integral splits into regular plus pinched terms, and combines this with a checked
  deformation from the literal §94 unit circle. It intentionally does not manufacture the
  missing global branch-sheet deformation.
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
  recovery bridges, and the contradiction with the compiled §103 restriction certificate. It
  also proves Poincare's full intermediate parameter count: rank at most four for the five ratios
  plus injective first-kind recovery of the two eccentricities implies rank at most two for the
  entire orientation differential; a literal four-coordinate factorization is therefore
  impossible for the certified family.
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
  the automatically selected arbitrary-unit root germ. It also treats free homotopies of closed
  loops, where the two side integrals in Stokes' boundary formula cancel.
- `ChapterVIWindingObstruction.lean`: normalized winding integrals for closed paths, exact values
  one and zero for poles inside and outside the unit circle, invariance under a free closed smooth
  pole-avoiding homotopy, a construction translating an actual moving contour by an actual moving
  pole, and the no-coalescence theorem for two opposite-side poles.
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

This remains the conceptual bottleneck globally, but the local coefficient and terminal lifted
cycle are no longer open.
`ChapterVILocalVanishingCycle.lean` applies the parametric pinch theorem to Poincaré's literal
principal numerator/Jacobian on a rectangle where the actual source radicand is exactly `k+v²`;
the coefficient is proved nonzero. `ChapterVIThreeArcAsymptotic.lean` proves that this is also the
full contour coefficient once the source-sheet three-arc realization and an `o(-log k)` estimate
for the two outer arcs are supplied; it also proves that any finite regular-arc limit implies this
estimate automatically. `ChapterVIDJointLiftedContour.lean` constructs the near-D five-piece
source-sheet family and proves all its branch restrictions. The missing theorem must join the §94
circle to this family by a relative source-sheet deformation and prove continuity of the exposed
regular remainder along the full route.

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
2. Instantiate `ChapterVIFiniteNonvanishingCover` for the two explicit outer-arc rectangles. Use
   the pinned LeanCompCert array/loop route for the large finite sample table, while proving the
   covering and Lipschitz/error bounds in Lean. Then construct the square-root sheets and prove
   the two outer integrals have finite limits (hence are `o(-log k)`).
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
first-order stationarity of Poincaré's singularity parameter. `ChapterVISection102.lean`
additionally performs the finite Chapter V algebra that was formerly hidden inside the reference
to no. 85: from the pre-resonance first-order Fourier equation, resonance (12 bis), and
independence it derives the corrected common-kernel equation and rank five. The printed
normalization `-ζH=S` is false for `Dλ=Bλζ^λ`; Lean checks an exact rational counterexample,
while `H=-ζS` gives the asserted cancellation. `ChapterVNo85FourierExtraction.lean` now applies
the actual two-torus Haar Fourier functional to one function-level first-order Poisson equation,
so the head and five tail equations are derived together rather than assumed separately. Thus
the remaining source-level task in §§102–103 is to derive its standard multiplier/interchange,
resonance, and independence fields from a full analytic uniform-integral model and identify the
resulting six coefficients with the common-radius singularity observables of the continued
contour. The analytic coefficient extraction and finite algebra from those hypotheses to the
rank-at-most-two bound are now kernel checked.

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
- Henri Poincaré, Chapter V no. 85 facsimiles [p. 247][page-247] and [p. 248][page-248].
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
[page-247]: https://fr.wikisource.org/wiki/Page:Henri_Poincar%C3%A9_-_Les_m%C3%A9thodes_nouvelles_de_la_m%C3%A9canique_c%C3%A9leste,_Tome_1,_1892.djvu/259
[page-248]: https://fr.wikisource.org/wiki/Page:Henri_Poincar%C3%A9_-_Les_m%C3%A9thodes_nouvelles_de_la_m%C3%A9canique_c%C3%A9leste,_Tome_1,_1892.djvu/260
[page-325]: https://fr.wikisource.org/wiki/Page:Henri_Poincar%C3%A9_-_Les_m%C3%A9thodes_nouvelles_de_la_m%C3%A9canique_c%C3%A9leste,_Tome_1,_1892.djvu/337
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
