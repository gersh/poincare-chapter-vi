# Poincaré Chapter VI in Lean

This repository is a source-faithful reconstruction of the decisive argument in Chapter VI of
volume I of Poincaré's *Les méthodes nouvelles de la mécanique céleste*. It is intentionally
separate from Lean Pool while the historical proof is still research-level mathematics.

The classical planar restricted-three-body theorem is already formalized in
[Lean Pool PR #329](https://github.com/Vilin97/lean-pool/pull/329). This project pins that merge
commit and re-exports its final theorem, while pursuing Poincaré's original route through Fourier
coefficients, complex singularities, Darboux asymptotics, and projective curves.

## Current result

The classical pinch route in §§95--100 now has a concrete global-to-local spine at Poincaré's
point D. For the exact parameters `a=-1`, `c=3`, `τ=1/100`, and `β=2`, Lean reconstructs the
§97 branch calculation: D's branch reaches the collision-curve bifurcation B, its two descendants
meet `|z|=1` with `|x|<1`, and the other descendant has a unique `|z|=1` endpoint with `|x|>1`.
The proof uses exact rational inequalities, rigorous exponential bounds, calculus, and the
intermediate-value theorem; LeanCompCert supplies only the finite certificate isolating D's
cubic root. The two inverse-monotone descendants are explicit continuous paths in Poincaré's
`x^(1/3)` coordinate: Lean proves pointwise that both annihilate his literal collision factor,
carry the same actual complex `z` parameter, and coalesce at D. A winding-integral theorem then
proves that a smooth closed contour cannot avoid both opposite-side singularities through that
collision. More strongly, any `C²` closed contour family beginning at the unit circle and keeping
the literal transformed radicand nonzero throughout the radial continuation yields a direct
contradiction. The exact change back to the §94 variable,
`t=u exp((100/30003)((u^3)⁻¹-u^3))`, is now verified; its endpoint maps to the same anomaly pair
D as the local germ. The local base point is now defined to be this explicit global endpoint, so
the formerly possible cubic deck transformation is proved to be exactly `1`.
The explicit global endpoint has analytic order two and reaches the prepared local model. The
actual §94 numerator is analytic and nonzero at D. On one certified real rectangle the literal
source radicand is exactly `k+v²`, its complete numerator/Jacobian amplitude is `C¹`, and Lean
proves that the fixed symmetric middle-cycle integral divided by `-log k` tends to the nonzero
amplitude at D. The canonical local source root is defined from the literal radicand; Lean proves
it is exactly `sqrt(k+v²)` on that rectangle and proves the pointwise pullback identity from
Poincaré's source one-form to the evaluated Morse one-form, with no residual branch-sign premise.
The same compact local model now records that the derivative of the inverse Morse fiber is
exactly its named Jacobian at every point of the rectangle, supplying the velocity datum needed
for the path-level curve-integral change of variables. Lean now also constructs the literal
source-coordinate middle `Path` as the inverse-Morse image of the straight `[-L,L]` segment and
proves its continuity, exact endpoints, and exact derivative. The resulting source curve integral
is formally identical to the normal-form curve integral and hence to the logarithmic middle
integral. Thus the middle contribution is now the normalized curve integral of Poincaré's literal
principal source integrand, rather than only an identified quadratic model.
Lean also constructs a canonical global contour in Poincaré's `x^(1/3)` plane:
it starts at the literal unit circle, its radius stays strictly between the two explicit pole
radii before D, and its endpoint passes through their common collision. The normalized three-arc
theorem passes the local coefficient to the full contour once this topological family is lifted
to a compatible square-root sheet, given the required smooth local parameterization, and its two
outer arcs are proved regular; the general §98 Riemann-surface discussion is not represented as
complete.

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
  previously explicit uniform Lipschitz premise can now be derived from `C¹` regularity on a
  compact parameter-contour rectangle. The
  moving-center theorem exactly transports the affine local cycle
  `[h(k)-L,h(k)+L]` to the symmetric model and identifies the leading coefficient with the
  amplitude at that moving center. The
  prepared-factor module also constructs a compatible holomorphic complex square-root product and
  inverse whenever the quadratic and unit factors remain in a common slit-plane chart. It works
  on a joint parameter-contour domain such as `ℂ × ℂ`; continuity automatically constructs an open
  common chart from slit-plane values along the whole cycle family. The unit itself need not start
  in the principal chart: every holomorphic unit nonzero at the pinch gets a locally chosen square-
  root germ, with the negative-ray case handled by a sign rotation and compensating factor of `I`.
  This arbitrary unit germ combines with the quadratic branch and convex contour transport. The still-open transport is
  verifying those values for Poincaré's actual moving cycle and carrying that cycle to the
  controlled symmetric model. The non-affine transport theorem itself is now formalized: a
  relative `C²` path homotopy inside the branch chart preserves the prepared inverse-square-root
  contour integral, with closedness of the holomorphic one-form proved automatically. For convex
  branch subdomains Lean constructs the canonical pointwise affine path homotopy and proves its
  image stays in the domain; `C²` extensions of the endpoint paths automatically discharge the
  homotopy regularity condition. This yields a direct convex-domain theorem for the prepared
  inverse square-root branch.
- Poincaré's §94 function is now defined literally as
  `Φ(z)=(2πi)⁻¹∮F(z,t)dt`. For a finite Fourier table, Lean proves that the contour keeps exactly
  the affine frequency ray `(m₁,m₂)=(an+b,cn+d)` and, after an explicit choice `root^c=z`, that
  the result is the displayed Laurent polynomial `∑ Aₘ₁ₘ₂ zⁿ`. A second definition records the
  continued contour as an actual `Path`. Lean constructs the positively oriented unit-circle
  path, proves its curve integral equals the circle integral in the literal definition of `Φ`,
  and proves the normalized integral invariant under a checked relative `C²` homotopy inside a
  holomorphic branch domain. The remaining source task is to lift and deform that explicit path
  through the physical collision branch sheet, not to re-prove parametrization or abstract
  contour invariance.
- the formal-to-analytic identity boundary is explicit. If the actual radicand and its prepared
  expression are proved to realize the same convergent multivariable power series, Lean proves
  their equality on a neighborhood and proves the prepared unit remains nonzero there. Local
  analyticity then constructs the unit's holomorphic square-root germ without any global
  extension assumption. Lean builds the natural open punctured quadratic chart and verifies that
  its holomorphic inverse branch squares against the original radicand to one. Every fixed-
  parameter slice now feeds directly into the formalized `C²` contour-homotopy theorem; requiring
  the deformation domain's closure to stay in the chart derives the needed boundary continuity
  automatically. A
  LeanCompCert certificate may discharge large finite coefficient comparisons used in this
  construction, but no fixed finite jet is treated as convergence or equality of analytic germs.
- the exact source radicand at D now has an analytic moving fiber-critical center. Lean derives
  invertibility of the critical equation from the certified nonzero second fiber derivative and
  applies the complex implicit function theorem, yielding both the analytic center and the
  neighborhood-valid equation `∂ₜψ(z,h(z))=0`. This closes the translation-to-the-critical-point
  step before convergent preparation; it does not infer Weierstrass convergence from a finite
  certificate.
- translating by that center and subtracting its analytic critical value now produces a complete
  convergent two-variable germ that vanishes identically on the parameter axis. Its first fiber
  derivative vanishes on that axis near D, while its second fiber derivative at D is proved
  nonzero. Lean now proves a convergent two-variable Hadamard-division theorem, applies it twice,
  and obtains a jointly analytic unit `U(z,u)` with `ψ(z,u)=u²U(z,u)` near D. Comparison with the
  singular-fiber order-two factorization proves `U(D,0) ≠ 0`. This closes the local joint square
  division without treating any finite jet as a convergence proof. Lean also proves that every
  sufficiently nearby centered fiber has exact order two and its own convergent nonvanishing
  unit. For the singular fiber itself,
  a locally chosen holomorphic square root of the unit now yields an inverse-square-root branch
  holomorphic off the pinch and certified against the actual radicand. Lean further decomposes
  this actual branch as `A(0)/u + R(u)`, where `A(0) ≠ 0` and `R` is analytic at the pinch.
  On a small disk in the principal slit plane, Lean constructs a primitive of this actual branch
  of the form `A(0) log u + Q(u)`, with `Q′ = R`; thus the nonzero logarithmic singularity is now
  obtained at function level on the singular fiber. The canonical joint-unit candidate is also
  defined explicitly as the quotient by `u²`, filled in on the axis by `∂²ᵤψ/2`. Its exact
  factorization is proved everywhere and its analyticity is proved off the axis. Identifying this
  specifically normalized piecewise representative with the constructed analytic unit on the
  axis remains separate from the now-complete existence of a joint analytic square quotient.
  The joint quotient is packaged as a `ChapterVIConvergentPreparedGerm` with center and kappa
  identically zero, so the existing holomorphic inverse-branch and contour-transport API applies
  directly to the actual centered radicand. Its unit and automatically selected unit root agree
  as germs with the singular-fiber choices; on the sheet `sqrt(u²)=u`, the prepared inverse branch
  therefore has the previously constructed primitive `A(0) log u + Q(u)`.
  Lean now also integrates this identity along every straight local arc contained in the prepared
  chart and selected sheet, obtaining exactly
  `A(0)(log u₁-log u₀)+Q(u₁)-Q(u₀)` with `A(0)≠0`. Thus the remaining §100 gap is placement of
  Poincaré's continued source cycle and control of its complementary, nonlocal arcs—not the
  fundamental-theorem-of-calculus passage from the prepared branch to its logarithm.
- the subtraction used for joint Hadamard division is now explicitly undone. If `S²=U`, Lean
  constructs the analytic Morse coordinate `v=uS(z,u)`, proves its derivative at D is a continuous
  linear equivalence, constructs an analytic local inverse `(z,v)↦(z,u(z,v))`, and proves for the
  original translated radicand that
  `ψ(z,h(z)+u(z,v)) = ψ(z,h(z)) + v²` near D. Thus Poincaré's moving `k(z)` is the genuine analytic
  critical value `ψ(z,h(z))`; it is not replaced by zero. This supplies a convergent
  parameter-dependent quadratic normal form through a documented holomorphic coordinate change,
  without pretending that formal Weierstrass preparation alone proves convergence.
- the change of integration differential is now included as well. The inverse fiber coordinate
  has a jointly analytic Jacobian `∂u/∂v`, its value at D is the proved nonzero number `S(D,0)⁻¹`,
  and an arbitrary analytic source numerator pulls back to an analytic amplitude
  `θ(z,v)=a(z,t(z,v))∂u/∂v`. Lean proves the exact pointwise one-form identity
  `a(z,t) dt/root(ψ) = θ(z,v) dv/root(k(z)+v²)` with the compatible local square-root sheet kept
  explicit.
- transversality is now discharged for the concrete D point: along the external `z` direction,
  the two selected local inverse branches have nonzero derivatives, so the vanishing collision
  factor has nonzero `z` derivative; its companion factor is already known nonzero. Hence
  `k'(z_D)≠0`. Lean uses the complex inverse-function theorem to make `k` itself the local
  parameter, proving unconditionally that the literal source radicand is `k+v²` and transporting
  the complete analytic numerator/Jacobian amplitude into that chart.
- the numerator is no longer arbitrary at D. Lean constructs the selected local cubic root
  `z^(1/3)` and formalizes Poincaré's literal §94 monomial
  `massProduct * t^(ad-bc-1) * (z^(1/c))^(-d)`. For `a=-1,c=3` it proves this source numerator
  analytic and nonzero, pulls it into the `(k,v)` chart, and proves the resulting leading
  amplitude is nonzero. Its exact value contains the inverse Morse root, matching the defining
  identity on p. 323 and making explicit the apparent error in the subsequently printed formula.
- `ChapterVILocalVanishingCycle.lean` restricts that literal holomorphic amplitude to real
  positive critical values, extracts one compact rectangle on which the source radicand is
  exactly `k+v²`, and proves the normalized symmetric middle-cycle integral tends to its nonzero
  value at D. This is a calculation for Poincaré's actual source term, not only an abstract model.
- the §99 contour localization is now an exact path theorem. For
  `C₀=C₀' * C₀'' * C₀'''`, Lean splits the normalized integral into the two regular-arc
  contributions plus the middle pinched contribution. A source-facing theorem starts at the
  literal unit-circle `Φ` and performs the same split after a checked deformation. The
  deformation remains explicit data because it is precisely the global admissibility/sheet
  obligation that Poincaré only sketches.
- `ChapterVIThreeArcAsymptotic.lean` combines those results: if the checked source-sheet
  deformation identifies this middle cycle and the two complementary arc integrals are
  `o(-log k)`, the full continued principal integral has the same explicitly nonzero logarithmic
  coefficient. A finite limit of the complementary contribution automatically implies that
  lower-order condition, so ordinary continuity of the regular arcs is enough. Its continuation
  structure is the current global interface.
- `ChapterVIDRadialContour.lean` supplies the previously abstract global contour geometry for D.
  It proves the pole radii remain strictly ordered until collision, chooses the unique constant
  convex weight making the initial intermediate circle have radius one, constructs the resulting
  closed contour homotopy, proves it avoids both poles before the endpoint, and proves its final
  negative-real half-turn is exactly the collision lift.
- `ChapterVIDGlobalMorseBridge.lean` proves that the exact global `u -> t` map is
  holomorphic and unramified at D, composes it with the prepared Morse map, and constructs the
  canonical local inverse from the straight `v` segment back to the actual global `u` coordinate.
  Near D, the reconstructed `(z,t)` point is proved equal to `chapterVIDMorseSourcePoint`; this
  removes the former endpoint-only identification. `ChapterVIDFiberDerivative.lean` normalizes
  the local `t_D` directly to the explicit global endpoint, and
  `ChapterVIDGlobalLocalBridge.lean` proves the residual deck multiplier is `1`. The compiled
  polar cover below now supplies
  compatible square-root sheets on the two outer-arc rectangles. The remaining global work is to
  join those sheets to the full deforming three-arc family and match their signs to the middle
  Morse sheet.
- `ChapterVISquareRootSheet.lean` proves the general sheet theorem needed for those arcs: any
  continuous nonzero complex radicand on a simply connected parameter rectangle has a continuous
  square root with a prescribed base value. It also defines the precise LeanCompCert-facing
  continuum bridge. For the concrete D arcs the compiled target is the stronger and cheaper claim
  that the real part has a positive lower bound at every sample. A finite sample table, a certified
  covering radius, and a kernel-checked Lipschitz bound then imply nonvanishing everywhere and
  therefore produce the sheet. LeanCompCert is useful for the sample table; it does not replace
  the covering or analytic estimates. A final
  parametric-integration theorem proves that continuous outer-arc data then have finite endpoint
  limits, exactly the sufficient condition used by `ChapterVIThreeArcAsymptotic.lean`.
- `ChapterVIDCertificateContour.lean` replaces the unsafe naive linear interpolation by the
  explicit radius `q(s)^(1/6) * ((1-s) + s * (r_D / q_D^(1/6)))`. Lean proves its positivity, continuity,
  exact unit-circle start, and exact arrival at D. `ChapterVIDOuterArcs.lean` restricts its two
  regular quarters, proves the literal radicand is continuous there, and names the concrete
  nonvanishing-certificate types. The exploratory script
  `research/chapter_vi_outer_arc_scan.py` records why this radius was selected; its floating-point
  output is explicitly not accepted as proof.
- `ChapterVILeanCompCertRoots.lean` checks cubic- and sixth-root enclosures without evaluating a
  logarithm or fractional power numerically. Compiled signed-integer multiplication traces bound
  the cubes or sixth powers of dyadic endpoints, and a kernel proof turns those inequalities into
  root intervals.
- `ChapterVIDCriticalParameterInterval.lean` propagates the compiled isolation of the algebraic D
  root through the endpoint source modulus. A second compiled sign check narrows the root to a
  width of `10^-9`; a kernel-checked ten-term exponential estimate then encloses `q_D` tightly
  enough for the collision-end radial cells. Coarser qualitative bounds still use the elementary
  inequalities `1+E <= exp(E) <= 1/(1-E)`.
- `ChapterVIDRadialTrace.lean` and `ChapterVIDRadialCompiledGrid.lean` complete the radial input
  dimension: 17 cells at 20-bit precision and 233 primitive operations are flattened into one
  zero-returning compiled verdict. Every radial parameter now has certified enclosures for the
  exact source cubic root and the explicit contour radius. The generated table is reproducible
  with `research/generate_chapter_vi_radial_grid.py`; the generator is not part of the trust base.
- `ChapterVILeanCompCertPolarTrace.lean` preserves the exact polar dependency `u = r*v` and
  `v⁻¹ = conj(v)` for `‖v‖ = 1`. Its compiled trace encloses `u`, `u⁻¹`, `u³`, and `u⁻³` using only the
  existing signed-dyadic products and positive reciprocal checker. This avoids the large
  overestimate caused by independently inverting a rectangular enclosure of `u` near the D
  collision.
- `ChapterVILeanCompCertRadicandTrace.lean` carries those polar enclosures through both first-order
  exponential approximations, computes and checks the analytic remainder widths, and evaluates
  the two sparse Laurent factors. Its semantic theorem identifies the output with the literal
  root-coordinate radicand. A fixed-point feasibility scan finds a passing 20-bit mesh with 28
  cubically clustered radial cells and 32 quadratically clustered angular cells; the scan only
  chooses the mesh, while LeanCompCert must independently check the generated operations.
- `ChapterVIDRadialClusteredCompiledGrid.lean` and
  `ChapterVIDOuterArcUnitClusteredCompiledGrid.lean` turn that nonuniform mesh into exact
  continuum covers. Their generated dyadic tables and root/unit traces are checked in Lean's
  kernel; the generators remain outside the trust base.
- `ChapterVIDOuterArcPolarCompiledGrid.lean` combines the two axes into 1,792 interval cells. For
  every point of either outer-arc rectangle, Lean selects a cell, interprets its checked
  signed-integer operations, and proves the literal radicand has positive real part. It then
  proves nonvanishing and constructs the compatible global continuous square-root sheet.
- The large finite sweep is split into 56 radial-row artifacts of 13,824 integer claims each.
  `ChapterVIDOuterArcPolarAdmissibility.lean` kernel-checks every shard's 64-bit no-overflow
  conditions and exposes `CompiledRunVerdict`: the only remaining premise is that every
  reproducible CompCert artifact returned zero. `lake exe chapter-vi-polar-cert reference`
  performs the fast reference sweep; `emit SIDE INDEX OUTPUT.c` emits one self-checking restricted
  C shard; `check-shard SIDE INDEX` checks one shard; and `check-native` runs the full cached
  CompCert workflow when `ccomp` is installed.
  As LeanCompCert's trust model requires, a successful external run is an observation rather than
  a kernel proof of `Returns`; using it to construct `CompiledRunVerdict` requires an explicit
  attested or otherwise named run-admission boundary. The analytic and interval theorems remain
  conditional on that transparent premise and introduce no native-evaluation axiom themselves.
- `ChapterVIDOuterArcRegularity.lean` uses those compiled sheets to close the analytic regular-arc
  obligation. It pulls the literal principal numerator back through
  `t(u)=u exp((100/30003)(u^-3-u^3))`, formally differentiates this map and both rational quarter
  paths, and proves the resulting interval integral is the actual curve integral whenever the
  named cubic-root and square-root branches agree. Each outer integral—and their normalized
  sum—is continuous and therefore has a finite limit at D. The numerator agrees pointwise with
  `chapterVIPrincipalSourceNumerator` whenever the chosen global cubic-root lift agrees with the
  local source branch. The positive-real-part certificate further gives a canonical principal
  square-root sheet on each outer rectangle; Lean proves these sheets agree at their shared
  positive-real endpoint, eliminating the two arbitrary outer signs. Compatibility with the
  middle Morse chart remains; the chain rule and boundedness assertion for the two outer pieces
  do not.
- `ChapterVIPrincipalIntegrand.lean` now normalizes its local `z^(1/3)` inverse germ at the same
  positive real cube root used by the global root-coordinate path. Lean proves equality at D and
  eventual equality along the whole parameter path near D. Consequently the outer curve-integral
  theorem for the literal `chapterVIDPrincipalPhiIntegrand` needs only collision-square-root
  compatibility; the formerly separate cubic-root branch hypothesis is discharged automatically.
- `ChapterVIDRealCriticalParameter.lean` proves the exact real-axis property needed to identify
  the local critical-value parameter with Poincaré's global radial parameter. Conjugation
  symmetry of the selected Kepler inverses, critical center, and critical value is proved
  analytically. The orientation is reduced to exact rational formulas whose signs follow from
  the existing LeanCompCert-certified isolation interval for the concrete D root. Thus finite
  computation supplies only the root isolation and inequalities; exact realness remains a
  theorem of the analytic construction.
- `ChapterVIDCompiledThreeArcContinuation.lean` is the compiled-route global interface. Given
  the two regular connector arcs and the actual five-piece source-contour decomposition, it
  pulls back the compiled outer finite limit, combines it with the connector finite limit,
  automatically discharges the former broad `regular_sublog` premise, and proves that the full
  continuation has the explicit nonzero logarithmic coefficient. The local/global parameter
  synchronization, including exact source-parameter agreement on Poincaré's real affine ray,
  is now unconditional. The remaining regularity target is precisely the connector contribution
  and the geometric five-piece contour identity, rather than an unnamed global remainder.
- `ChapterVIConnectorRegularity.lean` and `ChapterVIFiveArcDecomposition.lean` isolate the next
  compiled boundary. For an affine connector, a finite nonvanishing cover now constructs its
  compatible square-root sheet and proves that its normalized integral has a finite collision
  limit. Lean also proves the exact path-level decomposition into the two outer quarters, two
  connectors, and the local pinched middle arc. What remains is to choose the two concrete
  source connectors, certify their literal radicands, and identify the resulting closed contour
  with the continued source cycle.
- `ChapterVIDMovingRootBridge.lean`, `ChapterVIDGlobalRootModel.lean`,
  `ChapterVIDRootConnectors.lean`, and `ChapterVIDConnectorIntegral.lean` now make that boundary
  concrete. Lean inverts Poincaré's exact `u -> t` map at D, shrinks the local Morse germ to a
  compact root-coordinate model, and defines the upper and lower affine connector rectangles
  with exact endpoints. Their outer boundaries are proved definitionally identical to the two
  compiled quarters. For either connector, finite nonvanishing covers for the root coordinate
  and literal radicand now construct the square-root sheet and prove the fully transformed
  connector integral has a finite limit. Producing those two concrete compiled covers per side,
  and matching the resulting continued sheet to the local Morse sheet, are the remaining
  connector tasks. The connector/outer sign is no longer a premise: each connector sheet is
  normalized at its outer endpoint, and connectedness proves agreement with the canonical outer
  sheet along the full shared boundary.
- The two regular quarters now use the exact rational unit-circle parametrization
  `((1-t²)+2ti)/(1+t²)` (and its `-i` rotation). Lean proves norm one, endpoints, quadrants, and
  continuity. Thus the compiled grid no longer needs interval implementations of `π`, `sin`, or
  `cos`.
- The exploratory scan was used only to choose the clustered mesh. The formal result uses
  interval enclosures on entire cells, so it needs neither floating-point trust nor a separate
  global Lipschitz estimate.
- Before compilation, Lean proves an exact sparse normal form for the literal radicand. Its two
  first-body Laurent coordinates are squared binomials, and the circular second-body coordinates
  are `y` and `y⁻¹`; the resulting checker expression needs only rational complex arithmetic and
  one complex exponential.
- `ChapterVIIntervalCertificate.lean` gives the compiled comparisons their analytic meaning.
  Signed dyadic multiplication is certified by eight integer corner inequalities, positive
  reciprocal by two cross-multiplied inequalities, and four real products assemble a rectangular
  complex product. `ChapterVILeanCompCertIntervalBridge.lean` serializes those conditions as
  sign-magnitude product claims. LeanCompCert's proved straight-line checker multiplies the
  magnitudes, performs the sign-aware comparisons, and counts failures; a compiled zero result
  now implies the real multiplication and reciprocal containment theorems. The dependency is
  pinned to the exact revision containing that checker. `ChapterVIDOuterArcInterval.lean` removes
  the remaining complex exponential
  from the machine calculation: on the coarse radius annulus, Mathlib's exponential remainder
  theorem encloses it by `1+x` plus an explicit norm error. The compiled sweep therefore performs
  only signed fixed-point arithmetic and checked outward widening.
- `ChapterVILeanCompCertBatch.lean` concatenates multiplication, positive-reciprocal, positivity,
  and explicit comparison conditions in a campaign. One zero-failure shard verdict reconstructs
  every individual interval certificate in that row; the full grid uses 56 bounded-size artifacts
  rather than one artifact per arithmetic operation.
- `ChapterVIUnitSquareGrid.lean` proves that the exact rational `(n+2) × (n+2)` sample grid covers
  `I × I` within product distance `1/(n+1)`. It also packages a checked grid table and a Lipschitz
  estimate into the positive-real-part cover consumed by the square-root theorem.
  The same file provides a stronger interval-cell interface: if each compiled row encloses its
  entire rational cell, the cells cover `I × I` directly and no global Lipschitz estimate is
  required. This is the preferred route for the full campaign.
- `ChapterVIDOuterArcUnitTrace.lean` reduces the exact rational quarter
  `((1-t²)+2ti)/(1+t²)` to five primitive interval operations and handles the final quarter by an
  exact `-i` rotation. `ChapterVIDOuterArcUnitCompiledGrid.lean` supplies all seventeen width-
  `1/16` cells at 16 binary fractional bits. One compiled verdict checks all 85 operations, and
  Lean proves that every `t ∈ I` is enclosed by a checked initial- and final-quarter rectangle.
- `ChapterVIDOuterArcCompiledSample.lean` instantiates the compiled route at the initial corner of
  the initial outer arc. Both sparse factors there are `-10201/10001`; a 16-bit dyadic enclosure
  and the signed LeanCompCert checker prove that their product lies in the strictly positive
  interval `[68182/65536, 68185/65536]`. This is a concrete first table row, not yet the full
  two-dimensional cover.
- `ChapterVILeanCompCertRealBridge.lean` proves the encoding theorem needed by the compiled route:
  LeanCompCert's all-integer fixed-point `rpow` bracket implies the corresponding outward-rounded
  interval for Mathlib's `Real.rpow`. The LeanCompCert dependency is pinned to a revision tested
  under both Lean 4.32.1 and this project's Lean 4.33 release candidate.

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
