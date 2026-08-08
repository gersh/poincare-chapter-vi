/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Fourier.AddCircle
import PoincareChapterVI.ChapterVIContour
import PoincareChapterVI.ChapterVIPhi
import PoincareChapterVI.ChapterVICycleDecomposition
import PoincareChapterVI.ChapterVIWindingObstruction
import PoincareChapterVI.ChapterVIDAdmissibility
import PoincareChapterVI.ChapterVIDRootCoordinates
import PoincareChapterVI.ChapterVIDRadialContour
import PoincareChapterVI.ChapterVIDCertificateContour
import PoincareChapterVI.ChapterVIDCriticalParameterInterval
import PoincareChapterVI.ChapterVIDRadialTrace
import PoincareChapterVI.ChapterVIDRadialCompiledGrid
import PoincareChapterVI.ChapterVIDGlobalLocalBridge
import PoincareChapterVI.ChapterVIDGlobalMorseBridge
import PoincareChapterVI.ChapterVISquareRootSheet
import PoincareChapterVI.ChapterVIUnitSquareGrid
import PoincareChapterVI.ChapterVIDOuterArcs
import PoincareChapterVI.ChapterVIIntervalCertificate
import PoincareChapterVI.ChapterVILeanCompCertIntervalBridge
import PoincareChapterVI.ChapterVILeanCompCertBatch
import PoincareChapterVI.ChapterVILeanCompCertComplexTrace
import PoincareChapterVI.ChapterVILeanCompCertPolarTrace
import PoincareChapterVI.ChapterVILeanCompCertRadicandTrace
import PoincareChapterVI.ChapterVILeanCompCertProposals
import PoincareChapterVI.ChapterVINonuniformGrid
import PoincareChapterVI.ChapterVIDRadialClusteredCompiledGrid
import PoincareChapterVI.ChapterVIDOuterArcUnitClusteredCompiledGrid
import PoincareChapterVI.ChapterVIDOuterArcPolarCompiledGrid
import PoincareChapterVI.ChapterVIDOuterArcPolarAdmissibility
import PoincareChapterVI.ChapterVIDOuterArcRegularity
import PoincareChapterVI.ChapterVILeanCompCertRoots
import PoincareChapterVI.ChapterVIDOuterArcInterval
import PoincareChapterVI.ChapterVIDOuterArcCompiledSample
import PoincareChapterVI.ChapterVIDOuterArcUnitTrace
import PoincareChapterVI.ChapterVIDOuterArcUnitCompiledCell
import PoincareChapterVI.ChapterVIDOuterArcUnitCompiledGrid
import PoincareChapterVI.ChapterVILeanCompCertRealBridge
import PoincareChapterVI.ChapterVIContourTransport
import PoincareChapterVI.ChapterVIComplexBranch
import PoincareChapterVI.ChapterVICurveAlgebra
import PoincareChapterVI.ChapterVIDarboux
import PoincareChapterVI.ChapterVIDarbouxSpectrum
import PoincareChapterVI.ChapterVIDarbouxTransfer
import PoincareChapterVI.ChapterVIJacobian
import PoincareChapterVI.ChapterVILatticeReduction
import PoincareChapterVI.ChapterVIPinchModel
import PoincareChapterVI.ChapterVILocalVanishingCycle
import PoincareChapterVI.ChapterVIThreeArcAsymptotic
import PoincareChapterVI.Section103.Certificate
import PoincareChapterVI.Section103.Geometry
import PoincareChapterVI.ChapterVISingularityAlgebra
import PoincareChapterVI.ChapterVISourceCoordinates
import PoincareChapterVI.ChapterVIDoubleZero
import PoincareChapterVI.ChapterVIDCandidate
import PoincareChapterVI.ChapterVIDFiberDerivative
import PoincareChapterVI.ChapterVIAnalyticCriticalCenter
import PoincareChapterVI.ChapterVIAnalyticCentering
import PoincareChapterVI.ChapterVISection102DarbouxTransfer
import PoincareChapterVI.Section103.Ruppert
import PoincareChapterVI.Section103.RuppertCertificate
import PoincareChapterVI.Section103.RuppertKernel
import PoincareChapterVI.Section103.RuppertBounds
import PoincareChapterVI.Section103.RuppertNormalization
import PoincareChapterVI.ChapterVIWeierstrass
import PoincareChapterVI.ChapterVIAnalyticPreparation
import PoincareChapterVI.ChapterVIJointPreparation
import PoincareChapterVI.ChapterVIParametricMorse
import PoincareChapterVI.ChapterVIMorseAmplitude
import PoincareChapterVI.ChapterVICriticalParameter
import PoincareChapterVI.ChapterVIDTransversality
import PoincareChapterVI.ChapterVIPrincipalIntegrand
import LeanPool.PoincareThreeBody.LocalEnergyLeaf

/-!
# Poincaré, *Méthodes nouvelles*, Volume I, Chapter VI

This file isolates the interface between the restricted problem formalized in this project and
the decisive complex-singularity calculation in Chapter VI of Poincaré's first volume.

## Passage-by-passage status

* §90 (pp. 269--272): Poincaré writes the full three-body Hamiltonian as `F₀ + μ F₁` and isolates
  the mutual-distance part of `F₁`.  The restricted analogue is
  `hasDerivAt_hamiltonian_mass_zero`, with the resulting coefficient
  `firstMassPerturbation`; this is a different Hamiltonian, not a verification of Poincaré's
  displayed full-problem formula.
* §91--92 (pp. 272--278): Poincaré discusses osculating coordinates and the first homological
  equation.  `firstHomologicalEquation_of_poissonBracket_zero` verifies the parameter
  product-rule step, while
  `IsFirstIntegralFamily.firstHomologicalEquation_on_resonantKeplerOrbit` and the averaging
  lemmas verify its restricted resonant-orbit consequence.  The coordinate comparison in §92
  is not formalized.
* §93 (pp. 278--280): Poincaré recalls Darboux's one-variable coefficient estimates.
  `eventually_ne_zero_of_tendsto_div_one` verifies their elementary eventual-nonvanishing
  consequence, but the complex-analytic coefficient estimates themselves are not formalized.
* §94 (pp. 280--285): Poincaré reduces coefficients of a Fourier series in two mean anomalies,
  along an integral ray, to Laurent coefficients of a one-variable contour integral `Phi(z)`.
  `chapterVIShearExponent_eq_iff_mem_affineRay`,
  `chapterVIFiniteFourierPolynomial_substitution`, and
  `chapterVIReducedCoefficient_eq_sum_affineRay` verify the exact reduction for finite Fourier
  polynomials. `chapterVIReducedCoefficient_circleIntegral` verifies Poincaré's normalized-circle
  contour extraction for the resulting finite Laurent polynomial.
  `chapterVI_tsum_eq_iterated_shear_sum` extends the lattice reindexing to arbitrary summable
  double series. `chapterVI_laurentSeries_circleCoefficient` proves the infinite Laurent-series
  contour extraction under a weighted absolute-summability hypothesis on the chosen circle.
  Establishing that hypothesis and the corresponding annulus of holomorphic convergence for
  Poincaré's actual perturbing function `Phi(z)` is not yet formalized. The restricted problem has
  only one moving Kepler ellipse; the definition
  `chapterVIOrientationCoefficient` below records the corresponding one-circle coefficient, but
  is not itself Poincaré's full two-variable perturbing function.
* §95 (pp. 285--287): Poincaré characterizes candidate singularities of `Phi` by pinching two
  moving singularities of its contour integrand. Lean now proves invariance of the winding
  integral under a free closed smooth contour homotopy and the resulting obstruction: poles whose
  translated contours initially have winding numbers one and zero cannot coalesce while one
  smoothly transported closed contour avoids both. Identifying a complete physical source-sheet
  lift with the translated homotopies remains the global interface to this theorem.
* §96 (pp. 287--295): `chapterVI_planarKeplerCoordinate_mul_conjugate` verifies
  `ξ ξ₀ = (1 - sin φ cos u)²`. `chapterVI_planarSourceRadicand_exp` identifies Poincaré's
  concrete Laurent radicand with `(ξ - βη)(ξ₀ - β₀η₀)`, and
  `chapterVI_planarSourceRadicand_eq_cleared` proves that clearing `2xy` gives exactly the
  product of his two collision cubics. The two-eccentricity half-angle theorems verify the
  general equations (3) and (4), including the circular specialization used in §96, while the first- and
  second-kind reciprocal theorems verify the inversion symmetries of equations (7)--(10) and of
  the singularity parameter `z`. The printed equation (10) has `x² - 1`; its derivation and the
  claimed reciprocal symmetry instead require `x² + 1`, which the formalization makes explicit.
  `ChapterVISourceCoordinates.lean` then verifies the exact exponential Kepler substitution,
  constructs its local analytic inverse away from Poincaré's first-kind critical equation, proves
  `z = exp(ial) exp(icl')`, and constructs a convergent power series for the literal §99
  radicand `ψ(z,t)` after `exp(il) = tᶜ`. `ChapterVIDoubleZero.lean` splits this literal germ
  as the two source collision factors and reduces exact fiber order two to the four finite checks
  `H=0`, `H'=0`, `H''≠0`, and `H₀≠0` at the selected source point.
* §97--98 (pp. 295--314): Poincaré decides by contour deformation which candidate singularities
  are admissible. For the concrete planar D instance, Lean now reconstructs the decisive §97
  calculation rather than assuming the drawing: it proves the exact collision-curve intersection
  at B, differentiates the branch modulus, isolates the unique exterior `|z|=1` endpoint with
  `-100<x<-1`, and uses exact exponential bounds plus the intermediate-value theorem to construct
  both descendants through B with `|x|<1`. Thus D has exactly the terminal inside/inside/outside
  configuration asserted by Poincaré. The winding obstruction formalizes why opposite sides force
  a genuine pinch. `ChapterVIDRadialContour.lean` constructs the corresponding contour family:
  a circle whose radius begins at one, remains strictly between the two pole radii, and reaches
  their common negative-real collision at its final half-turn. Poincaré's general square-root
  sheet continuation in §98 remains a sketch in the source and is not claimed here.
* §99--101 (pp. 314--325): local singular expansions and Darboux asymptotics show that high-order
  resonant coefficients do not vanish. `exists_chapterVI_weierstrassNormalForm` applies
  Weierstrass preparation to a bivariate formal series whose parameter specialization has order
  two and obtains Poincaré's exact `((t - h)² + k) ψ₁` factorization, with `ψ₁` a unit and `h`,
  `k` vanishing at the singular parameter. Before that formal preparation step,
  `exists_chapterVID_analyticCriticalCenter` applies the complex implicit function theorem to the
  exact convergent source radicand and constructs Poincaré's analytic moving fiber-critical center
  through D. `ChapterVIAnalyticCentering.lean` then translates to this moving center, subtracts
  the analytic critical value, and proves that the resulting convergent germ vanishes together
  with its first fiber derivative along the parameter axis while retaining a nonzero second
  fiber derivative at D. A convergent two-variable Hadamard-division theorem is then applied
  twice, producing a jointly analytic nonvanishing unit in the exact factorization
  `ψ(z,u)=u²U(z,u)`. On the singular fiber it constructs a holomorphic punctured inverse-
  square-root branch proved correct for the actual centered radicand. That actual branch is
  further decomposed as a nonzero constant divided by the centered fiber coordinate plus a
  function analytic at the pinch, the local simple-pole statement underlying Poincaré's
  logarithmic contour term. On the principal slit plane, the actual branch is then integrated to
  a nonzero constant times `log u` plus a holomorphic regular primitive. A canonical two-variable
  unit candidate is the literal quotient by `u²`, filled in on the centered axis by half the
  second fiber derivative. Its exact factorization holds everywhere and it is analytic off the
  axis; matching that specifically normalized piecewise function with the constructed analytic
  unit on the axis is a separate normalization question.
  `ChapterVIJointPreparation.lean` packages the resulting factorization in the convergent
  prepared-germ interface. Its joint inverse branch is holomorphic and certified against the
  actual centered radicand; its unit and unit root restrict to the singular-fiber choices, and on
  the sheet `sqrt(u²)=u` the prepared branch inherits the explicit nonzero logarithmic primitive.
  `hasSum_chapterVILogSingularityCoefficient` verifies the
  logarithmic Taylor expansion used in §100, and
  `chapterVI_darbouxAsymptotic_of_logarithmicLeadingTerm` connects its exact coefficients plus a
  little-oh remainder to Poincaré's leading Darboux model.
  `eventually_coefficient_ne_zero_of_chapterVI_darboux_asymptotic` then verifies asymptotics-to-
  nonvanishing. `tendsto_successiveCoefficientRatio_of_chapterVI_darboux_asymptotic` proves the
  p. 326 recovery formula `Dₙ₊₁/Dₙ → z₀⁻¹`, and
  `chapterVI_darbouxSingularityInverse_unique` proves that an isolated leading singularity is
  determined by its coefficient sequence. `ChapterVIDarbouxSpectrum.lean` replaces the ratio
  argument when equally dominant singularities coexist: a finite exponential annihilator and
  Vandermonde inverse recover the normalized unit-circle spectrum modulo a vanishing error.
  `ChapterVIDarbouxTransfer.lean` proves the intervening coefficient step for finitely many
  constant leading logarithms: equality of analytic germs determines their Taylor coefficients,
  and a remainder analytic on a strictly larger disk vanishes after the common Darboux
  normalization. The radius is explicit, so the recovered bases are `R z₀⁻¹`, rather than
  silently assuming `R = 1`. It also treats every finite amplitude jet
  `(1-z/z₀)^k log(1-z/z₀)`: all positive-order terms are proved subleading, so only the value of
  the analytic log amplitude at the singularity contributes to the recovered spectrum. Tannery's
  theorem extends this transfer to an infinite analytic-amplitude series under an explicit
  summable uniform coefficient bound. More source-faithfully, factoring a varying amplitude as
  `G(z₀) + (1-z/z₀)H(z)` reduces its tail to convolution with an exact `O(1/n²)` kernel; Lean
  derives the required weighted summability directly when `H` is analytic on a disk larger than
  the boundary circle. The holomorphic divided difference `dslope` now constructs `H` and its
  scalar power series automatically from any amplitude analytic beyond the boundary point.
  A scalar Cauchy-product theorem and analytic-germ uniqueness derive the full varying-log
  coefficient sequence from the function-level decomposition. Establishing that decomposition
  and larger-disk analyticity for the actual contour amplitude, uniformly in the orbital
  parameters, remains open.
  `tendsto_chapterVI_quadraticPinch_sub_log` evaluates the real symmetric prepared quadratic model
  and proves its exact logarithmic asymptotic.
  `tendsto_chapterVI_weightedQuadraticPinch_div_neg_log` further proves that a continuous
  Lipschitz amplitude changes the leading logarithmic coefficient by exactly its value at the
  pinch; its varying part has a uniformly bounded integral. The vector-valued parameter-dependent
  theorem `tendsto_chapterVI_parametricQuadraticPinch_inv_neg_log_smul` applies in particular to
  complex amplitudes, permits the center value to vary continuously with the pinch parameter, and
  uses one uniform Lipschitz bound. The stronger
  `tendsto_chapterVI_parametricQuadraticPinch_inv_neg_log_smul_of_contDiffOn` derives that bound
  from `C¹` regularity on a compact parameter-contour rectangle. The moving-center theorem exactly translates the interval
  `[h(k)-L,h(k)+L]` to the symmetric model and recovers the amplitude at the moving collision.
  `ChapterVIComplexBranch.lean` constructs a compatible
  holomorphic square-root product and its inverse on any domain where the prepared quadratic and
  unit factors lie in the complex slit plane. This construction is joint in the parameter and
  contour coordinate, and continuity automatically promotes slit-plane values on an entire cycle
  family to an open common branch chart containing it. More generally, every holomorphic unit
  nonzero at the base point now receives an automatically chosen local square-root germ, including
  the sign-rotated case when its value lies on the principal branch cut; this germ combines with
  the quadratic branch and the contour-transport theorem.
  `ChapterVIAnalyticPreparation.lean` proves the analytic identity layer: two actual functions
  realizing the same convergent multivariable series agree near the pinch, and a convergent
  prepared germ therefore has the completed-square factorization with a locally nonzero unit.
  It then constructs the unit root from local analyticity alone, builds an open punctured
  quadratic branch chart, and proves that the resulting holomorphic inverse branch is an actual
  inverse square root of the original radicand on an open neighbourhood of the pinch. Fixed
  parameter slices inherit an open holomorphic chart and feed directly into the checked `C²`
  contour-homotopy theorem, provided the deformation domain's closure remains in that chart.
  Constructing those convergent realizations from the nested formal Weierstrass factors, and
  proving the source cycle's factor values lie in one such chart, remain open.
  `ChapterVIContourTransport.lean` proves genuine non-affine contour invariance for
  a relative `C²` path homotopy in that chart: for a holomorphic scalar integrand Lean constructs
  the closed one-form and discharges Stokes' theorem automatically. On a convex branch subdomain,
  the canonical pointwise affine path homotopy is constructed and proved to remain inside the
  domain; `C²` extensions of the two paths automatically give the required `C²` homotopy. A direct
  theorem applies this to the prepared inverse square root, including the arbitrary unit-root
  germ. `ChapterVICycleDecomposition.lean` formalizes Poincaré's exact split
  `C₀=C₀' * C₀'' * C₀'''` and, after a checked deformation from the literal unit circle, proves
  that `Phi` is the sum of the two regular-arc terms and the middle pinch term.
  `ChapterVIPrincipalIntegrand.lean` constructs D's local cubic root of `z`, defines the actual
  §94 monomial numerator, and proves its Morse-chart leading amplitude is nonzero.
  `ChapterVILocalVanishingCycle.lean` extracts a compact real rectangle on which the literal
  source radicand is exactly `k+v²` and proves the actual symmetric middle integral divided by
  `-log k` tends to that nonzero amplitude. It now constructs the inverse-Morse middle path in
  the literal source coordinate, proves its derivative and the exact curve-integral pullback, and
  identifies that logarithmic integral with Poincaré's principal source one-form on this path.
  `ChapterVIThreeArcAsymptotic.lean` proves that the full
  contour inherits this coefficient once the source-sheet three-arc realization is constructed
  and its two regular arcs are `o(-log k)`. `ChapterVIDGlobalMorseBridge.lean` proves that the
  explicit global `u=x^(1/3)` coordinate is locally analytically equivalent at D to the same
  Morse `v` coordinate and that its inverse reconstructs the exact local Morse source point. The
  local `t_D` is normalized to the explicit global contour endpoint, so the formerly necessary
  cubic deck multiplier is formally equal to one.
  `ChapterVISquareRootSheet.lean` reduces the compatible outer-arc square-root sheet to
  nonvanishing on a compact parameter rectangle and supplies a finite-cover/Lipschitz interface
  for discharging that fact with a large LeanCompCert sample certificate. The concrete compiled
  polar bounds now construct both outer sheets, and `ChapterVIDOuterArcRegularity.lean` pulls the
  literal principal numerator through Poincare's `u` coordinate, proves the exact transformed
  contour velocity by the chain rule, identifies the interval expression with the original curve
  integral under named branch-agreement hypotheses, and proves that the resulting normalized sum
  has a finite limit at D. Because the certificate places both outer radicands in the positive
  real half-plane, it also selects the canonical principal square root and proves the two outer
  sheets agree at their common positive-real endpoint. The local `z^(1/3)` germ is likewise now
  normalized to the global positive-real parameter lift, and Lean proves they agree on an entire
  neighborhood of D. Thus only the collision square-root sheet must be matched to the middle
  Morse sheet before identifying the resulting three-piece cycle with the continued source
  contour.
* §102--103 (pp. 325--334): Poincaré uses the dependence of complex singular points on orbital
  parameters and an algebraic-curve intersection count to contradict an additional uniform
  integral. `chapterVI_scaledSingularities_jacobian_det` verifies the exact Jacobian rescaling
  factor `-z₁⁶ / ζ⁷` in §102. It does not establish the analytic dependence or rank hypotheses.
  `chapterVI_scaledSingularities_jacobian_det_eq_zero_iff` proves the ensuing equivalence between
  dependence of the six scaled singularities and dependence of their five ratios.
  `ChapterVISection102.lean` verifies the block-determinant step on p. 329 and reduces the
  §102--103 contradiction to Darboux coefficient data factoring through two essential orientation
  coordinates. Both an isolated leading singularity and a locally uniform finite spectrum of
  equally dominant singularities are supported; the latter uses continuity to prevent local
  root-label permutation. `ChapterVISection102DarbouxTransfer.lean` converts either a finite
  logarithmic germ decomposition, finite log-amplitude jets, a full analytic amplitude with
  explicit Tannery control, or the regular-factor analytic form above with a larger-disk analytic
  remainder into that spectrum interface and hence the §103 contradiction. Its most source-facing
  interface starts from the actual function-level varying-log germ and derives every coefficient
  and tail estimate internally. The recovery theorems
  derive the rank-at-most-two assertion for the canonical differential of all constructed
  second-kind roots. In §103,
  `chapterVI_curvePolynomial_derivative` verifies the corrected identity
  `x ∂P/∂x = 2 ∑ VᵢUᵢ + 2P`; the printing has `+P`, which agrees only after restricting to `P=0`.
  `chapterVI_cubicDerivativeCurveEquation_reduction` verifies the subsequent reduction modulo
  `P`, and `chapterVI_reducedCurve_totalDegree_le_seven` proves its degree-seven estimate under
  the displayed degree bounds. `chapterVISection103_derivedRotationMinor_eq` reconstructs exact
  coefficient rows from two genuine rational spatial Kepler ellipses and three infinitesimal
  relative rotations. `chapterVISection103_no_projective_infinitesimal_rotation` uses their
  nonzero determinant and the `y²z⁴` coefficient to prove that no nonzero such rotation preserves
  `P`, even up to rescaling, at that configuration. `chapterVI_ruppertExpression_factor` verifies
  the differential identity
  by which a proper factor of `P` would produce a vector in the kernel of Ruppert's absolute-
  irreducibility matrix. `chapterVIComplexRuppertMatrix_mulVec_eq_zero` reconstructs the exact
  `64 × 35` matrix from the ellipse coefficients and proves full column rank: LeanCompCert's
  `verified_decide` checks a `35 × 35` inverse modulo 29, and the proof lifts the nonzero minor
  through Gaussian integers to `ℂ`. The bounded-degree Ruppert argument proves absolute
  irreducibility. Exact localized normal forms prove the exceptional multiplicities `2`, `8`,
  and `8`. A bidirectional affine-elimination certificate then proves directly that the remaining
  affine common-zero locus consists of exactly 24 distinct non-origin points; its separability
  check is a mod-53 coefficient-list Bézout certificate transported to Mathlib polynomials.
  `Section103/MovingAlgebraicBranches.lean` constructs analytic branches of the genuine moving
  sextic and reduced septic at all 24 finite points. It computes their singularity derivatives
  as a linear map of the three rotation parameters; the §102 rank bound supplies a nonzero common
  stationary direction, from which Lean derives the deformation equation and completes the final
  contradiction using the compiled LeanCompCert restriction certificate.
  The theorems at the end of this file instead connect coefficient nonvanishing to the restricted
  dense Poincaré set and thence to the project's modified nonintegrability proof.

The unconditional theorem `nonintegrability_of_collisionBand` uses a modification: a real
logarithmic collision blow-up and analytic continuation replace §§93--101.  Consequently this
project proves a restricted nonintegrability theorem, but it does not yet verify Poincaré's
original complex-singularity/Darboux calculations in Chapter VI.
-/

noncomputable section

open AddCircle
open scoped Real

namespace PoincareChapterVI

open LeanPool.PoincareThreeBody

open Asymptotics Filter

/-- The orientation-dependent resonant average, descended to the circle of period `2 * pi`.

This is the one-angle restricted-problem counterpart of the functions whose two-angle Fourier
coefficients Poincaré studies in §94. -/
def chapterVIResonantAverageOnCircle (p q : ℕ) (eccentricity : ℝ) :
    AddCircle (2 * Real.pi) → ℂ :=
  let average : ℝ → ℝ := resonantDisturbingAverage p q eccentricity
  let periodic : Function.Periodic average (2 * Real.pi) :=
    fun orientation ↦ resonantDisturbingAverage_add_orientation_two_pi
      p q eccentricity orientation
  fun orientation ↦ (periodic.lift orientation : ℂ)

/-- The `n`th Fourier coefficient of the restricted resonant average.

Poincaré's §94 instead begins with coefficients `A_(m₁,m₂)` of the full perturbing function in
two mean anomalies and studies the ray `(m₁,m₂) = (a n + b, c n + d)`. -/
def chapterVIOrientationCoefficient
    (p q : ℕ) (eccentricity : ℝ) (n : ℤ) : ℂ :=
  haveI : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  fourierCoeff (chapterVIResonantAverageOnCircle p q eccentricity) n

/-- A nonzero nonconstant Fourier mode prevents the resonant average from being constant. -/
theorem exists_values_ne_of_chapterVIOrientationCoefficient_ne_zero
    {p q : ℕ} {eccentricity : ℝ} {n : ℤ}
    (hn : n ≠ 0)
    (hcoefficient : chapterVIOrientationCoefficient p q eccentricity n ≠ 0) :
    ∃ phaseA phaseB : ℝ,
      resonantDisturbingAverage p q eccentricity phaseA ≠
        resonantDisturbingAverage p q eccentricity phaseB := by
  by_contra hvalues
  push Not at hvalues
  have hcircle : chapterVIResonantAverageOnCircle p q eccentricity =
      fun _ ↦ (resonantDisturbingAverage p q eccentricity 0 : ℂ) := by
    funext orientation
    induction orientation using QuotientAddGroup.induction_on'
    simp only [chapterVIResonantAverageOnCircle]
    exact_mod_cast hvalues _ 0
  apply hcoefficient
  unfold chapterVIOrientationCoefficient
  rw [hcircle]
  let _ : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  change fourierCoeff
      (fun _ : AddCircle (2 * Real.pi) ↦
        (resonantDisturbingAverage p q eccentricity 0 : ℂ)) n = 0
  let value : ℂ := resonantDisturbingAverage p q eccentricity 0
  have hfunction : (fun _ : AddCircle (2 * Real.pi) ↦ value) =
      fun orientation ↦ value * fourier 0 orientation := by
    funext orientation
    simp
  rw [hfunction, fourierCoeff.const_mul]
  rw [congrFun (fourierCoeff_fourier (T := 2 * Real.pi) 0) n]
  simp [hn]

/-- A restricted-problem analogue of the output that §§93--101 of Chapter VI are intended to
establish: at every positive rational resonance with a nonempty admissible eccentricity range,
one admissible parameter has a nonzero nonconstant Fourier mode.

This predicate deliberately packages the missing Darboux calculation as a hypothesis.  It is not
asserted as an axiom and the unconditional proof in this project does not use it. -/
def HasChapterVIDarbouxNonvanishing : Prop :=
  ∀ p q : ℕ, 0 < p → 0 < q →
    (admissibleResonantEccentricitySet p q).Nonempty →
    ∃ eccentricity ∈ admissibleResonantEccentricitySet p q,
      ∃ n : ℤ, n ≠ 0 ∧
        chapterVIOrientationCoefficient p q eccentricity n ≠ 0

/-- A stronger, explicitly asymptotic form of the missing restricted Darboux calculation.  It
matches Poincaré's pattern of an exponential singularity factor times a nonzero inverse-power
leading term. -/
def HasChapterVIDarbouxAsymptotics : Prop :=
  ∀ p q : ℕ, 0 < p → 0 < q →
    (admissibleResonantEccentricitySet p q).Nonempty →
    ∃ eccentricity ∈ admissibleResonantEccentricitySet p q,
      ∃ singularityInverse leadingCoefficient : ℂ,
        singularityInverse ≠ 0 ∧ leadingCoefficient ≠ 0 ∧
          (fun index : ℕ ↦ chapterVIOrientationCoefficient p q eccentricity (index + 1))
            ~[atTop]
          chapterVILeadingDarbouxModel singularityInverse leadingCoefficient

/-- The formalized Darboux consequence: a nonzero leading asymptotic model supplies an actual
nonzero Fourier mode on every admissible resonance. -/
theorem hasChapterVIDarbouxNonvanishing_of_asymptotics
    (hasymptotics : HasChapterVIDarbouxAsymptotics) :
    HasChapterVIDarbouxNonvanishing := by
  intro p q hp hq hnonempty
  rcases hasymptotics p q hp hq hnonempty with
    ⟨eccentricity, heccentricity, singularityInverse, leadingCoefficient,
      hsingularity, hleading, hasymptotic⟩
  have hnonzero :=
    eventually_coefficient_ne_zero_of_chapterVI_darboux_asymptotic
      hsingularity hleading hasymptotic
  rcases hnonzero.exists with ⟨index, hindex⟩
  refine ⟨eccentricity, heccentricity, index + 1, ?_, hindex⟩
  exact_mod_cast Nat.succ_ne_zero index

/-- The Darboux nonvanishing output supplies a separating pair of orientations at one admissible
eccentricity on every rational resonance. -/
theorem hasSeparatingResonantAverages_of_chapterVI
    (hDarboux : HasChapterVIDarbouxNonvanishing) :
    HasSeparatingResonantAverages := by
  intro p q hp hq hnonempty
  rcases hDarboux p q hp hq hnonempty with
    ⟨eccentricity, heccentricity, n, hn, hcoefficient⟩
  rcases exists_values_ne_of_chapterVIOrientationCoefficient_ne_zero
      hn hcoefficient with ⟨phaseA, phaseB, hvalues⟩
  exact ⟨phaseA, phaseB, eccentricity, heccentricity, sub_ne_zero.mpr hvalues⟩

/-- Restricted replacement for the final step of Chapter VI: the Darboux output makes the
restricted classical Poincaré set dense.  This is not Poincaré's singularity-parameter count in
§§102--103. -/
theorem hasDenseClassicalPoincareSet_of_chapterVI
    (hDarboux : HasChapterVIDarbouxNonvanishing) :
    HasDenseClassicalPoincareSet :=
  hasDenseClassicalPoincareSet_of_analytic_separation
    (hasAnalyticSeparatingResonantAverages_of_separation
      (hasSeparatingResonantAverages_of_chapterVI hDarboux))

/-- Conditional Chapter VI route to the project's restricted nonintegrability statement.

The hypothesis is precisely where the still-unformalized complex singularity classification,
admissibility argument, local expansions, and Darboux estimates of §§93--101 enter. -/
theorem nonintegrability_of_chapterVI
    (hDarboux : HasChapterVIDarbouxNonvanishing) :
    ¬∃ δ : ℝ, 0 < δ ∧ ∃ F : ℝ → PhaseSpace → ℝ,
      IsJointlyAnalytic δ F ∧ IsFirstIntegralFamily δ F ∧
        IsIndependentSomewhere δ F :=
  nonintegrability_of_denseClassicalPoincareSet
    (hasDenseClassicalPoincareSet_of_chapterVI hDarboux)

/-- Conditional restricted nonintegrability directly from Darboux-type coefficient asymptotics. -/
theorem nonintegrability_of_chapterVI_asymptotics
    (hasymptotics : HasChapterVIDarbouxAsymptotics) :
    ¬∃ δ : ℝ, 0 < δ ∧ ∃ F : ℝ → PhaseSpace → ℝ,
      IsJointlyAnalytic δ F ∧ IsFirstIntegralFamily δ F ∧
        IsIndependentSomewhere δ F :=
  nonintegrability_of_chapterVI
    (hasChapterVIDarbouxNonvanishing_of_asymptotics hasymptotics)

end PoincareChapterVI
