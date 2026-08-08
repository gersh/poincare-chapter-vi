/-
Copyright (c) 2026 Gershon Bialer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gershon Bialer
-/

import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Complex.Basic

/-!
# Conjugation symmetry of a local analytic inverse

A finite interval certificate can establish inequalities, but it cannot establish that a complex
analytic branch is *exactly* real on the real axis.  This file isolates the ordinary analytic
argument needed for that step.  If a local map commutes with complex conjugation and its base
point is real, then the canonical inverse-function-theorem branch also commutes with conjugation
near the corresponding value.
-/

noncomputable section

open Complex Filter Topology
open scoped ComplexConjugate

namespace PoincareChapterVI

/-- Conjugation symmetry passes from a locally invertible holomorphic map to the canonical local
inverse supplied by the inverse function theorem.  The conclusion is an identity on a full
complex neighborhood, not merely on its real slice. -/
theorem eventually_conj_localInverse_conj
    {f : ℂ → ℂ} {f' a : ℂ}
    (hf : HasStrictDerivAt f f' a) (hf' : f' ≠ 0)
    (ha : conj a = a)
    (hconj : ∀ᶠ z in nhds a, f (conj z) = conj (f z)) :
    ∀ᶠ y in nhds (f a),
      conj (hf.localInverse f f' a hf' (conj y)) =
        hf.localInverse f f' a hf' y := by
  let inverse := hf.localInverse f f' a hf'
  let reflected : ℂ → ℂ := fun y ↦ conj (inverse (conj y))
  have hconjTendsto : Tendsto conj (nhds a) (nhds a) := by
    have hc := Complex.continuous_conj.continuousAt (x := a)
    change Tendsto conj (nhds a) (nhds (conj a)) at hc
    rw [ha] at hc
    exact hc
  have hleft : ∀ᶠ z in nhds a, inverse (f z) = z := by
    simpa only [inverse] using hf.eventually_left_inverse hf'
  have hleftReflected : ∀ᶠ z in nhds a, inverse (f (conj z)) = conj z :=
    hconjTendsto.eventually hleft
  have hreflectedLeft : ∀ᶠ z in nhds a, reflected (f z) = z := by
    filter_upwards [hconj, hleftReflected] with z hzconj hzleft
    unfold reflected
    rw [← hzconj, hzleft]
    simp
  simpa only [reflected, inverse] using
    hf.hasStrictFDerivAt_equiv hf'
      |>.localInverse_unique hreflectedLeft

/-- On real inputs near a real target value, a conjugation-symmetric local inverse is exactly
real.  This is the bridge used before any finite certificate is asked to prove an orientation
inequality. -/
theorem eventually_localInverse_ofReal_im_eq_zero
    {f : ℂ → ℂ} {f' a : ℂ}
    (hf : HasStrictDerivAt f f' a) (hf' : f' ≠ 0)
    (ha : conj a = a)
    (hfa : (f a).im = 0)
    (hconj : ∀ᶠ z in nhds a, f (conj z) = conj (f z)) :
    ∀ᶠ y : ℝ in nhds (f a).re,
      (hf.localInverse f f' a hf' (y : ℂ)).im = 0 := by
  have hsymm := eventually_conj_localInverse_conj hf hf' ha hconj
  have htarget : ((f a).re : ℂ) = f a := by
    apply Complex.ext
    · simp
    · simpa using hfa.symm
  have hofReal : Tendsto (fun y : ℝ ↦ (y : ℂ))
      (nhds (f a).re) (nhds (f a)) := by
    have hc := Complex.continuous_ofReal.continuousAt (x := (f a).re)
    change Tendsto (fun y : ℝ ↦ (y : ℂ))
      (nhds (f a).re) (nhds ((f a).re : ℂ)) at hc
    rw [htarget] at hc
    exact hc
  filter_upwards [hofReal.eventually hsymm] with y hy
  rw [Complex.conj_ofReal] at hy
  exact Complex.conj_eq_iff_im.mp hy

end PoincareChapterVI
