import AJI1ClosedScaleRadialBootstrap
import AJI13HilbertRadialDerivative
import AJI19ActualRadialSystemOperator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff
namespace Grad.AnnularSmoothCore
open Grad.AnnularSourceGraph Grad.SourceCollarCoefficients

/-- A continuous collar RHS has a continuous ambient extension with the same
values on the original collar. This adds no equation outside that collar. -/
theorem continuous_clampedCurve {E : Type*} [TopologicalSpace E]
    (lower : ℝ) (bounded : lower ≤ 1) (curve : ℝ → E)
    (continuous : ContinuousOn curve (Icc lower 1)) :
    Continuous (fun radius : ℝ => curve (radialClamp lower bounded radius)) :=
  (continuousOn_iff_continuous_domRestrict.mp continuous).comp (radialClamp_continuous lower bounded)

/-- Apply the existing Hilbert FTC separately to the two full Fourier
coordinates, retaining the product norm and both physical fields. -/
theorem hilbertPairDerivative_of_coordinates
    (lower : ℝ) (bounded : lower ≤ 1) (field derivative : ℝ → PhysicalHilbertPair)
    (continuous : ContinuousOn field (Icc lower 1))
    (derivativeContinuous : ContinuousOn derivative (Icc lower 1))
    (xLaw : ∀ mode radius, radius ∈ Icc lower 1 →
      HasDerivWithinAt (fun point => (field point).1 mode) ((derivative radius).1 mode)
        (Icc lower 1) radius)
    (xiLaw : ∀ mode radius, radius ∈ Icc lower 1 →
      HasDerivWithinAt (fun point => (field point).2 mode) ((derivative radius).2 mode)
        (Icc lower 1) radius)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt field (derivative radius) (Icc lower 1) radius := by
  let extended : ℝ → PhysicalHilbertPair :=
    fun point => derivative (radialClamp lower bounded point)
  have same (point : ℝ) (member : point ∈ Icc lower 1) : extended point = derivative point := by
    dsimp only [extended]
    rw [radialClamp_eq lower bounded point member]
  have extensionContinuous : Continuous extended :=
    continuous_clampedCurve lower bounded derivative derivativeContinuous
  have xDerivative := hilbertDerivative_of_coordinates lower
    (fun point => (field point).1) (fun point => (extended point).1)
    continuous.fst extensionContinuous.fst
    (fun mode point member => by rw [same point member]; exact xLaw mode point member)
    radius inside
  have xiDerivative := hilbertDerivative_of_coordinates lower
    (fun point => (field point).2) (fun point => (extended point).2)
    continuous.snd extensionContinuous.snd
    (fun mode point member => by rw [same point member]; exact xiLaw mode point member)
    radius inside
  simpa only [same radius inside, Prod.mk.eta] using xDerivative.prodMk xiDerivative

/-- The original two-grade radial system bootstraps from genuine coordinate
derivatives. All polynomial grades are retained before radial induction. -/
theorem physicalPairScale_smooth_of_coordinates
    (lower : ℝ) (bounded : lower < 1)
    (field source : ℕ → ℝ → PhysicalHilbertPair)
    (operator : ℕ → ℝ → PhysicalHilbertPair →L[ℂ] PhysicalHilbertPair)
    (continuous : ∀ grade, ContinuousOn (field grade) (Icc lower 1))
    (sourceSmooth : ∀ grade, ContDiffOn ℝ ∞ (source grade) (Icc lower 1))
    (operatorSmooth : ∀ grade, ContDiffOn ℝ ∞ (operator grade) (Icc lower 1))
    (xLaw : ∀ grade mode radius, radius ∈ Icc lower 1 →
      HasDerivWithinAt (fun point => (field grade point).1 mode)
        (((operator grade radius) (field (grade + 2) radius) + source grade radius).1 mode)
        (Icc lower 1) radius)
    (xiLaw : ∀ grade mode radius, radius ∈ Icc lower 1 →
      HasDerivWithinAt (fun point => (field grade point).2 mode)
        (((operator grade radius) (field (grade + 2) radius) + source grade radius).2 mode)
        (Icc lower 1) radius) :
    ∀ grade, ContDiffOn ℝ ∞ (field grade) (Icc lower 1) := by
  apply closedScaleSystem_smooth (fun _ => PhysicalHilbertPair) lower bounded 2
    field source operator continuous sourceSmooth operatorSmooth
  intro grade radius inside
  have rhsContinuous : ContinuousOn
      (fun point => (operator grade point) (field (grade + 2) point) + source grade point)
      (Icc lower 1) :=
    ((operatorSmooth grade).continuousOn.clm_apply (continuous (grade + 2))).add
      (sourceSmooth grade).continuousOn
  exact hilbertPairDerivative_of_coordinates lower bounded.le (field grade) _
    (continuous grade) rhsContinuous (xLaw grade) (xiLaw grade) radius inside

end Grad.AnnularSmoothCore
