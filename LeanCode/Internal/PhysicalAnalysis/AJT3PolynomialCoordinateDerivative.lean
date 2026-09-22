import AJT2SameClampedSystem

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.SourceCollarCoefficients Grad.AnnularSourceGraph

/-- AE equality of continuous collar candidates is pointwise, including
both endpoints. This is applied to the actual full RHS, never to an assumed
derivative representative. -/
theorem collarCurve_eq_of_ae {E : Type*} [TopologicalSpace E] [T2Space E]
    (lower : ℝ) (bounded : lower < 1) (first second : ℝ → E)
    (firstContinuous : ContinuousOn first (Icc lower 1))
    (secondContinuous : ContinuousOn second (Icc lower 1))
    (same : first =ᵐ[volume.restrict (Icc lower 1)] second) :
    EqOn first second (Icc lower 1) :=
  MeasureTheory.Measure.eqOn_of_ae_eq same firstContinuous secondContinuous
    (by rw [interior_Icc, closure_Ioo bounded.ne])

/-- Constant polynomial Fourier insertion transports the genuine base
coordinate derivative. The RHS equality is established from its full AE
physical formula and continuity on the collar. -/
theorem coordinateDerivative_of_grade {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (lower : ℝ) (bounded : lower < 1) (scalar : ℂ)
    (field base derivative baseDerivative : ℝ → E)
    (fieldSame : EqOn field (fun point => scalar • base point) (Icc lower 1))
    (derivativeContinuous : ContinuousOn derivative (Icc lower 1))
    (baseDerivativeContinuous : ContinuousOn baseDerivative (Icc lower 1))
    (derivativeSame : derivative =ᵐ[volume.restrict (Icc lower 1)]
      fun point => scalar • baseDerivative point)
    (law : ∀ radius ∈ Icc lower 1,
      HasDerivWithinAt base (baseDerivative radius) (Icc lower 1) radius)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt field (derivative radius) (Icc lower 1) radius := by
  have same := collarCurve_eq_of_ae lower bounded derivative
    (fun point => scalar • baseDerivative point) derivativeContinuous
    ((show ContinuousOn (fun _ : ℝ => scalar) (Icc lower 1) from continuousOn_const).smul
      baseDerivativeContinuous) derivativeSame
  rw [same inside]
  exact ((law radius inside).const_smul scalar).congr
    (fun point member => fieldSame member) (fieldSame inside)

end Grad.AnnularSmoothCore
