import AKBB1SameCorrectedPPrimitiveCoefficients
import AKAK22SamePhysicalAxialDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarFlux
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.AnnularSmoothCore Grad.BoundaryTrace Grad.SourceCollarFullSource

/-- Actual AE coefficient laws determine the SAME continuous coefficients
at every radius, including both collar endpoints. -/
theorem samePhysical_modeMultiplier {parameters : PhaseParameters} {lower : ℝ}
    {positive : 0 < lower} {first second : DivisionRow 1 lower}
    (a : SmoothLowPhysicalRow parameters lower positive first)
    (b : SmoothLowPhysicalRow parameters lower positive second) (bounded : lower < 1)
    (multiplier : (ℤ × ℤ) → ℂ)
    (same : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      lowRhoPhysicalCoefficient parameters lower positive first radius mode =
        multiplier mode • lowRhoPhysicalCoefficient parameters lower positive second radius mode)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    a.physicalCurve 0 radius mode = multiplier mode • b.physicalCurve 0 radius mode := by
  apply collarCurve_eq_of_ae lower bounded
    (fun location => a.physicalCurve 0 location mode)
    (fun location => multiplier mode • b.physicalCurve 0 location mode)
    ((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode).continuous.comp_continuousOn
      (a.physicalCurve_smooth bounded 0).continuousOn)
    (((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode).continuous.comp_continuousOn
      (b.physicalCurve_smooth bounded 0).continuousOn).const_smul (multiplier mode)) _ inside
  filter_upwards [a.physicalCurve_actual bounded 0,b.physicalCurve_actual bounded 0,same]
    with location aSame bSame law
  simpa only [aSame mode,bSame mode,pow_zero,one_smul] using law mode

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution))

theorem sharedCorrectedP_physicalCurve (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    (seven.correctedP parameters length compact lower positive bounded state).physicalCurve 0 radius mode =
      angularInverseMultiplier mode • (seven.bulkUnit (0 : Fin 1) (0 : Fin 7)).physicalCurve 0 radius mode :=
  samePhysical_modeMultiplier _ _ bounded angularInverseMultiplier
    (sharedCorrectedP_primitiveCoefficients parameters length compact lower positive bounded state lengthPositive data solution)
    radius inside mode

theorem sharedBThree_physicalCurve (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    (seven.lowPhysicalCurves parameters length compact lower positive bounded state 1).physicalCurve 0 radius mode =
      (Complex.I * (mode.1 : ℂ)) • (seven.bThree parameters length compact lower positive bounded state).physicalCurve 0 radius mode :=
  samePhysical_modeMultiplier _ _ bounded (fun mode => Complex.I * (mode.1 : ℂ))
    (sharedBThree_angularCoefficients parameters length compact lower positive bounded state lengthPositive data solution)
    radius inside mode

end Grad.ActualPolarFlux
