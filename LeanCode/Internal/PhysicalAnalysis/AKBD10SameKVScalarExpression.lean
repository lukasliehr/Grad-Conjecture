import AKBD9ActualCofactorAngularProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualDeterminantEquations
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)

open Grad.ActualPolarFlux Grad.ActualCartesianEquations

variable {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

/-- Exact scalar form of the actual K_v, with both internal angular
projections kept inside the corresponding original signed kappa product. -/
theorem sameKV_scalar (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.physicalKV parameters length compact lower positive bounded state).fullField bounded (radius,angles) 0 =
      (∑ component : Fin 3,originalCofactorJetSeries parameters length compact state 1 component 0 1
        (collarRadius lower positive bounded.le radius) angles * curves.fullField bounded (radius,angles) component) +
      originalCofactorSmoothEntry parameters length compact state 1 0 radius angles *
        removePolarMean (fun query => (curves.retainedForce parameters length compact lower positive bounded state).fullField bounded (radius,query) 0) angles +
      originalCofactorSmoothEntry parameters length compact state 1 1 radius angles *
        (curves.forceZero parameters length compact lower positive bounded state).fullField bounded (radius,angles) 0 -
      originalCofactorSmoothEntry parameters length compact state 1 2 radius angles *
        removePolarMean (fun query => (physicalForceCurves parameters length compact lower positive bounded state.val 1 curves).fullField bounded (radius,query) 0) angles := by
  let retained := curves.retainedForce parameters length compact lower positive bounded state
  let forceTwo := physicalForceCurves parameters length compact lower positive bounded state.val 1 curves
  let point : RadialPoint := ⟨radius,⟨positive.le.trans inside.1,inside.2⟩⟩
  have coefficient (component : Fin 3) := originalCofactorSmoothEntry_literal parameters length compact state 1 component point angles
  have value := congrArg (fun output : ComplexEuclidean 1 => output 0)
    (fullField_originalKV parameters length compact lower positive bounded state curves radius inside angles)
  simp only [PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul] at value
  rw [removePolarMean_coordinate (fun query => retained.fullField bounded (radius,query))
      (retained.fullField_continuous_angles bounded radius inside) angles,
    removePolarMean_coordinate (fun query => forceTwo.fullField bounded (radius,query))
      (forceTwo.fullField_continuous_angles bounded radius inside) angles] at value
  dsimp only [point] at coefficient
  rw [coefficient 0,coefficient 1,coefficient 2]
  simpa [retained,forceTwo,originalCofactorJetRowProduct,Fin.sum_univ_three,PiLp.add_apply,PiLp.smul_apply,
    matrixUnit_apply,operatorBasis] using value

end Grad.ActualDeterminantEquations
