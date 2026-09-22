import AKAO25SameOriginalCofactorDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualPolarFlux
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

def _root_.Grad.ActualSmoothPhysicalField.SmoothLowPhysicalRow.forceZero :
    SmoothLowPhysicalRow parameters lower positive
      (regularRadialBulkAction parameters 0 lower positive bounded.le
        (radialOriginalForceZeroKernel parameters length compact state)
        (radialOriginalForceZeroKernel_regular parameters length compact state) row) :=
  curves.action parameters lower positive bounded _
    (radialOriginalForceZeroKernel_regular parameters length compact state)
    (actualOriginalForceZero_conjugated_smooth parameters length compact state lower positive bounded)

def _root_.Grad.ActualSmoothPhysicalField.SmoothLowPhysicalRow.physicalKV :
    SmoothLowPhysicalRow parameters lower positive
      (regularRadialBulkAction parameters 0 lower positive bounded.le
        (radialKVKernel parameters length compact state) (radialKVKernel_regular parameters length compact state) row) :=
  curves.action parameters lower positive bounded _
    (radialKVKernel_regular parameters length compact state)
    (actualKV_conjugated_smooth parameters length compact state lower positive bounded)

theorem fullField_originalForceZero (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.forceZero parameters length compact lower positive bounded state).fullField bounded (radius,angles) 0 =
      (physicalForceCurves parameters length compact lower positive bounded state.val 0 curves).fullField bounded (radius,angles) 0 -
        2 * curves.fullField bounded (radius,angles) 0 := by
  let projection := fun r : RadialPoint => coordinateProjectionKernel (radialKernelParameters parameters r) 3 0
  let force := fun r => radialForceKernel parameters length compact state.val.val r 0 0
  have projectionRegular : RegularKernelFamily projection := constantMatrixRadialKernel_regular parameters _ _ _
  have projectionSmooth : SmoothConjugatedFamily parameters lower positive bounded.le projection :=
    smoothConjugatedFamily_fixed parameters lower positive bounded
      (fun p => coordinateProjectionKernel p 3 0) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
  have scaledRegular : RegularKernelFamily (fun r => fullKernelSmul (-2) (projection r)) :=
    fixedRadialKernel_regular parameters _ (fun _ _ => (sameConstantMatrixKernel _ _ _ _ _).smul (-2))
  have scaledSmooth : SmoothConjugatedFamily parameters lower positive bounded.le (fun r => fullKernelSmul (-2) (projection r)) :=
    SmoothConjugatedFamily.smul projectionSmooth (fun _ => -2) contDiffOn_const
  have forceRegular := radialForceKernel_regular parameters length compact state.val.val 0 0
  have forceSmooth := radialForceKernel_conjugated_smooth parameters length compact state.val.val lower positive bounded 0 0
  have same := fullField_action_add parameters lower positive bounded curves
    (fun r => fullKernelSmul (-2) (projection r)) force scaledRegular forceRegular scaledSmooth forceSmooth radius inside angles
  rw [fullField_action_radial_smul parameters lower positive bounded curves (fun _ => -2) continuousOn_const
      projection projectionRegular projectionSmooth scaledRegular scaledSmooth radius inside angles,
    fullField_action_projection parameters lower positive bounded curves 0 radius inside angles,
    curves.fullField_bulkUnit bounded (0 : Fin 1) 0 radius inside angles] at same
  change (curves.forceZero parameters length compact lower positive bounded state).fullField bounded (radius,angles) =
    (-2 : ℂ) • matrixUnit (0 : Fin 1) 0 (curves.fullField bounded (radius,angles)) +
    (physicalForceCurves parameters length compact lower positive bounded state.val 0 curves).fullField bounded (radius,angles) at same
  rw [same]
  simp [matrixUnit_apply,operatorBasis]
  ring

end Grad.ActualPolarFlux
