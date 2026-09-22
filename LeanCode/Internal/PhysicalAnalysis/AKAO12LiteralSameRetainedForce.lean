import AKAO11SameRetainedForceDeviation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualPolarFlux
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

/-- The actual completed r1 row is literal original retained-force multiplication. -/
theorem fullField_originalRetainedForce (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.retainedForce parameters length compact lower positive bounded state).fullField bounded (radius,angles) 0 =
      ∑ component : Fin 3,originalRetainedForceRow parameters length state.val.val.epsilon state.val.val.field
        angles.2 angles.1 (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) component *
          curves.fullField bounded (radius,angles) component := by
  let deviation := radialRetainedForceDeviationKernel parameters length compact state.val.val
  let projection := fun r : RadialPoint => coordinateProjectionKernel (radialKernelParameters parameters r) 3 1
  have deviationRegular := radialRetainedForceDeviationKernel_regular parameters length compact state.val
  have projectionRegular : RegularKernelFamily projection := constantMatrixRadialKernel_regular parameters _ _ _
  have deviationSmooth := retainedForceDeviation_smooth parameters length compact lower positive bounded state
  have projectionSmooth : SmoothConjugatedFamily parameters lower positive bounded.le projection :=
    smoothConjugatedFamily_fixed parameters lower positive bounded
      (fun p => coordinateProjectionKernel p 3 1) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
  have same := fullField_action_congr parameters lower positive bounded curves
    (fun r => radialRetainedForceKernel parameters length compact state.val.val r)
    (fun r => fullKernelAdd (fullKernelAdd (deviation r) (deviation r)) (fullKernelAdd (projection r) (projection r)))
    (radialRetainedForceKernel_regular parameters length compact state.val)
    ((deviationRegular.add deviationRegular).add (projectionRegular.add projectionRegular))
    (actualRetainedForce_conjugated_smooth parameters length compact state lower positive bounded)
    ((deviationSmooth.add deviationSmooth).add (projectionSmooth.add projectionSmooth)) (fun r => by
      apply FullTwoFrequencyKernel.ext_entry
      intro shift mode
      simp only [radialRetainedForceKernel,fullKernelAdd_entry,fullKernelSmul_entry,
        deviation,projection,radialRetainedForceDeviationKernel]
      module) radius inside angles
  rw [fullField_action_add parameters lower positive bounded curves
      (fun r => fullKernelAdd (deviation r) (deviation r)) (fun r => fullKernelAdd (projection r) (projection r))
      (deviationRegular.add deviationRegular) (projectionRegular.add projectionRegular)
      (deviationSmooth.add deviationSmooth) (projectionSmooth.add projectionSmooth) radius inside angles,
    fullField_action_add parameters lower positive bounded curves deviation deviation deviationRegular deviationRegular deviationSmooth deviationSmooth radius inside angles,
    fullField_action_add parameters lower positive bounded curves projection projection projectionRegular projectionRegular projectionSmooth projectionSmooth radius inside angles,
    fullField_action_projection parameters lower positive bounded curves 1 radius inside angles] at same
  change (curves.retainedForce parameters length compact lower positive bounded state).fullField bounded (radius,angles) =
    ((curves.retainedForceDeviation parameters length compact lower positive bounded state).fullField bounded (radius,angles) +
      (curves.retainedForceDeviation parameters length compact lower positive bounded state).fullField bounded (radius,angles)) +
    ((curves.bulkUnit (0 : Fin 1) 1).fullField bounded (radius,angles) +
      (curves.bulkUnit (0 : Fin 1) 1).fullField bounded (radius,angles)) at same
  rw [same,fullField_retainedForceDeviation parameters length compact lower positive bounded state curves radius inside angles,
    curves.fullField_bulkUnit bounded (0 : Fin 1) 1 radius inside angles]
  simp_rw [originalRetainedForceRow_deviation parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low]
  simp [polarFamilyRowProduct,polarFamilyAngleEntry,
    forceMatrixFamily_actual parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low,
    matrixUnit_apply,operatorBasis,Fin.sum_univ_three]
  ring

end Grad.ActualPolarFlux
