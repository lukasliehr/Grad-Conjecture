import AKAO21SameCofactorJetRowAction

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

theorem coordinateProjection_one_identity (parameters : PhaseParameters) :
    coordinateProjectionKernel parameters 1 0 = fullIdentityKernel parameters 1 := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift mode
  by_cases zero : shift=(0,0)
  · subst shift
    rw [coordinateProjectionKernel,constantMatrixKernel_entry,if_pos rfl,fullIdentityKernel_entry_zero]
    apply ContinuousLinearMap.ext
    intro vector
    apply PiLp.ext
    intro component
    fin_cases component
    simp [matrixUnit_apply,operatorBasis]
  · rw [coordinateProjectionKernel,constantMatrixKernel_entry,if_neg zero,
      fullIdentityKernel_entry_ne_zero parameters 1 shift mode zero]

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (cofactorRow : Fin 3)
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

theorem fullField_signedCofactorComponent_diagonal
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.signedCofactorComponent parameters length compact lower positive bounded state cofactorRow cofactorRow).fullField bounded (radius,angles) =
      originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field
        cofactorRow angles.2 angles.1 (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) cofactorRow •
          curves.fullField bounded (radius,angles) := by
  let deviation := radialCofactorJetComponentKernel parameters length compact state cofactorRow cofactorRow 0 0
  let projection := fun r : RadialPoint => coordinateProjectionKernel (radialKernelParameters parameters r) 1 0
  have deviationRegular := radialCofactorJetComponentKernel_regular parameters length compact state cofactorRow cofactorRow 0 0
  have projectionRegular : RegularKernelFamily projection := constantMatrixRadialKernel_regular parameters _ _ _
  have deviationSmooth := actualCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded cofactorRow cofactorRow 0 0
  have projectionSmooth : SmoothConjugatedFamily parameters lower positive bounded.le projection :=
    smoothConjugatedFamily_fixed parameters lower positive bounded
      (fun p => coordinateProjectionKernel p 1 0) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
  have same := fullField_action_congr parameters lower positive bounded curves
    (radialSignedCofactorComponentKernel parameters length compact state cofactorRow cofactorRow)
    (fun r => fullKernelSub (deviation r) (projection r))
    (radialSignedCofactorComponentKernel_regular parameters length compact state cofactorRow cofactorRow)
    (deviationRegular.sub projectionRegular)
    (actualSignedCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded cofactorRow cofactorRow)
    (deviationSmooth.sub projectionSmooth) (fun r => by
      apply FullTwoFrequencyKernel.ext_entry
      intro shift mode
      have circle : circularCofactorComponentKernel (radialKernelParameters parameters r) cofactorRow cofactorRow =
          fullKernelNeg (fullIdentityKernel (radialKernelParameters parameters r) 1) := by
        simp [circularCofactorComponentKernel]
      rw [radialSignedCofactorComponentKernel,fullKernelAdd_entry,circle,fullKernelNeg_entry,fullKernelSub_entry]
      change -(fullIdentityKernel (radialKernelParameters parameters r) 1).entry shift mode +
        (deviation r).entry shift mode = (deviation r).entry shift mode -
        (coordinateProjectionKernel (radialKernelParameters parameters r) 1 0).entry shift mode
      rw [coordinateProjection_one_identity]
      abel) radius inside angles
  rw [fullField_action_sub parameters lower positive bounded curves deviation projection deviationRegular projectionRegular
      deviationSmooth projectionSmooth radius inside angles,
    fullField_action_projection parameters lower positive bounded curves 0 radius inside angles] at same
  change (curves.signedCofactorComponent parameters length compact lower positive bounded state cofactorRow cofactorRow).fullField bounded (radius,angles) =
    (curves.cofactorDeviationComponent parameters length compact lower positive bounded state cofactorRow cofactorRow).fullField bounded (radius,angles) -
    (curves.bulkUnit (0 : Fin 1) 0).fullField bounded (radius,angles) at same
  rw [same,fullField_cofactorDeviationComponentProduct parameters length compact lower positive bounded state cofactorRow cofactorRow curves radius inside angles,
    curves.fullField_bulkUnit bounded (0 : Fin 1) 0 radius inside angles]
  simp only [polarFamilyAngleEntry,
    originalCofactorDeviation_matrix parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low,
    polarMatrixEntry_add,polarMatrixEntry_one,originalSignedCofactorRow]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simp [matrixUnit_apply,operatorBasis]
  ring

theorem fullField_signedCofactorComponent (component : Fin 3)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.signedCofactorComponent parameters length compact lower positive bounded state cofactorRow component).fullField bounded (radius,angles) =
      originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field
        cofactorRow angles.2 angles.1 (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) component •
          curves.fullField bounded (radius,angles) := by
  by_cases same : cofactorRow=component
  · subst component
    exact fullField_signedCofactorComponent_diagonal parameters length compact lower positive bounded state cofactorRow curves radius inside angles
  · exact fullField_signedCofactorComponent_offDiagonal parameters length compact lower positive bounded state cofactorRow component curves same radius inside angles

end Grad.ActualPolarFlux
