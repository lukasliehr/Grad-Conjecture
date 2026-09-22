import AKAO6SamePolarCofactorProduct

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
    (state : RetainedInverseState parameters length compact) (cofactorRow : Fin 3)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

def _root_.Grad.ActualSmoothPhysicalField.SmoothLowPhysicalRow.signedCofactorRow :
    SmoothLowPhysicalRow parameters lower positive
      (regularRadialBulkAction parameters 0 lower positive bounded.le
        (radialSignedCofactorRowKernel parameters length compact state cofactorRow)
        (radialSignedCofactorRowKernel_regular parameters length compact state cofactorRow) row) :=
  curves.action parameters lower positive bounded _
    (radialSignedCofactorRowKernel_regular parameters length compact state cofactorRow)
    (actualSignedCofactorRow_conjugated_smooth parameters length compact state lower positive bounded cofactorRow)

 theorem fullField_signedCofactorDifference (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.signedCofactorRow parameters length compact lower positive bounded state cofactorRow).fullField bounded (radius,angles) =
      (curves.cofactorDeviationRow parameters length compact lower positive bounded state cofactorRow).fullField bounded (radius,angles) -
        (curves.bulkUnit (0 : Fin 1) cofactorRow).fullField bounded (radius,angles) := by
  let deviation := radialCofactorJetRowKernel parameters length compact state cofactorRow 0 0
  let projection := fun r : RadialPoint => coordinateProjectionKernel (radialKernelParameters parameters r) 3 cofactorRow
  have deviationRegular := radialCofactorJetRowKernel_regular parameters length compact state cofactorRow 0 0
  have projectionRegular : RegularKernelFamily projection := constantMatrixRadialKernel_regular parameters _ _ _
  have deviationSmooth := actualCofactorRow_conjugated_smooth parameters length compact state lower positive bounded cofactorRow 0 0
  have projectionSmooth : SmoothConjugatedFamily parameters lower positive bounded.le projection :=
    smoothConjugatedFamily_fixed parameters lower positive bounded
      (fun p => coordinateProjectionKernel p 3 cofactorRow) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
  have same := fullField_action_congr parameters lower positive bounded curves
    (radialSignedCofactorRowKernel parameters length compact state cofactorRow)
    (fun r => fullKernelSub (deviation r) (projection r))
    (radialSignedCofactorRowKernel_regular parameters length compact state cofactorRow)
    (deviationRegular.sub projectionRegular)
    (actualSignedCofactorRow_conjugated_smooth parameters length compact state lower positive bounded cofactorRow)
    (deviationSmooth.sub projectionSmooth) (fun r => by
      apply FullTwoFrequencyKernel.ext_entry
      intro shift mode
      simp only [radialSignedCofactorRowKernel,fullKernelAdd_entry,fullKernelNeg_entry,fullKernelSub_entry]
      abel) radius inside angles
  rw [fullField_action_sub parameters lower positive bounded curves deviation projection deviationRegular projectionRegular
    deviationSmooth projectionSmooth radius inside angles,
    fullField_action_projection parameters lower positive bounded curves cofactorRow radius inside angles] at same
  exact same

/-- The actual completed signed row is the literal original polar signed cofactor, on the SAME field. -/
theorem fullField_signedCofactorRow (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.signedCofactorRow parameters length compact lower positive bounded state cofactorRow).fullField bounded (radius,angles) 0 =
      ∑ component : Fin 3, originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field
        cofactorRow angles.2 angles.1 (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) component *
          curves.fullField bounded (radius,angles) component := by
  rw [fullField_signedCofactorDifference parameters length compact lower positive bounded state cofactorRow curves radius inside angles,
    fullField_cofactorDeviationProduct parameters length compact lower positive bounded state cofactorRow curves radius inside angles,
    curves.fullField_bulkUnit bounded (0 : Fin 1) cofactorRow radius inside angles]
  simp only [polarFamilyRowProduct,polarFamilyAngleEntry,
    originalCofactorDeviation_matrix parameters length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low,
    polarMatrixEntry_add,polarMatrixEntry_one,originalSignedCofactorRow]
  simp [matrixUnit_apply,operatorBasis,add_smul,Finset.sum_add_distrib]

end Grad.ActualPolarFlux
