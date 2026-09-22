import AKDS33OriginalUnitPrincipalEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
namespace Grad.OriginalCoreRealization.OriginalUnitRankState
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.SourceCollarCoefficients
open Grad.ActualGaugeSigmaPrimitives Grad.ActualCurrentPrimitives Grad.SourceCollar
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.InverseAllocation
open Grad.GaugeCoefficients.Physical.RadialLedger
variable {parameters : PhaseParameters} {length radius : ℝ}

/-- Exact physical-L inverse in the original unit-disk ledger. -/
theorem frameInverse_matrix (state : OriginalUnitRankState parameters length radius)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix state.data.frameInverse grade angle point=
      (originalPhysicalFrameMatrix parameters length state.epsilon state.field angle point)⁻¹ := by
  have margin := originalCoefficient_low_margin parameters length state.rho state.epsilon state.field state.coefficientLow
  have inverse := originalInverseFamily_matrix_identity parameters length state.epsilon state.field margin.2.2 grade angle point
  exact (Matrix.inv_eq_right_inv inverse.1).symm

/-- The full original gauge, with the actual physical-L derivative. -/
theorem gauge_matrix (state : OriginalUnitRankState parameters length radius)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (fullGaugeFamily state.data.gaugeDeviation) grade angle point=
      originalPhysicalGaugeMatrix parameters length state.val.rho state.val.alpha state.val.delta state.val.parameter
        state.epsilon state.field angle point := by
  have actual := originalUnitLedgerData_gauge_matrix parameters length state.val.rho state.val.alpha state.val.delta
    state.val.parameter state.epsilon state.field state.coefficientLow grade angle point
  change familyMatrix (fun index => identityFamily 1 parameters.sigma0 parameters.gamma 1 3 index+
    state.data.gaugeDeviation index) grade angle point=_
  have coherentGauge : FamilyCoherent state.data.gaugeDeviation :=
    originalGaugeDeviation_coherent parameters length state.val.rho state.val.alpha state.val.delta
      state.val.parameter state.epsilon state.field state.coefficientLow
  have added := familyMatrix_add (unitDiskAdmissible parameters)
    (identityFamily 1 parameters.sigma0 parameters.gamma 1 3) state.data.gaugeDeviation
    (identityFamily_coherent 1 parameters.sigma0 parameters.gamma 1 3) coherentGauge grade angle point
  exact added.trans (by rw [familyMatrix_identity,actual]; abel)

/-- The literal signed flux coefficient is det(F) F^-1 F^-T + I,
with the original physical length in F. -/
theorem flux_matrix (state : OriginalUnitRankState parameters length radius)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix state.data.fluxDeviation grade angle point=
      (originalPhysicalFrameMatrix parameters length state.epsilon state.field angle point).det •
        ((originalPhysicalFrameMatrix parameters length state.epsilon state.field angle point)⁻¹*
          (originalPhysicalFrameMatrix parameters length state.epsilon state.field angle point)⁻¹.transpose)+1 := by
  have margin := originalCoefficient_low_margin parameters length state.rho state.epsilon state.field state.coefficientLow
  have frame := (originalFullFrameFamily_estimate parameters length state.rho state.epsilon state.field margin.1).actualCoherent
  have inverse := originalInverseFamily_coherent parameters length state.epsilon state.field margin.2.2
  have actual := assembleData_flux_matrix (unitDiskAdmissible parameters)
    (originalFullFrameFamily parameters length state.epsilon state.field)
    (originalInverseFamily parameters length state.epsilon state.field)
    (seedMatrixFamily (unitDiskAdmissible parameters) state.val.rho state.val.alpha state.val.delta state.val.parameter)
    (actualSeedInverse (unitDiskAdmissible parameters) state.val.rho state.val.alpha state.val.delta state.val.parameter)
    (originalSeedDerivative parameters length state.val.rho state.val.alpha state.val.delta state.val.parameter)
    (originalRotatedFamily parameters length state.epsilon state.field) frame inverse grade angle point
  rw [originalFullFrameFamily_matrix] at actual
  have inv := state.frameInverse_matrix grade angle point
  change familyMatrix (originalInverseFamily parameters length state.epsilon state.field) grade angle point=_ at inv
  rw [inv] at actual
  exact actual

/-- Both force rows are the actual rotated-frame covector products. -/
theorem rotated_matrix (state : OriginalUnitRankState parameters length radius)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix state.data.rotatedPlanarProduct grade angle point=
      (familyMatrix (originalRotatedFamily parameters length state.epsilon state.field) grade angle point*planarFrameColumns).transpose*
        (originalPhysicalFrameMatrix parameters length state.epsilon state.field angle point)⁻¹.transpose ∧
    familyMatrix state.data.rotatedThirdProduct grade angle point=
      (familyMatrix (originalRotatedFamily parameters length state.epsilon state.field) grade angle point*thirdFrameColumn).transpose*
        (originalPhysicalFrameMatrix parameters length state.epsilon state.field angle point)⁻¹.transpose := by
  have margin := originalCoefficient_low_margin parameters length state.rho state.epsilon state.field state.coefficientLow
  have inverse := originalInverseFamily_coherent parameters length state.epsilon state.field margin.2.2
  have rotated := originalRotatedFamily_coherent parameters length state.epsilon state.field
  have first := rotatedProduct_deviation_matrix (unitDiskAdmissible parameters) planarFrameColumns
    (originalRotatedFamily parameters length state.epsilon state.field)
    (originalInverseFamily parameters length state.epsilon state.field) rotated inverse grade angle point
  have second := rotatedProduct_deviation_matrix (unitDiskAdmissible parameters) thirdFrameColumn
    (originalRotatedFamily parameters length state.epsilon state.field)
    (originalInverseFamily parameters length state.epsilon state.field) rotated inverse grade angle point
  have inv := state.frameInverse_matrix grade angle point
  change familyMatrix (originalInverseFamily parameters length state.epsilon state.field) grade angle point=_ at inv
  rw [inv] at first second
  exact ⟨first,second⟩

end Grad.OriginalCoreRealization.OriginalUnitRankState
