import AKDS34OriginalUnitLedgerFidelity
import AKBQ15SameNativeCoefficientProducts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4000
namespace Grad.OriginalCoreRealization.OriginalUnitRankState
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger Grad.ActualCurrentPrimitives Grad.Constraints.Gauges
open Grad.ActualScaledNativeCoefficients
variable {parameters : PhaseParameters} {length radius : ℝ}
    (state : OriginalUnitRankState parameters length radius)

/-- Actual physical-length planar force matrix in unit coordinates. -/
theorem planarForce_matrix (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix state.data.rotatedPlanarProduct grade angle point =
      planarFrameColumns.transpose *
        familyMatrix (forceMatrixFamily parameters length state.epsilon state.field) grade angle point := by
  rw [forceMatrixFamily_matrix parameters length state.rho state.epsilon state.field state.coefficientLow]
  have actual := (state.rotated_matrix grade angle point).1
  rw [Matrix.transpose_mul, Matrix.mul_assoc] at actual
  exact actual

/-- Actual physical-length third force matrix in unit coordinates. -/
theorem thirdForce_matrix (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix state.data.rotatedThirdProduct grade angle point =
      thirdFrameColumn.transpose *
        familyMatrix (forceMatrixFamily parameters length state.epsilon state.field) grade angle point := by
  rw [forceMatrixFamily_matrix parameters length state.rho state.epsilon state.field state.coefficientLow]
  have actual := (state.rotated_matrix grade angle point).2
  rw [Matrix.transpose_mul, Matrix.mul_assoc] at actual
  exact actual

/-- The actual signed cofactor plus identity, with physical length retained. -/
theorem cofactorFlux_matrix (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix state.data.fluxDeviation grade angle point =
      familyMatrix (originalCofactorFamily parameters length state.epsilon state.field) grade angle point + 1 := by
  rw [originalCofactorFamily_eq_signedCofactor parameters length state.rho state.epsilon state.field state.coefficientLow]
  exact state.flux_matrix grade angle point

end Grad.OriginalCoreRealization.OriginalUnitRankState
