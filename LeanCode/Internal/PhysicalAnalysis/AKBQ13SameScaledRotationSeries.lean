import AKBQ12SameScaledFrameDerivatives
import ACP14GenuineFourierRotation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators
namespace Grad.ActualScaledNativeCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger Grad.ActualCurrentPrimitives Grad.NonlinearRange
open Grad.GaugeCoefficients.Neumann.Regularity

 theorem scaledFrameDerivativeSeries_unit {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3) (index : DerivativeIndex 1)
    (order : derivativeOrder index = 1) (angle : ℝ) (point : ClosedDisk) :
    (∑' cell : ℤ, fourierPhase cell angle • coefficientDerivative (actualFrameFamily parameters L ell epsilon field 1) cell index point) =
      (ell : ℂ) • (∑' cell : ℤ, fourierPhase cell angle • coefficientDerivative (actualFrameFamily parameters 1 1 epsilon field 1) cell index
        (physicalScaledPoint ell admissible.2.2.2.1.le
          (admissible.2.2.2.2.trans (min_le_left _ _)) point)).comp (physicalColumnScale L) := by
  let scaled := physicalScaledPoint ell admissible.2.2.2.1.le
    (admissible.2.2.2.2.trans (min_le_left _ _)) point
  let precompose : OperatorValue 3 3 →L[ℂ] OperatorValue 3 3 :=
    (ContinuousLinearMap.compL ℂ (PhysicalValue 3) (PhysicalValue 3) (PhysicalValue 3)).flip (physicalColumnScale L)
  have summable : Summable (fun cell : ℤ => fourierPhase cell angle •
      coefficientDerivative (actualFrameFamily parameters 1 1 epsilon field 1) cell index scaled) := by
    apply Summable.of_norm
    simpa only [norm_smul,fourierPhase_norm,one_mul] using
      coefficientDerivative_point_norm_summable (unitDiskAdmissible parameters)
        (actualFrameFamily parameters 1 1 epsilon field 1) index scaled
  have total := (precompose.hasSum summable.hasSum).const_smul (ell : ℂ)
  apply HasSum.tsum_eq
  apply total.congr_fun
  intro cell
  rw [scaledFrameDerivative_unit parameters admissible epsilon field cell index order point]
  change fourierPhase cell angle • ((ell : ℂ) • precompose _) = (ell : ℂ) • precompose (fourierPhase cell angle • _)
  rw [map_smul,smul_comm]

/-- R_Y commutes with the genuine dilation, with the original physical third-column normalization. -/
theorem scaledRotatedFrame_original {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3) (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    rotatedPhysicalFrameMatrix parameters L ell epsilon field angle point =
      familyMatrix (originalRotatedFamily parameters L epsilon field) grade angle
        (physicalScaledPoint ell admissible.2.2.2.1.le
          (admissible.2.2.2.2.trans (min_le_left _ _)) point) := by
  rw [originalRotatedFamily_matrix]
  have scale : operatorMatrix (physicalColumnScale L) = Matrix.diagonal ![1,1,(L:ℂ)⁻¹] := operatorMatrix_matrixOperator _
  rw [← scale]
  unfold rotatedPhysicalFrameMatrix
  rw [scaledFrameDerivativeSeries_unit parameters admissible epsilon field firstSpatialIndex rfl,
    scaledFrameDerivativeSeries_unit parameters admissible epsilon field secondSpatialIndex rfl,
    ← operatorMatrix_comp]
  congr 1
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro coordinate
  simp only [ContinuousLinearMap.comp_apply,add_apply,smul_apply,PiLp.add_apply,PiLp.smul_apply,
    physicalScaledPoint,smul_eq_mul,Complex.ofReal_mul]
  ring

end Grad.ActualScaledNativeCoefficients
