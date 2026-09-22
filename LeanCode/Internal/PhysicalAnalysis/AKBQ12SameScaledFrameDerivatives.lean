import AKBQ1SameScaledFrame
import ACP1OriginalRotation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.ActualScaledNativeCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Physical.Ledger

 theorem frameMultiDerivative_columnScale {grade : ℕ} (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : GradeCore parameters 3 grade) (cell : ℤ) (index : CartesianMultiIndex) (point : ClosedDisk) :
    (frameDeviationMultiDerivative parameters 1 epsilon field cell index point).comp (physicalColumnScale L) =
      frameDeviationMultiDerivative parameters L epsilon field cell index point := by
  apply ContinuousLinearMap.ext
  intro value
  rw [ContinuousLinearMap.comp_apply,physicalColumnScale_apply]
  apply PiLp.ext
  intro coordinate
  simp only [frameDeviationMultiDerivative,add_apply,columnEmbedding_apply,PiLp.add_apply,
    PiLp.smul_apply,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,
    Matrix.vecHead,Matrix.vecTail,smul_eq_mul,Complex.ofReal_one,inv_one,one_smul]
  dsimp
  ring

/-- Genuine first coefficient derivatives obey the same y=ell Y scaling, including the original third-column length factor. -/
theorem scaledFrameDerivative_unit {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3) (cell : ℤ) (index : DerivativeIndex 1)
    (order : derivativeOrder index = 1) (point : ClosedDisk) :
    coefficientDerivative (actualFrameFamily parameters L ell epsilon field 1) cell index point =
      (ell : ℂ) • (coefficientDerivative (actualFrameFamily parameters 1 1 epsilon field 1) cell index
        (physicalScaledPoint ell admissible.2.2.2.1.le
          (admissible.2.2.2.2.trans (min_le_left _ _)) point)).comp (physicalColumnScale L) := by
  have scaled := actualFrameDeviationCoefficient_derivative parameters admissible epsilon
    (GradeCore.ofCoreLinear (grade := 5) field) cell index point
  rw [order,pow_one] at scaled
  have unit := actualFrameDeviationCoefficient_derivative parameters (unitDiskAdmissible parameters) epsilon
    (GradeCore.ofCoreLinear (grade := 5) field) cell index
    (physicalScaledPoint ell admissible.2.2.2.1.le
      (admissible.2.2.2.2.trans (min_le_left _ _)) point)
  rw [Complex.ofReal_one,one_pow,one_smul,physicalScaledPoint_unit] at unit
  change coefficientDerivative (actualFrameFamily parameters 1 1 epsilon field 1) cell index _ = _ at unit
  rw [unit,frameMultiDerivative_columnScale]
  exact scaled

end Grad.ActualScaledNativeCoefficients
