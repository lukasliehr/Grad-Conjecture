import AKBQ1SameScaledFrame
import GSP2PhysicalGaugeMatrix

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Grad.ActualScaledNativeCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.ActualGaugeSigmaPrimitives

 theorem scaledSpatialColumn (ell : ℝ) (nonnegative : 0 ≤ ell) (bounded : ell ≤ 1) (point : ClosedDisk) :
    spatialColumn (physicalScaledPoint ell nonnegative bounded point) = (ell : ℂ) • spatialColumn point := by
  ext row column
  simp only [spatialColumn,physicalScaledPoint,PiLp.smul_apply,smul_eq_mul,Complex.ofReal_mul,Matrix.smul_apply]

 theorem scaledPhysicalGaugeMatrix (L ell : ℝ) (nonnegative : 0 ≤ ell) (bounded : ell ≤ 1)
    (seed derivative : Matrix (Fin 2) (Fin 2) ℂ) (inverseTranspose : Matrix (Fin 3) (Fin 3) ℂ)
    (point : ClosedDisk) :
    physicalGaugeMatrix seed (((ell / L : ℝ) : ℂ) • derivative) inverseTranspose point =
      physicalGaugeMatrix seed (((L : ℂ)⁻¹) • derivative) inverseTranspose
        (physicalScaledPoint ell nonnegative bounded point) := by
  have column : planarPhysicalInclusion * (((ell / L : ℝ) : ℂ) • derivative) * spatialColumn point =
      planarPhysicalInclusion * (((L : ℂ)⁻¹) • derivative) *
        spatialColumn (physicalScaledPoint ell nonnegative bounded point) := by
    rw [scaledSpatialColumn]
    simp only [Matrix.mul_smul,Matrix.smul_mul,smul_smul]
    rw [Complex.ofReal_div,div_eq_mul_inv,mul_comm (ell : ℂ) (L : ℂ)⁻¹]
  unfold physicalGaugeMatrix
  simp only [column]
  rfl

/-- C0 is the original full gauge matrix at y=ell Y, including the physical L^-1 seed derivative. -/
theorem scaledLedgerGauge_original {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {field : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon field)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (fullGaugeFamily ledger.val.gaugeDeviation) grade angle point =
      originalPhysicalGaugeMatrix parameters L rho alpha delta parameter epsilon field angle
        (physicalScaledPoint ell admissible.2.2.2.1.le
          (admissible.2.2.2.2.trans (min_le_left _ _)) point) := by
  rw [actualFullGauge_matrix ledger]
  change physicalGaugeMatrix _ (actualScaledSeedDerivative (admissible := admissible)
    (rho := rho) (alpha := alpha) (delta := delta) (parameter := parameter) angle point)
    (familyMatrix ledger.val.frameInverse grade angle point).transpose point = _
  rw [actualScaledSeedDerivative_formula,scaledLedgerInverse_original ledger,
    scaledPhysicalGaugeMatrix]
  rfl

end Grad.ActualScaledNativeCoefficients
