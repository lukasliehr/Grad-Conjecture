import GSP12OriginalPhysicalCoefficients

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.ActualGaugeSigmaPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Frame

/-- Literal gauge covectors: iota M e_theta and e_T+iota (L^-1 M')Y.
The supplied derivative here is already the physical L^-1 M'. -/
def physicalGaugeCovector (seed derivative : Matrix (Fin 2) (Fin 2) ℂ)
    (angle : ℝ) (point : ClosedDisk) (kind : Fin 2) : Fin 3 → ℂ :=
  if kind = 0 then planarPhysicalInclusion.mulVec (seed.mulVec ![-(Real.sin angle : ℂ), (Real.cos angle : ℂ)])
  else fun row => (toroidalPhysicalColumn + planarPhysicalInclusion * derivative * spatialColumn point) row 0

theorem physicalGaugeRow_covector (seed derivative : Matrix (Fin 2) (Fin 2) ℂ)
    (inverseTranspose : Matrix (Fin 3) (Fin 3) ℂ) (angle : ℝ) (point : ClosedDisk)
    (kind : Fin 2) (component : Fin 3) :
    polarMatrixEntry (if kind = 0 then 1 else 2) component angle
      (physicalGaugeMatrix seed derivative inverseTranspose point) =
      matrixPairing (physicalGaugeCovector seed derivative angle point kind)
        inverseTranspose (polarVector component angle) := by
  fin_cases kind <;>
    simp [polarMatrixEntry, physicalGaugeCovector, physicalGaugeMatrix, polarVector, matrixPairing,
      Matrix.mulVec, dotProduct, Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two,
      physicalTangentialVector, physicalToroidalVector] <;> ring

theorem originalGaugeRow_covector (parameters : PhaseParameters) (L rho alpha delta parameter epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2) (axialAngle polarAngle : ℝ)
    (point : ClosedDisk) (component : Fin 3) :
    originalGaugeRow parameters L rho alpha delta parameter epsilon field kind axialAngle polarAngle point component =
      matrixPairing
        (physicalGaugeCovector (physicalSeedMatrix rho alpha delta parameter axialAngle)
          (((L : ℂ)⁻¹) • operatorMatrix (deriv (harmonicSeedOperator rho alpha delta parameter) axialAngle))
          polarAngle point kind)
        (originalPhysicalFrameMatrix parameters L epsilon field axialAngle point)⁻¹.transpose
        (polarVector component polarAngle) :=
  physicalGaugeRow_covector _ _ _ _ _ _ _

end Grad.ActualGaugeSigmaPrimitives
