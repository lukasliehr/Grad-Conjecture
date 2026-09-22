import GQ6PhysicalMeans

noncomputable section

set_option maxHeartbeats 2200000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.GaugeTransfer

open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

/-- The physical planar covector iota*M*JY, in physical component order. -/
def physicalTangentCovector (seed : Matrix (Fin 2) (Fin 2) ℂ) (point : ClosedDisk) : Fin 3 → ℂ :=
  (planarPhysicalInclusion * seed).mulVec ![-(point.val 1 : ℂ), (point.val 0 : ℂ)]

/-- e_T+iota*((ell/L)M')Y. The derivative argument is the actual scaled
seed derivative, identified with its literal Fourier series below. -/
def physicalToroidalCovector (scaledDerivative : Matrix (Fin 2) (Fin 2) ℂ) (point : ClosedDisk) : Fin 3 → ℂ :=
  fun row => (toroidalPhysicalColumn + planarPhysicalInclusion * scaledDerivative * spatialColumn point) row 0

theorem physicalGaugeMatrix_tangent (seed scaledDerivative : Matrix (Fin 2) (Fin 2) ℂ)
    (inverseTranspose : Matrix (Fin 3) (Fin 3) ℂ) (point : ClosedDisk) (value : PhysicalValue 3) :
    storedTangentDot point (WithLp.toLp 2 ((physicalGaugeMatrix seed scaledDerivative inverseTranspose point).mulVec value)) =
      ∑ row : Fin 3, (inverseTranspose.mulVec value) row * physicalTangentCovector seed point row := by
  simp [storedTangentDot, physicalGaugeMatrix, physicalTangentCovector, planarPhysicalInclusion,
    Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Fin.sum_univ_three]
  ring

theorem physicalGaugeMatrix_toroidal (seed scaledDerivative : Matrix (Fin 2) (Fin 2) ℂ)
    (inverseTranspose : Matrix (Fin 3) (Fin 3) ℂ) (point : ClosedDisk) (value : PhysicalValue 3) :
    (physicalGaugeMatrix seed scaledDerivative inverseTranspose point).mulVec value 2 =
      ∑ row : Fin 3, (inverseTranspose.mulVec value) row * physicalToroidalCovector scaledDerivative point row := by
  simp [physicalGaugeMatrix, physicalToroidalCovector, planarPhysicalInclusion, toroidalPhysicalColumn, spatialColumn,
    Matrix.mulVec, dotProduct, Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two, Fin.sum_univ_three]
  ring

theorem fullGauge_action_matrix {L sigma gamma ell : ℝ} (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (grade : ℕ) (angle : ℝ) (field : ClosedDisk → PhysicalValue 3) (point : ClosedDisk) :
    fullGaugeValueAction gauge grade angle field point =
      WithLp.toLp 2 ((familyMatrix (fullGaugeFamily gauge) grade angle point).mulVec (field point)) := by
  apply PiLp.ext
  intro row
  exact operatorMatrix_action _ _ row

section ActualLedger

variable {L ell : ℝ} {parameters : PhaseParameters}
    {admissible : Admissible L parameters.sigma0 parameters.gamma ell}
    {rho alpha delta parameter epsilon : ℝ} {base : ACore parameters 3}
    (ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base)

def physicalInverseTranspose (grade : ℕ) (angle : ℝ) (point : ClosedDisk) : Matrix (Fin 3) (Fin 3) ℂ :=
  (operatorMatrix (coefficientPhysicalValue (ledger.val.frameInverse grade) angle point)).transpose

def actualScaledSeedDerivative (angle : ℝ) (point : ClosedDisk) : Matrix (Fin 2) (Fin 2) ℂ :=
  operatorMatrix (fourierEvaluation (seedDerivativeCoefficient admissible 0 rho alpha delta parameter) angle point)

theorem actualGauge_tangent (grade : ℕ) (angle : ℝ) (field : ClosedDisk → PhysicalValue 3) (point : ClosedDisk) :
    storedTangentDot point (fullGaugeValueAction ledger.val.gaugeDeviation grade angle field point) =
      ∑ row : Fin 3, ((physicalInverseTranspose ledger grade angle point).mulVec (field point)) row *
        physicalTangentCovector (physicalSeedMatrix rho alpha delta parameter angle) point row := by
  rw [fullGauge_action_matrix, actualFullGauge_matrix ledger]
  exact physicalGaugeMatrix_tangent _ _ _ point (field point)

theorem actualGauge_toroidal (grade : ℕ) (angle : ℝ) (field : ClosedDisk → PhysicalValue 3) (point : ClosedDisk) :
    fullGaugeValueAction ledger.val.gaugeDeviation grade angle field point 2 =
      ∑ row : Fin 3, ((physicalInverseTranspose ledger grade angle point).mulVec (field point)) row *
        physicalToroidalCovector (actualScaledSeedDerivative (admissible := admissible)
          (rho := rho) (alpha := alpha) (delta := delta) (parameter := parameter) angle point) point row := by
  rw [fullGauge_action_matrix, actualFullGauge_matrix ledger]
  exact physicalGaugeMatrix_toroidal _ _ _ point (field point)

end ActualLedger

end Grad.GaugeCoefficients.Physical.GaugeTransfer
