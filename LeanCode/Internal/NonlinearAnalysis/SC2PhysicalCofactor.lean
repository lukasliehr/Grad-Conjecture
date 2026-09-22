import SC1PolarSourceAlgebra
import GC17Consumer
import GC17FixedMatrices
import OriginalEvaluationBound

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 700000

open scoped BigOperators

namespace Grad.SourceCollar

open Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.InverseAllocation
open Grad.GaugeCoefficients.Physical.Ledger

/-- The radial planar unit vector in the **column/domain** ordering
`(y₁,y₂,ζ)` of the Cartesian frame.  The rows of the frame use the distinct
physical-value ordering `(planar₁,toroidal,planar₂)`. -/
def physicalRadialVector (angle : ℝ) : Fin 3 → ℂ :=
  ![(Real.cos angle : ℂ), (Real.sin angle : ℂ), 0]

/-- The positively oriented tangential planar unit vector in the physical
frame-column ordering `(y₁,y₂,ζ)`. -/
def physicalTangentialVector (angle : ℝ) : Fin 3 → ℂ :=
  ![-(Real.sin angle : ℂ), (Real.cos angle : ℂ), 0]

/-- The third frame-domain basis vector `e₃=e_ζ`. -/
def physicalToroidalVector : Fin 3 → ℂ := ![0, 0, 1]

/-- Bilinear (not Hermitian) matrix pairing used in BS29. -/
def matrixPairing (left : Fin 3 → ℂ) (matrix : Matrix (Fin 3) (Fin 3) ℂ)
    (right : Fin 3 → ℂ) : ℂ :=
  dotProduct left (matrix.mulVec right)

/-- The three literal BS29 cofactor contractions. -/
def physicalKappa (angle : ℝ) (cofactor : Matrix (Fin 3) (Fin 3) ℂ) : Fin 3 → ℂ :=
  ![matrixPairing (physicalTangentialVector angle) cofactor (physicalRadialVector angle),
    matrixPairing (physicalTangentialVector angle) cofactor (physicalTangentialVector angle),
    matrixPairing (physicalTangentialVector angle) cofactor physicalToroidalVector]

def firstPlanarDerivativeWord : CartesianWord 1 := fun _ => 0

def secondPlanarDerivativeWord : CartesianWord 1 := fun _ => 1

/-- Exact global Fourier realization of the two planar derivatives, the cell
derivative, and the value of the original physical displacement.  The point
is in the original unit disk, rather than the normalized cap. -/
def originalPhysicalFrameDeviation (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) (axialAngle : ℝ) (point : ClosedDisk) :
    OperatorValue 3 3 :=
  let coefficients := originalCoefficientCore parameters field
  let location : DiskCellDomain := (point, (axialAngle : CellCircle))
  let first := ordinaryDerivativeExtension coefficients firstPlanarDerivativeWord 0 location
  let second := ordinaryDerivativeExtension coefficients secondPlanarDerivativeWord 0 location
  let axial := ordinaryDerivativeExtension coefficients emptyCartesianWord 1 location
  let value := ordinaryDerivativeExtension coefficients emptyCartesianWord 0 location
  columnEmbedding 3 3 0 first + columnEmbedding 3 3 1 second +
    columnEmbedding 3 3 2 ((L : ℂ)⁻¹ •
      (axial + (epsilon : ℂ) • physicalRotation (referenceStateValue point + value)))

/-- The literal global Cartesian frame at one point of the original physical
disk.  Unlike `physicalFrameMatrix`, whose `point` is a normalized cap
coordinate and whose state is evaluated at `ell * point`, this definition's
`point` is already the physical point. -/
def originalPhysicalFrameMatrix (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) (axialAngle : ℝ) (point : ClosedDisk) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  operatorMatrix (referenceFrame +
    originalPhysicalFrameDeviation parameters L epsilon field axialAngle point)

/-- Literal BS28 signed inverse Gram at the same original physical point as
`originalPhysicalFrameMatrix`.  `Matrix.inv` is totalized by Mathlib; this
definition by itself deliberately asserts no invertibility. -/
def originalPhysicalSignedCofactor (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) (axialAngle : ℝ) (point : ClosedDisk) :
    Matrix (Fin 3) (Fin 3) ℂ :=
  let frame := originalPhysicalFrameMatrix parameters L epsilon field axialAngle point
  frame.det • (frame⁻¹ * (frame⁻¹).transpose)

/-- The signed cofactor recovered from the actual GC17 flux-deviation
coefficient.  GC17 stores `B_C + I`, so the identity is subtracted here. -/
def actualSignedCofactor {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (frameBase : ‖frameInverseInput parameters admissible epsilon field 0‖ ≤ 1 / 4)
    (seedBase : ‖seedInverseInput admissible rho alpha delta parameter 0‖ ≤ 1 / 4)
    (grade : ℕ) (axialAngle : ℝ) (point : ClosedDisk) : Matrix (Fin 3) (Fin 3) ℂ :=
  let ledger := physicalLedger parameters admissible rho alpha delta parameter epsilon field frameBase seedBase
  operatorMatrix (coefficientPhysicalValue (ledger.val.fluxDeviation grade) axialAngle point) - 1

/-- The accepted actual flux ledger gives exactly
`det(F_C) F_C⁻¹ F_C⁻ᵀ`, including the determinant sign. -/
theorem actualSignedCofactor_eq {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (rho alpha delta parameter epsilon : ℝ) (field : ACore parameters 3)
    (frameBase : ‖frameInverseInput parameters admissible epsilon field 0‖ ≤ 1 / 4)
    (seedBase : ‖seedInverseInput admissible rho alpha delta parameter 0‖ ≤ 1 / 4)
    (grade : ℕ) (axialAngle : ℝ) (point : ClosedDisk) :
    let inverse := operatorMatrix (coefficientPhysicalValue
      ((physicalLedger parameters admissible rho alpha delta parameter epsilon field
        frameBase seedBase).val.frameInverse grade) axialAngle point)
    actualSignedCofactor parameters admissible rho alpha delta parameter epsilon field
        frameBase seedBase grade axialAngle point =
      (physicalFrameMatrix parameters L ell epsilon field axialAngle point).det •
        (inverse * inverse.transpose) := by
  dsimp only [actualSignedCofactor]
  rw [Grad.GaugeCoefficients.Physical.Ledger.Consumer.actualCofactorValue]
  abel

/-- Signed cofactor at the circular reference frame. -/
def referenceSignedCofactor : Matrix (Fin 3) (Fin 3) ℂ :=
  (operatorMatrix referenceFrame).det •
    (operatorMatrix referenceFrame * (operatorMatrix referenceFrame).transpose)

theorem referenceSignedCofactor_eq : referenceSignedCofactor = -1 := by
  unfold referenceSignedCofactor
  rw [referenceFrame_matrix_det, referenceFrame_matrix_transpose,
    referenceFrame_matrix_square]
  simp

/-- BS29 at the circle: the determinant sign makes
`κ = (0,-1,0)`. -/
theorem physicalKappa_reference (angle : ℝ) :
    physicalKappa angle referenceSignedCofactor = ![0, -1, 0] := by
  rw [referenceSignedCofactor_eq]
  funext coordinate
  fin_cases coordinate <;>
    simp [physicalKappa, matrixPairing, physicalRadialVector,
      physicalTangentialVector, physicalToroidalVector, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]
  · ring
  · have trig : ((Real.sin angle : ℂ) ^ 2 + (Real.cos angle : ℂ) ^ 2) = 1 := by
      exact_mod_cast Real.sin_sq_add_cos_sq angle
    rw [← Complex.ofReal_sin, ← Complex.ofReal_cos]
    calc
      _ = -(((Real.sin angle : ℂ) ^ 2 + (Real.cos angle : ℂ) ^ 2)) := by ring
      _ = -1 := by rw [trig]

end Grad.SourceCollar
