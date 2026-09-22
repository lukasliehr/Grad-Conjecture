import ACP11ExactPolarForceAlgebra

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.ActualCurrentPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollar Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

def originalPolarForceRow (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2) (axialAngle polarAngle : ℝ)
    (point : ClosedDisk) (component : Fin 3) : ℂ :=
  let frame := originalPhysicalFrameMatrix parameters L epsilon field axialAngle point
  let rotated := rotatedPhysicalFrameMatrix parameters 1 1 epsilon field axialAngle point *
    Matrix.diagonal ![1, 1, (L : ℂ)⁻¹]
  rawPolarForceRow kind (rotated * polarDomainMatrix polarAngle + frame * polarDomainDerivative polarAngle)
    ((polarDomainMatrix polarAngle).transpose * frame⁻¹) component

def forceReferenceRow (kind : Fin 2) (component : Fin 3) : ℂ :=
  if kind = 0 ∧ component = 0 then -2 else 0

theorem originalPolarForceRow_deviation (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (axialAngle polarAngle : ℝ) (point : ClosedDisk) (component : Fin 3) :
    originalPolarForceRow parameters L epsilon field kind axialAngle polarAngle point component -
      forceReferenceRow kind component =
        forcePolarComponent kind polarAngle (originalForceMatrix parameters L epsilon field axialAngle point) component := by
  have margin := originalCoefficient_low_margin parameters L rho epsilon field low
  have invId := (originalInverseFamily_matrix_identity parameters L epsilon field margin.2.2 0 axialAngle point).2
  rw [originalInverseFamily_eq_matrixInverse parameters L rho epsilon field low] at invId
  unfold originalPolarForceRow
  rw [rawPolarForceRow_exact _ _ _ invId]
  exact add_sub_cancel_right _ _

/-- Literal AD10 force rows, with the circular row removed before taking
their full two-frequency coefficients. No independent coefficient premise. -/
theorem originalPolarForceRow_doubleCoefficient (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (mode : ℤ × ℤ) :
    angularCoefficient (fun angle => angularCoefficient (fun axialAngle =>
      originalPolarForceRow parameters L epsilon field kind axialAngle angle
        (polarClosedPoint radius angle nonnegative bounded) component - forceReferenceRow kind component) mode.2) mode.1 =
      forceScalar parameters L rho epsilon field kind low component 0 radius mode := by
  simp_rw [originalPolarForceRow_deviation parameters L rho epsilon field kind low]
  exact actualForce_doubleCoefficient parameters L rho epsilon field kind low component radius nonnegative bounded mode

end Grad.ActualCurrentPrimitives
