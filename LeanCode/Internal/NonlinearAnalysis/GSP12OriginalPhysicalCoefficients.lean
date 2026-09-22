import GSP10ActualGaugeMoments
import GSP11ActualSigmaMoments

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.ActualGaugeSigmaPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarCoefficients Grad.SourceCollar Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.SourceCollarDivision

/-- AE4's two gauge rows in the original polar coordinate order (radial, angular, toroidal). -/
def originalGaugeRow (parameters : PhaseParameters) (L rho alpha delta parameter epsilon : ℝ)
    (field : ACore parameters 3) (kind : Fin 2)
    (axialAngle polarAngle : ℝ) (point : ClosedDisk) (component : Fin 3) : ℂ :=
  polarMatrixEntry (if kind = 0 then 1 else 2) component polarAngle
    (originalPhysicalGaugeMatrix parameters L rho alpha delta parameter epsilon field axialAngle point)

theorem gaugeScalar_doubleCoefficient (parameters : PhaseParameters) (L rho alpha delta parameter epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (kind : Fin 2) (component : Fin 3) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (mode : ℤ × ℤ) :
    angularCoefficient (fun angle => angularCoefficient (fun axialAngle =>
      originalGaugeRow parameters L rho alpha delta parameter epsilon field kind axialAngle angle
        (polarClosedPoint radius angle nonnegative bounded) component -
        (if (if kind = 0 then (1 : Fin 3) else 2) = component then 1 else 0)) mode.2) mode.1 =
      gaugeScalar parameters L rho alpha delta parameter epsilon field low kind component 0 radius mode := by
  have exactCoefficient := polarEntry_doubleCoefficient parameters
    (originalGaugeDeviation parameters L rho alpha delta parameter epsilon field)
    (originalGaugeDeviation_coherent parameters L rho alpha delta parameter epsilon field low)
    (if kind = 0 then 1 else 2) component radius nonnegative bounded mode
  simp_rw [originalGaugeDeviation_matrix parameters L rho alpha delta parameter epsilon field low,
    polarMatrixEntry_sub, polarMatrixEntry_one] at exactCoefficient
  exact exactCoefficient

/-- The circular flux row is (-1,0,0), hence the deviation is sigma+e_radial. -/
theorem sigmaScalar_doubleCoefficient (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (mode : ℤ × ℤ) :
    angularCoefficient (fun angle => angularCoefficient (fun axialAngle =>
      originalSigmaRow parameters L epsilon field axialAngle angle
        (polarClosedPoint radius angle nonnegative bounded) component +
        (if (0 : Fin 3) = component then 1 else 0)) mode.2) mode.1 =
      sigmaScalar parameters L rho epsilon field low component 0 radius mode := by
  have exactCoefficient := polarEntry_doubleCoefficient parameters
    (originalCofactorDeviation parameters L epsilon field)
    (originalCofactorDeviation_coherent parameters L rho epsilon field low)
    0 component radius nonnegative bounded mode
  simp_rw [originalCofactorDeviation_matrix parameters L rho epsilon field low,
    polarMatrixEntry_add, polarMatrixEntry_one] at exactCoefficient
  exact exactCoefficient

end Grad.ActualGaugeSigmaPrimitives
