import AKU40ActualCurrentForceTaylor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.AxisSplit Grad.AxisJet Grad.NonlinearRange Grad.NonlinearProduct
open Grad.GaugeCoefficients.Physical.Frame Grad.NonlinearDivision

theorem axisConstantCore_physical {parameters : PhaseParameters} {dimension : ℕ}
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) (point : ClosedDisk) (angle : ℝ) :
    coreValue (axisConstantCore data) point angle = axisPhysicalValue data angle := by
  rw [axisConstantCore,vectorAxisProfileCore_physical]
  rfl

theorem partialCore_axisConstantCore {parameters : PhaseParameters} {dimension : ℕ}
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) (direction : Fin 2) :
    partialCore parameters direction (axisConstantCore data) = 0 := by
  apply acore_ext
  intro cell point
  rw [partialCore_val,axisConstantCore_val]
  exact partial_constantValueJet_value direction (data.val cell) point

theorem traceFirst_physical {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (direction : Fin 2) (angle : ℝ) :
    axisPhysicalValue (traceFirst direction field) angle =
      coreValue (partialCore parameters direction field) closedOrigin angle :=
  traceZero_physical (partialCore parameters direction field) angle

theorem traceZero_dot_physical {parameters : PhaseParameters}
    (first second : ACore parameters 3) (angle : ℝ) :
    axisPhysicalValue (traceZero (dotOperation parameters first second)) angle 0 =
      Grad.NonlinearQuotient.complexDot (axisPhysicalValue (traceZero first) angle)
        (axisPhysicalValue (traceZero second) angle) := by
  rw [traceZero_physical,coreValue_dotOperation,traceZero_physical,traceZero_physical]

/-- The genuine original Fourier product of two axis vectors. -/
def axisDot {parameters : PhaseParameters}
    (first second : Grad.AxisCore.AxisSmoothCore parameters 3) : Grad.AxisCore.AxisSmoothCore parameters 1 :=
  traceZero (dotOperation parameters (axisConstantCore first) (axisConstantCore second))

theorem axisDot_physical {parameters : PhaseParameters}
    (first second : Grad.AxisCore.AxisSmoothCore parameters 3) (angle : ℝ) :
    axisPhysicalValue (axisDot first second) angle 0 =
      Grad.NonlinearQuotient.complexDot (axisPhysicalValue first angle) (axisPhysicalValue second angle) := by
  rw [axisDot,traceZero_dot_physical,traceZero_axisConstantCore,traceZero_axisConstantCore]

theorem traceZero_dot_eq_axisDot {parameters : PhaseParameters}
    (first second : ACore parameters 3) :
    traceZero (dotOperation parameters first second) = axisDot (traceZero first) (traceZero second) := by
  apply axisPhysicalValue_ext
  intro angle
  apply PiLp.ext
  intro index
  have only : index = 0 := Subsingleton.elim _ _
  subst index
  rw [traceZero_dot_physical,axisDot_physical]

theorem axisDot_comm {parameters : PhaseParameters}
    (first second : Grad.AxisCore.AxisSmoothCore parameters 3) : axisDot first second = axisDot second first := by
  apply axisPhysicalValue_ext
  intro angle
  apply PiLp.ext
  intro index
  have only : index = 0 := Subsingleton.elim _ _
  subst index
  rw [axisDot_physical,axisDot_physical]
  simp only [Grad.NonlinearQuotient.complexDot,mul_comm]

theorem originalLinearTaylorCore_physical {parameters : PhaseParameters} {dimension : ℕ}
    (field : ACore parameters dimension) (point : ClosedDisk) (angle : ℝ) :
    coreValue (originalLinearTaylorCore field) point angle =
      point.val 0 • coreValue (partialCore parameters 0 field) closedOrigin angle +
        point.val 1 • coreValue (partialCore parameters 1 field) closedOrigin angle := by
  rw [originalLinearTaylorCore,coreValue_add,coreValue_coordinate,coreValue_coordinate,
    axisConstantCore_physical,axisConstantCore_physical,traceFirst_physical,traceFirst_physical]

end Grad.FinitePhysicalJetLift
