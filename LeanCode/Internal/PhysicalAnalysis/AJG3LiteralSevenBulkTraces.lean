import AJG2SameBulkNegativeKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.AnnularPhysicalReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularReconstruction
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.PhaseAlgebra

/-- The seven scalar traces of an actual collected bulk input. -/
def bulkSevenTrace (parameters : PhaseParameters) (radius : RadialPoint) (field : CellL2 7) :
    SevenSlotTrace (radialKernelParameters parameters radius) 0 0 :=
  WithLp.toLp 2 (fun slot => fullNegativeKernelAction (radialKernelParameters parameters radius) 0 0
    (sevenInputSlotKernel (radialKernelParameters parameters radius) slot)
    (bulkNegativeLift parameters radius 7 field))

theorem bulkSevenTrace_coefficient (parameters : PhaseParameters) (radius : RadialPoint) (field : CellL2 7)
    (slot : Fin 7) (mode : ℤ × ℤ) :
    negativeTraceCoefficient (radialKernelParameters parameters radius) 0 0
      (bulkSevenTrace parameters radius field slot) mode 0 =
      (Real.exp (radialPhase parameters radius.val mode.2) : ℂ)⁻¹ * field mode slot := by
  change negativeTraceCoefficient _ 0 0 (fullNegativeKernelAction _ 0 0 _ _) mode 0 = _
  rw [sevenInputSlotKernel, coordinateProjectionKernel_action_coefficient, bulkNegativeLift_coefficient]
  rfl

theorem bulkSevenTrace_flatten (parameters : PhaseParameters) (radius : RadialPoint) (field : CellL2 7) :
    sevenSlotFlatten (radialKernelParameters parameters radius) 0 0 (bulkSevenTrace parameters radius field) =
      bulkNegativeLift parameters radius 7 field := by
  apply NegativeTrace.ext_coefficient (radialKernelParameters parameters radius) 0 0
  intro mode
  apply PiLp.ext
  intro slot
  rw [sevenSlotFlatten_coefficient, bulkSevenTrace_coefficient, bulkNegativeLift_coefficient]
  rfl

theorem bulkSevenTrace_meanFree (parameters : PhaseParameters) (radius : RadialPoint) (field : CellL2 7)
    (slot : Fin 7) (meanFree : ∀ cell : ℤ, field (0, cell) slot = 0) :
    IsAngularMeanFree (radialKernelParameters parameters radius) 0 0 (bulkSevenTrace parameters radius field slot) := by
  intro cell
  apply PiLp.ext
  intro coordinate
  have zero : coordinate = 0 := Fin.eq_zero coordinate
  subst coordinate
  rw [bulkSevenTrace_coefficient, meanFree, mul_zero]
  rfl

theorem bulkSevenTrace_derivative (parameters : PhaseParameters) (radius : RadialPoint) (field : CellL2 7)
    (slot derivativeSlot : Fin 7)
    (derivative : ∀ mode : ℤ × ℤ, field mode derivativeSlot = (Complex.I * (mode.1 : ℂ)) * field mode slot) :
    IsAngularDerivative (radialKernelParameters parameters radius) 0 0
      (bulkSevenTrace parameters radius field slot) (bulkSevenTrace parameters radius field derivativeSlot) := by
  intro mode
  apply PiLp.ext
  intro coordinate
  have zero : coordinate = 0 := Fin.eq_zero coordinate
  subst coordinate
  change negativeTraceCoefficient _ 0 0 (bulkSevenTrace parameters radius field derivativeSlot) mode 0 =
    (Complex.I * (mode.1 : ℂ)) * negativeTraceCoefficient _ 0 0 (bulkSevenTrace parameters radius field slot) mode 0
  rw [bulkSevenTrace_coefficient, bulkSevenTrace_coefficient, derivative]
  ring

end Grad.AnnularPhysicalReconstruction
