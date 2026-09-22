import QuotientLaplacianConsumer
import SmoothAngularAverage

noncomputable section

namespace Grad.NonlinearDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearQuotientBounds Grad.PhysicalFamily

/-- The axis point of the closed disk. -/
def closedOrigin : ClosedDisk := ⟨0, by simp [closedUnitDisk]⟩

@[simp] theorem closedOrigin_val : closedOrigin.val = 0 := rfl

theorem rotation_mem_closed (angle : ℝ) (point : ClosedDisk) :
    planeRotationAction angle point.val ∈ closedUnitDisk := by
  change ‖planeRotationAction angle point.val‖ ≤ 1
  rw [physicalRotation_norm]
  exact point.property

/-- The actual plane rotation, restricted to the closed disk. -/
def rotatedPoint (angle : ℝ) (point : ClosedDisk) : ClosedDisk :=
  ⟨planeRotationAction angle point.val, rotation_mem_closed angle point⟩

/-- Rotational invariance of one smooth closed-disk scalar, stated on the
closed disk itself: no collar, no extension outside the disk is assumed. -/
def IsRotationInvariant {dimension : ℕ} (field : ClosedJet dimension) : Prop :=
  ∀ (angle : ℝ) (point : ClosedDisk), field.value (rotatedPoint angle point) = field.value point

/-- The accepted Cartesian Laplacian of one closed jet: exactly the cell
coefficient of the accepted `laplacianCore`, with the accepted `partialJet`. -/
def laplacianJet {dimension : ℕ} (field : ClosedJet dimension) : ClosedJet dimension :=
  partialJet 0 (partialJet 0 field) + partialJet 1 (partialJet 1 field)

/-- O11 and O12 on the accepted smooth closed-disk carrier. For every smooth
rotation-invariant closed jet `q0` with `q0(0) = 0`, at every point of the
closed disk (boundary included) `q0(y) = |y|^2 · (I Δ q0)(y)`, where `I` is the
accepted radial integral `integralCoefficient` (the literal O8 kernel
`t log(1/t)`) and `Δ` the accepted Laplacian; and the axis value is
`(I Δ q0)(0) = Δ q0(0) / 4`. Scalars are the case `dimension = 1`. -/
def RadialDivisionGoal : Prop :=
  ∀ (dimension : ℕ) (field : ClosedJet dimension),
    IsRotationInvariant field → field.value closedOrigin = 0 →
    (∀ point : ClosedDisk, field.value point =
        ‖point.val‖ ^ 2 • integralCoefficient (laplacianJet field) point) ∧
    integralCoefficient (laplacianJet field) closedOrigin =
      (1 / 4 : ℝ) • laplacianCoefficient field closedOrigin

end Grad.NonlinearDivision
