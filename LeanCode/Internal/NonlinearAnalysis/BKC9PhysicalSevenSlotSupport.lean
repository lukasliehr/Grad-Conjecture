import BKC8ActualMassSupport
import BCS3SevenSlotSource

noncomputable section

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.SourceBoundarySupport Grad.RealFixedRanges
open Grad.QuotientProjection Grad.AxisCore

theorem actualSevenSlotTrace_rotation_source_meanFree
    (parameters : PhaseParameters) (L : ℝ) (angular cell : ℕ)
    (x : NegativeTrace parameters angular cell 1)
    (xi : PositiveTrace parameters angular cell 1)
    (source : ZAmbient parameters (angular + cell + 2)) :
    IsAngularMeanFree parameters angular cell
      (actualSevenSlotTrace parameters L angular cell x xi source 5) := by
  intro axial
  change negativeTraceCoefficient parameters angular cell
    (sourceBoundaryToNegative parameters angular cell
      (rotationOuterTrace parameters (angular + cell) source)) (0, axial) = 0
  rw [sourceBoundaryToNegative_coefficient]
  change sourceBoundaryCoefficient parameters (angular + cell)
    (boundaryAngular (highForceTrace parameters (angular + cell) source)) (0, axial) = 0
  rw [boundaryAngular_coefficient]
  simp

theorem positiveCellToNegative_meanFree {dimension : ℕ}
    (parameters : PhaseParameters) (angular cell : ℕ)
    (field : PositiveTrace parameters angular cell dimension)
    (supported : ∀ axial, positiveTraceCoefficient parameters angular cell field (0, axial) = 0) :
    IsAngularMeanFree parameters angular cell
      (positiveCellToNegative parameters angular cell field) := by
  intro axial
  rw [positiveCellToNegative_coefficient, supported axial, smul_zero]

/-- AE17's support on the original completed prescribed source domain and
the original mean-free retained scalar. -/
theorem actualSevenSlotTrace_known_support
    (parameters : PhaseParameters) (L : ℝ) (angular cell : ℕ)
    (large : 3 ≤ angular + cell + 2)
    (x : NegativeTrace parameters angular cell 1)
    (xi : PositiveTrace parameters angular cell 1)
    (xiMeanFree : ∀ axial, positiveTraceCoefficient parameters angular cell xi (0, axial) = 0)
    (source : sourceRange parameters (angular + cell + 2) large) :
    KnownSevenSlotSupport parameters L angular cell
      (actualSevenSlotTrace parameters L angular cell x xi source.val) := by
  refine ⟨actualSevenSlotTrace_rotation_source_meanFree parameters L angular cell
    x xi source.val, ?_⟩
  apply IsAngularMeanFree.add
  · intro axial
    exact actualSevenSlotTrace_prescribed_source_mean parameters L angular cell large
      x xi source axial
  · apply IsAngularMeanFree.smul
    exact positiveCellToNegative_meanFree parameters angular cell xi xiMeanFree

end Grad.BoundaryKernelAction
