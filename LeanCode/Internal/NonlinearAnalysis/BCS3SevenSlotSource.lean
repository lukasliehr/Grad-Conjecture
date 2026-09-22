import BCS2CompletedSourceMean
import BKA10SevenSlotInput

noncomputable section

namespace Grad.SourceBoundarySupport

open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace
open Grad.RealFixedRanges Grad.BoundaryKernelAction

/-- AH20's last slot is genuinely mean-free for every original completed
prescribed source. This consumes the actual source trace, without imposing
an extra support hypothesis on arbitrary ambient data. -/
theorem actualSevenSlotTrace_prescribed_source_mean (parameters : PhaseParameters)
    (L : ℝ) (angular cell : ℕ) (large : 3 ≤ angular + cell + 2)
    (x : NegativeTrace parameters angular cell 1)
    (xi : PositiveTrace parameters angular cell 1)
    (source : sourceRange parameters (angular + cell + 2) large) (axial : ℤ) :
    negativeTraceCoefficient parameters angular cell
      (actualSevenSlotTrace parameters L angular cell x xi source.val 6) (0, axial) = 0 := by
  change negativeTraceCoefficient parameters angular cell
    (sourceBoundaryToNegative parameters angular cell
      (sourceOuterTrace parameters L (angular + cell) source.val 2)) (0, axial) = 0
  rw [sourceBoundaryToNegative_coefficient]
  exact sourceOuterTrace_prescribed_fourth_mean parameters L (angular + cell) large source axial

end Grad.SourceBoundarySupport
