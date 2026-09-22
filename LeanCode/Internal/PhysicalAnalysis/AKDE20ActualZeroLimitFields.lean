import AKDE19ClosedPhysicalDerivativeZero

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
open Set
open scoped ContDiff
namespace Grad.OriginalCellFamily
open Grad.CartesianState Grad.ClosedJets Grad.Constraints Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.OriginalParameterEvaluation Grad.PhysicalFamily Grad.NonlinearQuotient Grad.AxisSplit
open Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit Grad.Q24Realization

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}
    {inverse : OriginalNewtonInverse neighborhood cellLength loss}

theorem constructedTilt_of_limit_zero (scale : OriginalNewtonScale inverse) (point : OriginalFiniteParameter)
    (zero : scale.parameterLimit point = 0) (cell : ℝ) : constructedTilt scale point cell=0 := by
  simp [constructedTilt,zero,smoothingChartCore,originalRealTilt,planarValue,physicalRealPart]
  rfl

theorem constructedRemainder_of_limit_zero (scale : OriginalNewtonScale inverse) (point : OriginalFiniteParameter)
    (member : point ∈ scale.openParameterDomain) (zero : scale.parameterLimit point = 0)
    (disk : ClosedDisk) (cell : ℝ) : constructedCellRemainder scale point disk.val cell=0 := by
  rw [constructedCellRemainder_original scale point member]
  have coreZero : (constructedChartState scale point (scale.parameterLimit_admissible point member).1).2.1=0 := by
    simp [constructedChartState,zero]
  rw [coreZero]
  change physicalRealPart 3 (originalCellField (0 : ACore parameters 3) disk.val cell)=0
  rw [originalCellField_coreValue]
  simp [coreValue,physicalRealPart]
  rfl

end Grad.OriginalCellFamily
