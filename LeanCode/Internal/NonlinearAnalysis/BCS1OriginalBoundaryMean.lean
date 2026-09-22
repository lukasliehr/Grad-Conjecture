import SBT8OuterTuple
import QT2SourceDensity

noncomputable section

open Set MeasureTheory
open scoped Topology Interval BigOperators

namespace Grad.SourceBoundarySupport

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.BoundaryTrace
open Grad.SourceBoundaryTrace Grad.QuotientProjection Grad.RealFixedRanges

/-- At angular frequency zero the original boundary coefficient is the
actual angular projection evaluated at the physical point (1,0). -/
theorem originalBoundaryCoefficient_zero_mode {dimension : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension) (cell : ℤ) :
    originalBoundaryCoefficient parameters field (0, cell) =
      ((angularCore parameters 0 field).val cell).value (boundaryDiskPoint 0) := by
  unfold originalBoundaryCoefficient
  rw [fourierCoeff_eq_intervalIntegral _ _ 0]
  rw [angularCore_apply, angularClosedJet_value]
  simp only [neg_zero, fourier_zero, one_smul, zero_add, one_div,
    angularCharacter_zero_mode, boundaryDiskPoint_rotation_zero]

/-- A genuine prescribed angular-mean constraint survives original boundary
Fourier evaluation, with every axial cell retained. -/
theorem originalBoundaryCoefficient_mean_free {dimension : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (meanFree : angularCore parameters 0 field = 0) (cell : ℤ) :
    originalBoundaryCoefficient parameters field (0, cell) = 0 := by
  rw [originalBoundaryCoefficient_zero_mode, meanFree]
  rfl

/-- The scalar fourth component is already mean-free on the full original
prescribed smooth source domain; flatness is unnecessary. -/
theorem prescribedSmoothSource_fourth_mean (parameters : PhaseParameters)
    (source : sourceSmoothRange parameters) :
    angularCore parameters 0 (source.val 3) = 0 := by
  have fixed := ((mem_sourceSmoothRange parameters source.val).mp source.property).1
  have constrained := quotientProjection_constrained parameters source.val
  rw [fixed] at constrained
  exact constrained.1

/-- Literal F2 = h/L at r=1 has no angular zero coefficient for prescribed
smooth data, in the original completed trace coordinates. -/
theorem fourthOuterTrace_prescribed_core_mean (parameters : PhaseParameters)
    (L : ℝ) (power : ℕ) (source : sourceSmoothRange parameters) (cell : ℤ) :
    sourceBoundaryCoefficient parameters power
      (fourthOuterTrace parameters L power
        (quotientEta parameters (power + 2) source.val)) (0, cell) = 0 := by
  rw [fourthOuterTrace_core, originalBoundaryCoefficient_mean_free parameters
    (source.val 3) (prescribedSmoothSource_fourth_mean parameters source), smul_zero]

end Grad.SourceBoundarySupport
