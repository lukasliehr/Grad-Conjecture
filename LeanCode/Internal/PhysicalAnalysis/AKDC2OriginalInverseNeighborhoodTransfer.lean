import AKDC1OriginalSmoothingContinuity
import AKCZ16OriginalZeroBranchSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3500
open Set

namespace Grad.NashMoser.OriginalIteration
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.ConstrainedGrades
open Grad.SmoothingFamily Grad.Q24Realization Grad.NashMoser.OriginalLimit Grad.SmoothForward
open Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates Grad.NashMoser.InverseCalculus

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}
    (inverse : OriginalNewtonInverse neighborhood cellLength loss)

/-- The additional actual PC left identity needed for parameter calculus.
The CY right-inverse construction and its original contract are unchanged. -/
structure OriginalNewtonInverse.LeftLaw : Prop where
  left : ∀ finite (member : finite ∈ neighborhood.parameterDomain) state
    (low : stateSize parameters reference inside base 0 state ≤ 2*neighborhood.radius) direction,
    inverse.map finite state
      (literalPhysicalSmoothForward parameters cellLength reference inside finite.1
        (neighborhood.patchInside (neighborhood.seedInside finite member)) (finite.2,state)
        (neighborhood.axis state low) direction) = direction

namespace OriginalNewtonInverse

/-- Reindexing into CZ's output grade s+4 preserves the independent low
source grade base+loss exactly. This is one fixed finite loss. -/
def parameterLoss (_inverse : OriginalNewtonInverse neighborhood cellLength loss) : ℕ := base+loss-4

theorem parameterLoss_index : inverse.parameterLoss+4 = base+loss := by
  dsimp [parameterLoss]
  have := neighborhood.baseLarge
  omega

/-- The original uniform one-high PC bound, applied to an actual branch in
its fixed low product, gives precisely the tame input for CZ. -/
theorem branch_tame (domain : Set OriginalFiniteParameter) (included : domain ⊆ neighborhood.parameterDomain)
    (branch : OriginalFiniteParameter → stateSmoothRange parameters reference inside)
    (low : ∀ point ∈ domain, stateSize parameters reference inside base 0 (branch point) ≤ 2*neighborhood.radius)
    (grade : ℕ) (point : OriginalFiniteParameter) (member : point ∈ domain)
    (source : sourceSmoothRange parameters) :
    ‖stateSmoothEmbedding parameters reference inside (grade+4) (branchGrade_large grade)
      (inverse.map point (branch point) source)‖ ≤ inverse.constant grade *
        (‖sourceSmoothEmbedding parameters (grade+inverse.parameterLoss+4)
          (branchGrade_large (grade+inverse.parameterLoss)) source‖+
        (1+‖stateSmoothEmbedding parameters reference inside (grade+inverse.parameterLoss+4)
          (branchGrade_large (grade+inverse.parameterLoss)) (branch point)‖)*
          ‖sourceSmoothEmbedding parameters (inverse.parameterLoss+4)
            (branchGrade_large inverse.parameterLoss) source‖) := by
  have highIndex : grade+inverse.parameterLoss+4 = base+(grade+loss) := by
    have := inverse.parameterLoss_index
    omega
  simp only [stateSmoothEmbedding_norm,sourceSmoothEmbedding_norm]
  rw [← stateOriginalSeminorms_apply parameters reference inside (grade+inverse.parameterLoss+4),highIndex,inverse.parameterLoss_index]
  exact (originalStateNorm_le_size parameters reference inside base grade (grade+4)
    (branchGrade_large grade) (by have := neighborhood.baseLarge; omega) _).trans
      (inverse.bounded grade point (included member) (branch point) (low point member) source)

end OriginalNewtonInverse
end Grad.NashMoser.OriginalIteration
