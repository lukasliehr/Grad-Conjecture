import Q24GradeCompatibility
import QW10Consumer

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1600000

namespace Grad.Q24Realization

open Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.SmoothingFamily Grad.RealFixedRanges Grad.ConstrainedTransfer
open Grad.ImplementationReadiness

/-- The independently constructed ambient Q24 transfer has exactly the
accepted COR27 N18 formula on the common original smooth product. -/
theorem completedReferenceTransfer_stateToGrade (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (state : StateCore parameters) :
    completedReferenceTransfer parameters reference insideR seed insideS grade
      (stateToGrade parameters grade state) =
    stateToGrade parameters grade (coreTransfer parameters reference insideR seed insideS state) := by
  change statePack (axisToGrade parameters.sigma0 (grade + 1) state.1)
    (completedSeedTransfer parameters reference insideR seed insideS grade
      (fieldEmbed parameters 3 grade state.2.1)) (fieldEmbed parameters 1 grade state.2.2) = _
  rw [completedSeedTransfer_core]
  rfl

/-- Q24's actual ambient expression is the accepted completed constrained
equivalence, not a new projection or an assumed range-preserving map. -/
theorem completedReferenceTransfer_actual (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 3 ≤ grade)
    (state : stateRange parameters reference insideR grade large) :
    completedReferenceTransfer parameters reference insideR seed insideS grade state.val =
      (completedTransfer parameters reference insideR seed insideS grade large state).val :=
  completedTransfer_ambient_agreement parameters reference insideR seed insideS grade large
    (completedReferenceTransfer parameters reference insideR seed insideS grade)
    (completedReferenceTransfer_contDiff parameters reference insideR seed insideS grade).continuous
    (fun core => completedReferenceTransfer_stateToGrade parameters reference insideR seed insideS grade core.val) state

theorem completedReferenceTransfer_mem (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 3 ≤ grade)
    (state : stateRange parameters reference insideR grade large) :
    completedReferenceTransfer parameters reference insideR seed insideS grade state.val ∈
      stateRange parameters seed insideS grade large := by
  rw [completedReferenceTransfer_actual parameters reference insideR seed insideS grade large state]
  exact (completedTransfer parameters reference insideR seed insideS grade large state).property

theorem completedReferenceTransfer_reverse (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 3 ≤ grade)
    (state : stateRange parameters reference insideR grade large) :
    completedReferenceTransfer parameters seed insideS reference insideR grade
      (completedReferenceTransfer parameters reference insideR seed insideS grade state.val) = state.val := by
  rw [completedReferenceTransfer_actual parameters reference insideR seed insideS grade large state,
    completedReferenceTransfer_actual parameters seed insideS reference insideR grade large,
    completedTransfer_reverse]

end Grad.Q24Realization
