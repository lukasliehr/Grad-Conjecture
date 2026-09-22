import QW6CompletedTransfer

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ConstrainedTransfer

open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges

theorem completedTransfer_reverse (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 3 ≤ grade) (field : stateRange parameters first insideFirst grade large) :
    completedTransfer parameters second insideSecond first insideFirst grade large
      (completedTransfer parameters first insideFirst second insideSecond grade large field) = field := by
  refine isClosed_property (stateSmoothEmbedding_denseRange parameters first insideFirst grade large)
    (isClosed_eq ((completedTransfer parameters second insideSecond first insideFirst grade large).continuous.comp
      (completedTransfer parameters first insideFirst second insideSecond grade large).continuous) continuous_id) ?_ field
  intro core
  dsimp only [Function.comp_apply, id_eq]
  rw [completedTransfer_core, completedTransfer_core, constrainedCoreTransfer_reverse]

theorem completedTransfer_self (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 3 ≤ grade) (field : stateRange parameters parameter inside grade large) :
    completedTransfer parameters parameter inside parameter inside grade large field = field := by
  refine isClosed_property (stateSmoothEmbedding_denseRange parameters parameter inside grade large)
    (isClosed_eq (completedTransfer parameters parameter inside parameter inside grade large).continuous continuous_id) ?_ field
  intro core
  dsimp only [Function.comp_apply, id_eq]
  rw [completedTransfer_core, constrainedCoreTransfer_self]

theorem completedTransfer_cocycle (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (third : Seed.Parameters) (insideThird : third ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 3 ≤ grade) (field : stateRange parameters first insideFirst grade large) :
    completedTransfer parameters second insideSecond third insideThird grade large
      (completedTransfer parameters first insideFirst second insideSecond grade large field) =
        completedTransfer parameters first insideFirst third insideThird grade large field := by
  refine isClosed_property (stateSmoothEmbedding_denseRange parameters first insideFirst grade large)
    (isClosed_eq ((completedTransfer parameters second insideSecond third insideThird grade large).continuous.comp
      (completedTransfer parameters first insideFirst second insideSecond grade large).continuous)
      (completedTransfer parameters first insideFirst third insideThird grade large).continuous) ?_ field
  intro core
  dsimp only [Function.comp_apply]
  rw [completedTransfer_core, completedTransfer_core, completedTransfer_core, constrainedCoreTransfer_cocycle]

/-- Continuous real linear equivalence of the actual completed constrained
slices. Both inverse equations are proved from N18 on the dense smooth core. -/
def completedTransferEquiv (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (grade : ℕ) (large : 3 ≤ grade) :
    stateRange parameters first insideFirst grade large ≃L[ℝ]
      stateRange parameters second insideSecond grade large where
  toLinearEquiv := {
    toLinearMap := (completedTransfer parameters first insideFirst second insideSecond grade large).toLinearMap
    invFun := completedTransfer parameters second insideSecond first insideFirst grade large
    left_inv := completedTransfer_reverse parameters first insideFirst second insideSecond grade large
    right_inv := completedTransfer_reverse parameters second insideSecond first insideFirst grade large }
  continuous_toFun := (completedTransfer parameters first insideFirst second insideSecond grade large).continuous
  continuous_invFun := (completedTransfer parameters second insideSecond first insideFirst grade large).continuous

theorem completedTransferEquiv_core (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (field : stateSmoothRange parameters first insideFirst) :
    completedTransferEquiv parameters first insideFirst second insideSecond grade large
      (stateSmoothEmbedding parameters first insideFirst grade large field) =
        stateSmoothEmbedding parameters second insideSecond grade large
          (coreTransferEquiv parameters first insideFirst second insideSecond field) :=
  completedTransfer_core parameters first insideFirst second insideSecond grade large field

theorem completedTransferEquiv_symm (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    (completedTransferEquiv parameters first insideFirst second insideSecond grade large).symm =
      completedTransferEquiv parameters second insideSecond first insideFirst grade large := by
  ext field
  rfl

theorem completedTransferEquiv_bound (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (field : stateRange parameters first insideFirst grade large) :
    ‖completedTransferEquiv parameters first insideFirst second insideSecond grade large field‖ ≤
      transferConstant parameters first second grade * ‖field‖ :=
  completedTransfer_bound parameters first insideFirst second insideSecond grade large field

end Grad.ConstrainedTransfer
