import QW3CoreTransfer

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ConstrainedTransfer

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.RealFixedRanges Grad.SmoothingFamily Grad.Cor18

theorem coreTransfer_reverse (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (field : StateCore parameters)
    (poloidal : poloidalCorrection parameters first insideFirst field.2.1 = 0)
    (toroidal : toroidalCorrection parameters first insideFirst field.2.1 = 0) :
    coreTransfer parameters second insideSecond first insideFirst
      (coreTransfer parameters first insideFirst second insideSecond field) = field := by
  rw [coreTransfer_apply, coreTransfer_apply]
  exact Prod.ext rfl (Prod.ext (seedTransfer_reverse parameters first insideFirst second insideSecond
    field.2.1 poloidal toroidal) rfl)

theorem coreTransfer_self (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : StateCore parameters)
    (poloidal : poloidalCorrection parameters parameter inside field.2.1 = 0)
    (toroidal : toroidalCorrection parameters parameter inside field.2.1 = 0) :
    coreTransfer parameters parameter inside parameter inside field = field := by
  rw [coreTransfer_apply]
  exact Prod.ext rfl (Prod.ext (seedTransfer_identity parameters parameter inside field.2.1 poloidal toroidal) rfl)

theorem constrainedCoreTransfer_reverse (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (field : stateSmoothRange parameters first insideFirst) :
    constrainedCoreTransfer parameters second insideSecond first insideFirst
      (constrainedCoreTransfer parameters first insideFirst second insideSecond field) = field := by
  have constraints := smoothState_constraints parameters first insideFirst field
  apply Subtype.ext
  exact (constrainedCoreTransfer_coe parameters second insideSecond first insideFirst _).trans
    ((congrArg (coreTransfer parameters second insideSecond first insideFirst)
      (constrainedCoreTransfer_coe parameters first insideFirst second insideSecond field)).trans
      (coreTransfer_reverse parameters first insideFirst second insideSecond field.val constraints.1.2.1 constraints.1.2.2.1))

theorem constrainedCoreTransfer_self (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (field : stateSmoothRange parameters parameter inside) :
    constrainedCoreTransfer parameters parameter inside parameter inside field = field := by
  have constraints := smoothState_constraints parameters parameter inside field
  apply Subtype.ext
  exact (constrainedCoreTransfer_coe parameters parameter inside parameter inside field).trans
    (coreTransfer_self parameters parameter inside field.val constraints.1.2.1 constraints.1.2.2.1)

theorem coreTransfer_cocycle (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (third : Seed.Parameters) (insideThird : third ∈ Seed.parameterDomain) (field : StateCore parameters) :
    coreTransfer parameters second insideSecond third insideThird
      (coreTransfer parameters first insideFirst second insideSecond field) =
        coreTransfer parameters first insideFirst third insideThird field := by
  simp only [coreTransfer_apply]
  rw [seedTransfer_cocycle]

theorem constrainedCoreTransfer_cocycle (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (third : Seed.Parameters) (insideThird : third ∈ Seed.parameterDomain)
    (field : stateSmoothRange parameters first insideFirst) :
    constrainedCoreTransfer parameters second insideSecond third insideThird
      (constrainedCoreTransfer parameters first insideFirst second insideSecond field) =
        constrainedCoreTransfer parameters first insideFirst third insideThird field := by
  apply Subtype.ext
  exact (constrainedCoreTransfer_coe parameters second insideSecond third insideThird _).trans
    ((congrArg (coreTransfer parameters second insideSecond third insideThird)
      (constrainedCoreTransfer_coe parameters first insideFirst second insideSecond field)).trans
      ((coreTransfer_cocycle parameters first insideFirst second insideSecond third insideThird field.val).trans
        (constrainedCoreTransfer_coe parameters first insideFirst third insideThird field).symm))

/-- The actual formula-defined N18 real linear equivalence between the
canonical smooth full constrained slices. Its inverse is the reverse formula. -/
def coreTransferEquiv (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain) :
    stateSmoothRange parameters first insideFirst ≃ₗ[ℝ] stateSmoothRange parameters second insideSecond where
  toLinearMap := constrainedCoreTransfer parameters first insideFirst second insideSecond
  invFun := constrainedCoreTransfer parameters second insideSecond first insideFirst
  left_inv := constrainedCoreTransfer_reverse parameters first insideFirst second insideSecond
  right_inv := constrainedCoreTransfer_reverse parameters second insideSecond first insideFirst

theorem coreTransferEquiv_apply (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (field : stateSmoothRange parameters first insideFirst) :
    (coreTransferEquiv parameters first insideFirst second insideSecond field).val =
      (field.val.1, seedTransfer parameters first insideFirst second insideSecond field.val.2.1, field.val.2.2) := rfl

theorem coreTransferEquiv_symm_apply (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (field : stateSmoothRange parameters second insideSecond) :
    (coreTransferEquiv parameters first insideFirst second insideSecond).symm field =
      coreTransferEquiv parameters second insideSecond first insideFirst field := rfl

theorem coreTransferEquiv_bound (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (grade : ℕ) (field : stateSmoothRange parameters first insideFirst) :
    ‖stateToGrade parameters grade (coreTransferEquiv parameters first insideFirst second insideSecond field).val‖ ≤
      transferConstant parameters first second grade * ‖stateToGrade parameters grade field.val‖ :=
  coreTransfer_norm_le parameters first insideFirst second insideSecond grade field.val

end Grad.ConstrainedTransfer
