import QW2TransferConstraints

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

namespace Grad.ConstrainedTransfer

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.CompletedReality Grad.RealFixedRanges Grad.SmoothingFamily Grad.Cor18 Grad.AxisCore

/-- Literal N18 on the vector coordinate; identity on the free axis and
mean-zero scalar coordinates. -/
def coreTransfer (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain) :
    StateCore parameters →ₗ[ℂ] StateCore parameters :=
  LinearMap.id.prodMap ((seedTransfer parameters first insideFirst second insideSecond).prodMap LinearMap.id)

theorem coreTransfer_apply (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain) (field : StateCore parameters) :
    coreTransfer parameters first insideFirst second insideSecond field =
      (field.1, seedTransfer parameters first insideFirst second insideSecond field.2.1, field.2.2) := rfl

theorem coreTransfer_conjugate (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain) (field : StateCore parameters) :
    xCoreConjugation parameters (coreTransfer parameters first insideFirst second insideSecond field) =
      coreTransfer parameters first insideFirst second insideSecond (xCoreConjugation parameters field) := by
  simp only [coreTransfer_apply, xCoreConjugation, LinearMap.prodMap_apply]
  rw [seedTransfer_conjugate]

theorem smoothState_constraints (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : stateSmoothRange parameters parameter inside) :
    FullConstraints parameters parameter inside field.val := by
  have fixed := ((mem_stateSmoothRange parameters parameter inside field.val).1 field.property).1
  have constraints := fullProjection_constraints parameters parameter inside field.val
  rwa [fixed] at constraints

theorem coreTransfer_mem (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (field : stateSmoothRange parameters first insideFirst) :
    coreTransfer parameters first insideFirst second insideSecond field.val ∈
      stateSmoothRange parameters second insideSecond := by
  apply (mem_stateSmoothRange parameters second insideSecond _).2
  have constraints := smoothState_constraints parameters first insideFirst field
  refine ⟨fullProjection_fixes parameters second insideSecond _ ?_, ?_⟩
  · exact ⟨seedTransfer_vectorConstraints parameters first insideFirst second insideSecond field.val.2.1
      constraints.1, constraints.2⟩
  · rw [coreTransfer_conjugate,
      ((mem_stateSmoothRange parameters first insideFirst field.val).1 field.property).2]

def constrainedCoreTransfer (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain) :
    stateSmoothRange parameters first insideFirst →ₗ[ℝ] stateSmoothRange parameters second insideSecond where
  toFun field := ⟨coreTransfer parameters first insideFirst second insideSecond field.val,
    coreTransfer_mem parameters first insideFirst second insideSecond field⟩
  map_add' firstField secondField := by
    apply Subtype.ext
    exact (coreTransfer parameters first insideFirst second insideSecond).map_add firstField.val secondField.val
  map_smul' scalar field := by
    apply Subtype.ext
    exact ((coreTransfer parameters first insideFirst second insideSecond).restrictScalars ℝ).map_smul scalar field.val

theorem constrainedCoreTransfer_coe (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (field : stateSmoothRange parameters first insideFirst) :
    (constrainedCoreTransfer parameters first insideFirst second insideSecond field).val =
      coreTransfer parameters first insideFirst second insideSecond field.val := rfl

def transferConstant (parameters : PhaseParameters) (first second : Seed.Parameters) (grade : ℕ) : ℝ :=
  1 + |seedTransferGradeConstant parameters first second grade|

theorem transferConstant_nonneg (parameters : PhaseParameters) (first second : Seed.Parameters) (grade : ℕ) :
    0 ≤ transferConstant parameters first second grade := by unfold transferConstant; positivity

theorem coreTransfer_norm_le (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (grade : ℕ) (field : StateCore parameters) :
    ‖stateToGrade parameters grade (coreTransfer parameters first insideFirst second insideSecond field)‖ ≤
      transferConstant parameters first second grade * ‖stateToGrade parameters grade field‖ := by
  rw [coreTransfer_apply, stateToGrade_embedded_norm, stateToGrade_embedded_norm]
  dsimp only
  simp only [aGradeEta_norm, ofCoreLinear_norm_coordinates]
  have vector := seedTransfer_coordinates_bound parameters first insideFirst second insideSecond
    (grade := grade) field.2.1
  have axisNonneg := norm_nonneg (axisToGrade parameters.sigma0 (grade + 1) field.1)
  have vectorNonneg := norm_nonneg (cartesianGradeCoordinates parameters grade field.2.1)
  have scalarNonneg := norm_nonneg (cartesianGradeCoordinates parameters grade field.2.2)
  have absolute := mul_le_mul_of_nonneg_right (le_abs_self
    (seedTransferGradeConstant parameters first second grade)) vectorNonneg
  unfold transferConstant
  nlinarith [mul_nonneg (abs_nonneg (seedTransferGradeConstant parameters first second grade)) axisNonneg,
    mul_nonneg (abs_nonneg (seedTransferGradeConstant parameters first second grade)) scalarNonneg]

end Grad.ConstrainedTransfer
