import QP3AffineModes

noncomputable section

namespace Grad.QuotientProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.AxisCore

def meanPair (parameters : PhaseParameters) :
    SmoothQuotient parameters →ₗ[ℂ] SmoothQuotient parameters :=
  (removeMean parameters 2).comp (removeMean parameters 3)

theorem meanPair_apply (parameters : PhaseParameters) (field : SmoothQuotient parameters) :
    meanPair parameters field =
      ![field 0, field 1, field 2 - angularCore parameters 0 (field 2),
        field 3 - angularCore parameters 0 (field 3)] := by
  funext coordinate
  fin_cases coordinate <;> rfl

theorem firstMode_meanPair (parameters : PhaseParameters) (field : SmoothQuotient parameters) :
    firstMode parameters (meanPair parameters field) = firstMode parameters field := rfl

theorem modeProjection_meanPair (parameters : PhaseParameters) (field : SmoothQuotient parameters) :
    modeProjection parameters (meanPair parameters field) = modeProjection parameters field := by
  rw [modeProjection_apply, firstMode_meanPair, modeProjection_apply]

theorem affineTrace_meanPair (parameters : PhaseParameters) (field : SmoothQuotient parameters) :
    affineTrace parameters (meanPair parameters field) = affineTrace parameters field := rfl

theorem quotientProjection_apply (parameters : PhaseParameters) (field : SmoothQuotient parameters) :
    quotientProjection parameters field = meanPair parameters field - modeProjection parameters field -
      affineInsertion parameters (affineTrace parameters field) := by
  change (meanPair parameters field - modeProjection parameters (meanPair parameters field)) -
    affineInsertion parameters (affineTrace parameters
      (meanPair parameters field - modeProjection parameters (meanPair parameters field))) = _
  rw [modeProjection_meanPair, map_sub, affineTrace_meanPair,
    affineTrace_modeProjection, sub_zero]

theorem affineTrace_quotientProjection (parameters : PhaseParameters)
    (field : SmoothQuotient parameters) :
    affineTrace parameters (quotientProjection parameters field) = 0 := by
  rw [quotientProjection_apply, map_sub, map_sub, affineTrace_meanPair,
    affineTrace_modeProjection, affineTrace_insertion, sub_zero, sub_self]

theorem modeProjection_quotientProjection (parameters : PhaseParameters)
    (field : SmoothQuotient parameters) :
    modeProjection parameters (quotientProjection parameters field) = 0 := by
  rw [quotientProjection_apply, map_sub, map_sub, modeProjection_meanPair,
    modeProjection_idempotent, modeProjection_affineInsertion, sub_self, sub_zero]

theorem quotientProjection_third (parameters : PhaseParameters) (field : SmoothQuotient parameters) :
    quotientProjection parameters field 2 = field 2 - angularCore parameters 0 (field 2) := by
  rw [quotientProjection_apply, meanPair_apply, modeProjection_apply]
  change (field 2 - angularCore parameters 0 (field 2)) - 0 - 0 = _
  simp

theorem quotientProjection_fourth (parameters : PhaseParameters) (field : SmoothQuotient parameters) :
    quotientProjection parameters field 3 = field 3 - angularCore parameters 0 (field 3) := by
  rw [quotientProjection_apply, meanPair_apply, modeProjection_apply]
  change (field 3 - angularCore parameters 0 (field 3)) - 0 - 0 = _
  simp

theorem quotientProjection_third_mean (parameters : PhaseParameters)
    (field : SmoothQuotient parameters) :
    angularCore parameters 0 (quotientProjection parameters field 2) = 0 := by
  rw [quotientProjection_third, map_sub, angularCore_projection, if_pos rfl, sub_self]

theorem quotientProjection_fourth_mean (parameters : PhaseParameters)
    (field : SmoothQuotient parameters) :
    angularCore parameters 0 (quotientProjection parameters field 3) = 0 := by
  rw [quotientProjection_fourth, map_sub, angularCore_projection, if_pos rfl, sub_self]

def IsConstrained (parameters : PhaseParameters) (field : SmoothQuotient parameters) : Prop :=
  angularCore parameters 0 (field 3) = 0 ∧ angularCore parameters 0 (field 2) = 0 ∧
    modeProjection parameters field = 0 ∧ affineTrace parameters field = 0

theorem quotientProjection_constrained (parameters : PhaseParameters)
    (field : SmoothQuotient parameters) : IsConstrained parameters (quotientProjection parameters field) :=
  ⟨quotientProjection_fourth_mean parameters field, quotientProjection_third_mean parameters field,
    modeProjection_quotientProjection parameters field, affineTrace_quotientProjection parameters field⟩

theorem quotientProjection_fixes (parameters : PhaseParameters) (field : SmoothQuotient parameters)
    (constrained : IsConstrained parameters field) : quotientProjection parameters field = field := by
  obtain ⟨fourth, third, mode, affine⟩ := constrained
  rw [quotientProjection_apply, mode, affine, map_zero, sub_zero, sub_zero, meanPair_apply,
    third, fourth, sub_zero, sub_zero]
  funext coordinate
  fin_cases coordinate <;> rfl

theorem quotientProjection_idempotent (parameters : PhaseParameters)
    (field : SmoothQuotient parameters) :
    quotientProjection parameters (quotientProjection parameters field) =
      quotientProjection parameters field :=
  quotientProjection_fixes parameters _ (quotientProjection_constrained parameters field)

theorem quotientProjection_range (parameters : PhaseParameters) (field : SmoothQuotient parameters) :
    (∃ source, quotientProjection parameters source = field) ↔ IsConstrained parameters field := by
  constructor
  · rintro ⟨source, rfl⟩
    exact quotientProjection_constrained parameters source
  · intro constrained
    exact ⟨field, quotientProjection_fixes parameters field constrained⟩

end Grad.QuotientProjection
