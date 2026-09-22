import QP1LiteralMaps

noncomputable section

open scoped BigOperators

namespace Grad.QuotientProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.GaugeCoefficients.Radial Grad.AxisCore
open Grad.RepresentedKernel.SpatialProduct

theorem angular_reflection (parameters : PhaseParameters) (mode : ℤ)
    (field : ACore parameters 1) :
    angularCore parameters mode (reflection parameters field) =
      reflection parameters (angularCore parameters (-mode) field) := by
  simpa only [neg_neg] using (reflection_angular parameters (-mode) field).symm

theorem firstMode_apply (parameters : PhaseParameters) (field : SmoothQuotient parameters) :
    firstMode parameters field = (1 / 2 : ℂ) •
      (angularCore parameters 1 (field 0) +
        reflection parameters (angularCore parameters (-1) (field 1))) := rfl

theorem modeProjection_apply (parameters : PhaseParameters) (field : SmoothQuotient parameters) :
    modeProjection parameters field =
      ![firstMode parameters field, reflection parameters (firstMode parameters field), 0, 0] := by
  funext coordinate
  fin_cases coordinate <;> rfl

theorem firstMode_positive (parameters : PhaseParameters) (field : SmoothQuotient parameters) :
    angularCore parameters 1 (firstMode parameters field) = firstMode parameters field := by
  rw [firstMode_apply, map_smul, map_add, angular_reflection, angularCore_projection,
    angularCore_projection]
  norm_num

theorem firstMode_modeProjection (parameters : PhaseParameters) (field : SmoothQuotient parameters) :
    firstMode parameters (modeProjection parameters field) = firstMode parameters field := by
  rw [firstMode_apply, modeProjection_apply]
  change (1 / 2 : ℂ) • (angularCore parameters 1 (firstMode parameters field) +
    reflection parameters (angularCore parameters (-1)
      (reflection parameters (firstMode parameters field)))) = _
  rw [firstMode_positive, angular_reflection]
  norm_num only [neg_neg, firstMode_positive, reflection_involutive]
  module

theorem modeProjection_idempotent (parameters : PhaseParameters)
    (field : SmoothQuotient parameters) :
    modeProjection parameters (modeProjection parameters field) = modeProjection parameters field := by
  rw [modeProjection_apply, firstMode_modeProjection, modeProjection_apply]

theorem reflection_originPartial {dimension : ℕ} (field : ClosedJet dimension)
    (direction : Fin 2) :
    originPartial direction (orthogonalJet cartesianReflectionEquiv field) =
      (if direction = 0 then (1 : ℝ) else -1) • originPartial direction field := by
  rw [originPartial_eq_closedDerivative, orthogonalJet_derivative]
  change (∑ target : CartesianWord 1,
    chainFactor 1 cartesianReflectionEquiv (fun _ => direction) target •
      closedDerivative field 1 target
        (orthogonalClosedPoint cartesianReflectionEquiv originPoint)) = _
  have atOrigin : orthogonalClosedPoint cartesianReflectionEquiv originPoint = originPoint := by
    apply Subtype.ext
    exact cartesianReflectionEquiv.map_zero
  rw [atOrigin]
  have factor (target : CartesianWord 1) :
      chainFactor 1 cartesianReflectionEquiv (fun _ => direction) target =
        if target = (fun _ => direction) then (if direction = 0 then (1 : ℝ) else -1) else 0 := by
    unfold chainFactor Grad.TensorCoefficients.tensorCoefficient
    rw [Fin.prod_univ_one]
    unfold Grad.OrthogonalCoefficients.coefficient
    by_cases equal : target = fun _ => direction
    · subst target
      fin_cases direction <;>
        simp [cartesianReflectionEquiv, cartesianReflection, spatialDirection_component]
    · have unequal : target 0 ≠ direction := by
        intro same
        apply equal
        funext index
        fin_cases index
        exact same
      generalize entry : target 0 = value at *
      fin_cases direction <;> fin_cases value <;>
        simp_all [cartesianReflectionEquiv, cartesianReflection, spatialDirection_component]
  simp_rw [factor, ite_smul, zero_smul]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_univ, ite_true]
  rfl

theorem traceFirst_reflection (parameters : PhaseParameters) (direction : Fin 2)
    (field : ACore parameters 1) :
    traceFirst direction (reflection parameters field) =
      (if direction = 0 then (1 : ℂ) else -1) • traceFirst direction field := by
  apply Subtype.ext
  funext cell
  change originPartial direction (orthogonalJet cartesianReflectionEquiv (field.val cell)) = _
  rw [reflection_originPartial]
  fin_cases direction <;> simp [traceFirst_val]

theorem affineTrace_modeProjection (parameters : PhaseParameters)
    (field : SmoothQuotient parameters) :
    affineTrace parameters (modeProjection parameters field) = 0 := by
  change (4 * Complex.I)⁻¹ •
    ((traceFirst 0 (firstMode parameters field) -
      Complex.I • traceFirst 1 (firstMode parameters field)) -
      (traceFirst 0 (reflection parameters (firstMode parameters field)) +
      Complex.I • traceFirst 1 (reflection parameters (firstMode parameters field)))) = 0
  rw [traceFirst_reflection, traceFirst_reflection]
  norm_num
  module

end Grad.QuotientProjection
