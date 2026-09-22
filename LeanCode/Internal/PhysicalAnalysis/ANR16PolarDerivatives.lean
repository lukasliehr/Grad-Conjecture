import ANR14RadialTestLift
import RadialDivision

noncomputable section
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.NonlinearQuotient Grad.PhysicalFamily

private theorem radialDirection_coordinates (angle : ℝ) :
    radialDirection angle = Real.cos angle • diskBasis 0 + Real.sin angle • diskBasis 1 := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [radialDirection, collarPlane, diskBasis]

private theorem radialDirection_quarter (angle : ℝ) :
    planeQuarterTurn (radialDirection angle) = -Real.sin angle • diskBasis 0 + Real.cos angle • diskBasis 1 := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [radialDirection, collarPlane, diskBasis, planeQuarterTurn]

theorem radialDirection_hasDerivAt (angle : ℝ) :
    HasDerivAt radialDirection (planeQuarterTurn (radialDirection angle)) angle := by
  have derivative := ((Real.hasDerivAt_cos angle).smul_const (diskBasis 0)).add
    ((Real.hasDerivAt_sin angle).smul_const (diskBasis 1))
  change HasDerivAt (fun current => Real.cos current • diskBasis 0 + Real.sin current • diskBasis 1)
    (-Real.sin angle • diskBasis 0 + Real.cos angle • diskBasis 1) angle at derivative
  simpa only [← radialDirection_coordinates, ← radialDirection_quarter] using derivative

theorem polarPlane_radial_derivative (radius angle : ℝ) :
    HasDerivAt (fun current => polarPlane (current, angle)) (radialDirection angle) radius := by
  have derivative := (hasDerivAt_id radius).smul_const (radialDirection angle)
  simpa only [one_smul, id_eq, ← polarPlane_eq] using derivative

theorem polarPlane_angular_derivative (radius angle : ℝ) :
    HasDerivAt (fun current => polarPlane (radius, current))
      (radius • planeQuarterTurn (radialDirection angle)) angle := by
  have derivative := (radialDirection_hasDerivAt angle).const_smul radius
  change HasDerivAt (fun current => radius • radialDirection current)
    (radius • planeQuarterTurn (radialDirection angle)) angle at derivative
  simpa only [← polarPlane_eq] using derivative

theorem polar_radial_first {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field) (radius angle : ℝ) :
    radialField (field ∘ polarPlane) (radius, angle) =
      fderiv ℝ field (polarPlane (radius, angle)) (radialDirection angle) := by
  have first := radialField_hasDerivAt (field ∘ polarPlane) (smooth.comp polarPlane_smooth) radius angle
  have second := ((smooth.differentiable (by simp)) (polarPlane (radius, angle))).hasFDerivAt.comp_hasDerivAt radius
    (polarPlane_radial_derivative radius angle)
  exact first.unique second

theorem polar_radial_second {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field) (radius angle : ℝ) :
    radialIter 2 (field ∘ polarPlane) (radius, angle) =
      fderiv ℝ (fderiv ℝ field) (polarPlane (radius, angle)) (radialDirection angle) (radialDirection angle) := by
  have first := radialField_hasDerivAt (radialField (field ∘ polarPlane))
    (radialField_smooth _ (smooth.comp polarPlane_smooth)) radius angle
  have derivative := (((contDiff_infty_iff_fderiv.mp smooth).2.differentiable (by simp))
    (polarPlane (radius, angle))).hasFDerivAt.comp_hasDerivAt radius (polarPlane_radial_derivative radius angle)
  have second := derivative.clm_apply (hasDerivAt_const radius (radialDirection angle))
  have expression : (fun current => radialField (field ∘ polarPlane) (current, angle)) =
      (fun current => fderiv ℝ field (polarPlane (current, angle)) (radialDirection angle)) :=
    funext (fun current => polar_radial_first field smooth current angle)
  rw [expression] at first
  have equality := first.unique second
  have radialTwo : radialIter 2 (field ∘ polarPlane) = radialField (radialField (field ∘ polarPlane)) := rfl
  have result : radialField (radialField (field ∘ polarPlane)) (radius, angle) =
      fderiv ℝ (fderiv ℝ field) (polarPlane (radius, angle)) (radialDirection angle) (radialDirection angle) := by
    simpa only [Function.comp_apply, map_zero, add_zero] using equality
  exact (congrArg (fun function : ℝ × ℝ → Value => function (radius, angle)) radialTwo).trans result

theorem polar_angular_first {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field) (radius angle : ℝ) :
    angularJet 1 (field ∘ polarPlane) (radius, angle) =
      fderiv ℝ field (polarPlane (radius, angle)) (radius • planeQuarterTurn (radialDirection angle)) := by
  have first := angularJet_hasDerivAt 0 (field ∘ polarPlane) (smooth.comp polarPlane_smooth) radius angle
  have second := ((smooth.differentiable (by simp)) (polarPlane (radius, angle))).hasFDerivAt.comp_hasDerivAt angle
    (polarPlane_angular_derivative radius angle)
  simp only [angularJet_zero] at first
  exact first.unique second

theorem polar_angular_second {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field) (radius angle : ℝ) :
    angularJet 2 (field ∘ polarPlane) (radius, angle) =
      radius ^ 2 • fderiv ℝ (fderiv ℝ field) (polarPlane (radius, angle))
        (planeQuarterTurn (radialDirection angle)) (planeQuarterTurn (radialDirection angle)) -
      radius • fderiv ℝ field (polarPlane (radius, angle)) (radialDirection angle) := by
  have first := angularJet_hasDerivAt 1 (field ∘ polarPlane) (smooth.comp polarPlane_smooth) radius angle
  have derivative := (((contDiff_infty_iff_fderiv.mp smooth).2.differentiable (by simp))
    (polarPlane (radius, angle))).hasFDerivAt.comp_hasDerivAt angle (polarPlane_angular_derivative radius angle)
  have turnDerivative := (quarterTurnCLM.hasFDerivAt.comp_hasDerivAt angle (radialDirection_hasDerivAt angle)).const_smul radius
  have second := derivative.clm_apply turnDerivative
  have expression : (fun current => angularJet 1 (field ∘ polarPlane) (radius, current)) =
      (fun current => fderiv ℝ field (polarPlane (radius, current)) (radius • planeQuarterTurn (radialDirection current))) :=
    funext (fun current => polar_angular_first field smooth radius current)
  rw [expression] at first
  have equality := first.unique second
  simpa only [Function.comp_apply, Pi.smul_apply, quarterTurnCLM_apply, quarterTurn_twice, map_smul, smul_apply, map_neg,
    smul_neg, smul_smul, ← pow_two, sub_eq_add_neg] using equality

end Grad.CircularHighRegularity
