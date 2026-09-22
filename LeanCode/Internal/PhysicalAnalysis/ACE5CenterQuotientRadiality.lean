import ACE4ActualCenterQuotient
import DivisionUniqueness

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial
open Grad.NonlinearProduct Grad.NonlinearRange Grad.NonlinearQuotientBounds

theorem centerCoordinate_nonzero (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (point : SpatialPlane) (offAxis : point ≠ 0) : signedComplexCoordinate (mode : ℝ) point ≠ 0 := by
  intro zero
  have real := congrArg Complex.re zero
  have imaginary := congrArg Complex.im zero
  rcases center with rfl | rfl <;> simp [signedComplexCoordinate] at real imaginary <;>
    apply offAxis <;> ext coordinate <;> fin_cases coordinate <;> simp_all

theorem centerCoordinate_injective {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1) :
    Function.Injective (coordinateMultiplyJet (dimension := dimension) (mode : ℝ)) := by
  intro first second equal
  have offAxis (point : ClosedDisk) (nonzero : point.val ≠ 0) : first.value point = second.value point := by
    apply smul_right_injective (ComplexEuclidean dimension) (centerCoordinate_nonzero mode center point.val nonzero)
    exact (coordinateMultiplyJet_value (mode : ℝ) first point).symm.trans
      ((congrArg (fun field : ClosedJet dimension => field.value point) equal).trans
        (coordinateMultiplyJet_value (mode : ℝ) second point))
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  by_cases axis : point.val = 0
  · have isOrigin : point = Grad.NonlinearDivision.closedOrigin := Subtype.ext axis
    rw [isOrigin]
    have firstLimit := (first.value.continuous.tendsto Grad.NonlinearDivision.closedOrigin).comp
      Grad.NonlinearDivision.axisSequence_tendsto
    have secondLimit := (second.value.continuous.tendsto Grad.NonlinearDivision.closedOrigin).comp
      Grad.NonlinearDivision.axisSequence_tendsto
    exact tendsto_nhds_unique (firstLimit.congr (fun index =>
      offAxis _ (Grad.NonlinearDivision.axisSequence_offAxis index))) secondLimit
  · exact offAxis point axis

theorem centerCoordinate_shift {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (field : ClosedJet dimension) :
    angularClosedJet mode (coordinateMultiplyJet (mode : ℝ) field) =
      coordinateMultiplyJet (mode : ℝ) (angularClosedJet 0 field) := by
  rcases center with rfl | rfl
  · simpa only [Int.cast_one, sub_self] using angularClosedJet_z 1 field
  · simpa only [Int.cast_neg, Int.cast_one, neg_add_cancel] using angularClosedJet_zbar (-1) field

/-- The actual quotient is a smooth Cartesian radial function. -/
theorem centerQuotient_mean {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (field : ClosedJet dimension) (pure : angularClosedJet mode field = field) :
    angularClosedJet 0 (centerQuotientJet mode field) = centerQuotientJet mode field := by
  apply centerCoordinate_injective mode center
  calc
    _ = angularClosedJet mode (coordinateMultiplyJet (mode : ℝ) (centerQuotientJet mode field)) :=
      (centerCoordinate_shift mode center _).symm
    _ = angularClosedJet mode field := congrArg (angularClosedJet mode) (centerQuotient_factor mode center field pure)
    _ = field := pure
    _ = _ := (centerQuotient_factor mode center field pure).symm

theorem centerQuotient_radial {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (field : ClosedJet dimension) (pure : angularClosedJet mode field = field) :
    Grad.NonlinearDivision.IsRotationInvariant (centerQuotientJet mode field) := by
  intro angle point
  have covariance := angularClosedJet_rotation_value 0 (centerQuotientJet mode field) angle point
  rw [centerQuotient_mean mode center field pure, angularCharacter_zero_mode, one_smul] at covariance
  convert covariance using 1
  congr 1
  apply Subtype.ext
  exact physicalRotation_eq_orthogonal angle point.val

end Grad.ActualCenterVolterra
