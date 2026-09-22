import ACE20ActualVolterraEquation
import ACE23VolterraUniqueness

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.NonlinearDivision (closedOrigin IsRotationInvariant laplacianJet)

theorem centerSigned_zero (dimension : ℕ) (sign : ℝ) :
    coordinateMultiplyJet sign (0 : ClosedJet dimension) = 0 := by
  rw [centerCoordinate_decomposition, centerCoordinate_zero, centerCoordinate_zero, smul_zero, add_zero]

theorem centerSigned_neg {dimension : ℕ} (sign : ℝ) (field : ClosedJet dimension) :
    coordinateMultiplyJet sign (-field) = -coordinateMultiplyJet sign field := by
  have equality := centerSigned_smul sign (-1 : ℂ) field
  simpa only [neg_one_smul] using equality

theorem centerPinned_sub {dimension : ℕ} (first second : ClosedJet dimension)
    (firstPinned : CenterPinned first) (secondPinned : CenterPinned second) : CenterPinned (first - second) := by
  constructor
  · simp only [sub_eq_add_neg, closedJet_value_add, closedJet_value_neg, ContinuousMap.add_apply,
      ContinuousMap.neg_apply, firstPinned.1, secondPinned.1, neg_zero, add_zero]
  · intro direction
    simp only [sub_eq_add_neg, centerPartial_add, centerPartial_neg, closedJet_value_add, closedJet_value_neg,
      ContinuousMap.add_apply, ContinuousMap.neg_apply, firstPinned.2 direction, secondPinned.2 direction,
      neg_zero, add_zero]

theorem centerLaplacian_sub {dimension : ℕ} (first second : ClosedJet dimension) :
    laplacianJet (first - second) = laplacianJet first - laplacianJet second := by
  simp only [laplacianJet, sub_eq_add_neg, centerPartial_add, centerPartial_neg]
  abel

/-- Uniqueness of a pinned homogeneous solution in the actual signed first
mode, proved through the explicit Volterra kernel. -/
theorem centerHomogeneous_zero {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (parameter : ℝ) (field : ClosedJet dimension) (pure : angularClosedJet mode field = field)
    (pinned : CenterPinned field) (equation : laplacianJet field = (parameter : ℂ) • field) : field = 0 := by
  have factor := centerQuotient_factor mode center field pure
  have radial := centerQuotient_radial mode center field pure
  have quotientPinned : CenterPinned (coordinateMultiplyJet (mode : ℝ) (centerQuotientJet mode field)) := by
    rwa [factor]
  have origin := centerSigned_pinned_origin (mode : ℝ) (centerQuotientJet mode field) quotientPinned
  have quotientEquation : laplacianJet (coordinateMultiplyJet (mode : ℝ) (centerQuotientJet mode field)) =
      coordinateMultiplyJet (mode : ℝ) ((parameter : ℂ) • centerQuotientJet mode field) := by
    rw [centerSigned_smul, factor]
    exact equation
  have integral := pinnedRadial_volterra_inverse mode center (centerQuotientJet mode field)
    ((parameter : ℂ) • centerQuotientJet mode field) radial origin quotientEquation
  rw [volterraJet_smul] at integral
  have zero := volterra_homogeneous_zero parameter (centerQuotientJet mode field) integral
  rw [zero, centerSigned_zero] at factor
  exact factor.symm

/-- The source is the same literal closed jet in both equations. -/
theorem pinnedCenter_unique {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1) (frequency : ℝ)
    (source first second : ClosedJet dimension)
    (firstPure : angularClosedJet mode first = first) (secondPure : angularClosedJet mode second = second)
    (firstPinned : CenterPinned first) (secondPinned : CenterPinned second)
    (firstEquation : laplacianJet first + ((3 * frequency ^ 2 : ℝ) : ℂ) • first = -source)
    (secondEquation : laplacianJet second + ((3 * frequency ^ 2 : ℝ) : ℂ) • second = -source) :
    first = second := by
  have pure : angularClosedJet mode (first - second) = first - second := by
    have equality := (angularClosedJetLinear dimension mode).map_sub first second
    change angularClosedJet mode (first - second) = angularClosedJet mode first - angularClosedJet mode second at equality
    rwa [firstPure, secondPure] at equality
  have firstLaplacian := eq_sub_iff_add_eq.mpr firstEquation
  have secondLaplacian := eq_sub_iff_add_eq.mpr secondEquation
  have homogeneous : laplacianJet (first - second) = ((-3 * frequency ^ 2 : ℝ) : ℂ) • (first - second) := by
    rw [centerLaplacian_sub, firstLaplacian, secondLaplacian]
    push_cast
    module
  exact sub_eq_zero.mp (centerHomogeneous_zero mode center (-3 * frequency ^ 2) (first - second)
    pure (centerPinned_sub first second firstPinned secondPinned) homogeneous)

end Grad.ActualCenterVolterra
