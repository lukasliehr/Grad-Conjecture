import ACB7ActualPureProfile

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterBounds
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotient Grad.NonlinearQuotientBounds Grad.ActualCenterVolterra Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.BoundaryTrace Grad.PhysicalFamily Grad.CollarCartesian Grad.SourceBoundaryTrace

private theorem centerCharacter_hasDerivAt (mode : ℤ) (angle : ℝ) :
    HasDerivAt (cellExponential mode) ((Complex.I * (mode : ℂ)) * cellExponential mode angle) angle := by
  have derivative := (cellExponential_hasFDerivAt mode angle).hasDerivAt
  simpa [cellExponentialDerivative, mul_comm] using derivative

theorem profileMode_radial (mode : ℤ) (profile : ℝ → ComplexEuclidean 1) (smooth : ContDiff ℝ ∞ profile) :
    radialField (profileMode mode profile) = profileMode mode (deriv profile) := by
  funext point
  exact (radialField_hasDerivAt _ (profileMode_smooth mode profile smooth) point.1 point.2).unique
    (((smooth.differentiable (by simp)) point.1).hasDerivAt.const_smul (cellExponential mode point.2))

theorem profileMode_radial_two (mode : ℤ) (profile : ℝ → ComplexEuclidean 1) (smooth : ContDiff ℝ ∞ profile) :
    radialIter 2 (profileMode mode profile) = profileMode mode (deriv (deriv profile)) := by
  change radialField (radialField (profileMode mode profile)) = _
  rw [profileMode_radial mode profile smooth,
    profileMode_radial mode (deriv profile) (contDiff_infty_iff_deriv.mp smooth).2]

theorem profileMode_angular_one (mode : ℤ) (profile : ℝ → ComplexEuclidean 1) (smooth : ContDiff ℝ ∞ profile)
    (radius angle : ℝ) :
    angularJet 1 (profileMode mode profile) (radius, angle) =
      (Complex.I * (mode : ℂ)) • profileMode mode profile (radius, angle) := by
  have first := angularJet_hasDerivAt 0 _ (profileMode_smooth mode profile smooth) radius angle
  rw [angularJet_zero] at first
  have second := (centerCharacter_hasDerivAt mode angle).smul_const (profile radius)
  exact (first.unique second).trans (mul_smul _ _ _)

theorem profileMode_angular_two (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (profile : ℝ → ComplexEuclidean 1) (smooth : ContDiff ℝ ∞ profile) (radius angle : ℝ) :
    angularJet 2 (profileMode mode profile) (radius, angle) = -profileMode mode profile (radius, angle) := by
  have first := angularJet_hasDerivAt 1 _ (profileMode_smooth mode profile smooth) radius angle
  simp_rw [profileMode_angular_one mode profile smooth] at first
  have second := ((centerCharacter_hasDerivAt mode angle).smul_const (profile radius)).const_smul (Complex.I * (mode : ℂ))
  have result := first.unique second
  change angularJet 2 (profileMode mode profile) (radius, angle) =
    (Complex.I * (mode : ℂ)) • (((Complex.I * (mode : ℂ)) * cellExponential mode angle) • profile radius) at result
  rw [result, smul_smul, ← mul_assoc]
  have square : (Complex.I * (mode : ℂ)) * (Complex.I * (mode : ℂ)) = -1 := by
    rcases center with rfl | rfl <;> norm_num
  rw [square, neg_one_mul, neg_smul]
  rfl

/-- The actual global pure representative yields the multiplied collar
ODE through the Cartesian Laplacian formula, without a singular definition. -/
theorem pureProfile_laplacian (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (field : ClosedJet 1) (radius : ℝ) :
    radius ^ 2 • diskLaplacian (pureExtension mode field) (polarPlane (radius, 0)) =
      radius ^ 2 • deriv (deriv (pureProfile mode field)) radius +
        radius • deriv (pureProfile mode field) radius - pureProfile mode field radius := by
  have representation : pureExtension mode field ∘ polarPlane = profileMode mode (pureProfile mode field) := by
    funext point
    exact pureExtension_polar mode field point.1 point.2
  have formula := polar_laplacian_multiplied (pureExtension mode field) (pureExtension_smooth mode field) radius 0
  rw [representation, profileMode_radial_two mode _ (pureProfile_smooth mode field),
    profileMode_radial mode _ (pureProfile_smooth mode field),
    profileMode_angular_two mode center _ (pureProfile_smooth mode field)] at formula
  simpa only [profileMode, cellExponential, Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_smul, sub_eq_add_neg] using formula

theorem pureProfile_value (mode : ℤ) (field : ClosedJet 1) (pure : angularClosedJet mode field = field)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    pureProfile mode field radius = field.value (Grad.SourceCollarDivision.polarClosedPoint radius 0 nonnegative bounded) :=
  congrArg (fun jet : ClosedJet 1 => jet.value (Grad.SourceCollarDivision.polarClosedPoint radius 0 nonnegative bounded))
    (pureExtension_jet mode field pure)

end Grad.ActualCenterBounds
