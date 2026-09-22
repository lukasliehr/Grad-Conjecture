import AEN3FirstOrderRadialRecurrence

noncomputable section
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ExceptionalNative
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange
open Grad.NonlinearQuotientBounds Grad.ActualCenterVolterra Grad.ActualExceptionalInverse
open Grad.ActualCenterBounds Grad.CircularHighRegularity Grad.SourceCollarDivision Grad.BoundaryTrace

theorem pureProfile_euler (mode : ℤ) (field : ClosedJet 1) (pure : angularClosedJet mode field = field)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    (eulerJet field).value (polarClosedPoint radius 0 nonnegative bounded) =
      radius • deriv (pureProfile mode field) radius := by
  have derivative := (((pureExtension_smooth mode field).differentiable (by simp))
    (polarPlane (radius, 0))).hasFDerivAt.comp_hasDerivAt radius (polarPlane_radial_derivative radius 0)
  change HasDerivAt (pureProfile mode field)
    (fderiv ℝ (pureExtension mode field) (polarPlane (radius, 0)) (radialDirection 0)) radius at derivative
  have euler := eulerJet_global_value (pureExtension mode field) (pureExtension_smooth mode field)
    (polarClosedPoint radius 0 nonnegative bounded)
  rw [pureExtension_jet mode field pure] at euler
  rw [euler, derivative.deriv]
  change fderiv ℝ (pureExtension mode field) (polarPlane (radius, 0)) (polarPlane (radius, 0)) = _
  conv_lhs => arg 2; rw [polarPlane_eq]
  exact map_smul _ _ _

/-- The literal signed Cartesian equation gives an actual first-order
radial equation on every closed positive collar. -/
theorem pureProfile_signed_equation (sign mode : ℤ) (signed : sign = 1 ∨ sign = -1)
    (field forcing : ClosedJet 1) (pure : angularClosedJet mode field = field)
    (forcingPure : angularClosedJet (mode - sign) forcing = forcing)
    (equation : signedLowering sign field = forcing) (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1) :
    deriv (pureProfile mode field) radius = pureProfile (mode - sign) forcing radius +
      (-((sign * mode : ℤ) : ℝ)) • (radius⁻¹ • pureProfile mode field radius) := by
  change centerDifferential sign field = forcing at equation
  have euler := centerDifferential_euler sign signed field
  rw [equation, pureMode_rotation mode field pure, smul_smul] at euler
  have coefficient : (Complex.I * (sign : ℂ)) * (Complex.I * (mode : ℂ)) = -(((sign * mode : ℤ) : ℝ) : ℂ) := by
    push_cast
    calc (Complex.I * (sign : ℂ)) * (Complex.I * (mode : ℂ)) = Complex.I ^ 2 * ((sign : ℂ) * (mode : ℂ)) := by ring
         _ = _ := by rw [Complex.I_sq]; ring
  rw [coefficient, neg_smul, sub_neg_eq_add] at euler
  let point := polarClosedPoint radius 0 positive.le bounded
  have evaluated := congrArg (fun jet : ClosedJet 1 => jet.value point) euler
  rw [coordinateMultiplyJet_value, closedJet_value_add, closedJet_value_smul,
    ContinuousMap.add_apply, ContinuousMap.smul_apply, Complex.coe_smul] at evaluated
  have coordinate : signedComplexCoordinate (sign : ℝ) point.val = (radius : ℂ) := by
    simp [point, Grad.SourceCollarDivision.polarClosedPoint, signedComplexCoordinate, polarPlane, Grad.BoundaryTrace.collarPlane]
  rw [coordinate, Complex.coe_smul] at evaluated
  dsimp only [point] at evaluated
  rw [pureProfile_euler mode field pure radius positive.le bounded,
    ← pureProfile_value mode field pure radius positive.le bounded,
    ← pureProfile_value (mode - sign) forcing forcingPure radius positive.le bounded] at evaluated
  apply smul_right_injective (ComplexEuclidean 1) positive.ne'
  calc
    radius • deriv (pureProfile mode field) radius =
      radius • pureProfile (mode - sign) forcing radius - ((sign * mode : ℤ) : ℝ) • pureProfile mode field radius := by
        rw [evaluated]
        module
    _ = _ := by
      simp only [smul_add, smul_smul]
      have scalar : radius * (-((sign * mode : ℤ) : ℝ) * radius⁻¹) = -((sign * mode : ℤ) : ℝ) := by field_simp
      rw [scalar, neg_smul, sub_eq_add_neg]

theorem pureProfile_signed_within_equation (sign mode : ℤ) (signed : sign = 1 ∨ sign = -1)
    (field forcing : ClosedJet 1) (pure : angularClosedJet mode field = field)
    (forcingPure : angularClosedJet (mode - sign) forcing = forcing)
    (equation : signedLowering sign field = forcing)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    EqOn (derivWithin (pureProfile mode field) (Icc lower 1))
      (fun radius => pureProfile (mode - sign) forcing radius +
        (-((sign * mode : ℤ) : ℝ)) • (radius⁻¹ • pureProfile mode field radius)) (Icc lower 1) := by
  intro radius inside
  rw [((pureProfile_smooth mode field).differentiable (by simp) radius).derivWithin
    ((uniqueDiffOn_Icc bounded) radius inside)]
  exact pureProfile_signed_equation sign mode signed field forcing pure forcingPure equation radius
    (positive.trans_le inside.1) inside.2

theorem pureProfile_signed_energy_recurrence (sign mode : ℤ) (signed : sign = 1 ∨ sign = -1)
    (small : |(mode : ℝ)| ≤ 2) (field forcing : ClosedJet 1) (pure : angularClosedJet mode field = field)
    (forcingPure : angularClosedJet (mode - sign) forcing = forcing)
    (equation : signedLowering sign field = forcing) (order : ℕ) :
    radialWithinEnergy (1 / 2) (order + 1) (pureProfile mode field) ≤
      4 * (radialWithinEnergy (1 / 2) order (pureProfile (mode - sign) forcing) +
        4 * radialProductConstant (1 / 2) (by norm_num) (by norm_num) order *
          ∑ index ∈ Finset.range (order + 1), radialWithinEnergy (1 / 2) (order - index) (pureProfile mode field)) := by
  have scalar : |-((sign * mode : ℤ) : ℝ)| ≤ 2 := by
    rcases signed with rfl | rfl <;> simpa using small
  exact firstOrder_energy_recurrence (1 / 2) (by norm_num) (by norm_num) _ _
    (pureProfile_smooth mode field).contDiffOn (pureProfile_smooth (mode - sign) forcing).contDiffOn _ scalar
    (pureProfile_signed_within_equation sign mode signed field forcing pure forcingPure equation
      (1 / 2) (by norm_num) (by norm_num)) order

end Grad.ExceptionalNative
