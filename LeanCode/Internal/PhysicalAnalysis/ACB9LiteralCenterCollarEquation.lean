import ACB8PureProfileLaplacian

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterBounds
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotient Grad.NonlinearQuotientBounds Grad.ActualCenterVolterra Grad.CircularHighWeak
open Grad.CircularHighRegularity Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.BoundaryTrace Grad.PhysicalFamily Grad.CollarCartesian Grad.SourceBoundaryTrace
open Grad.NonlinearDivision (laplacianJet)

/-- The genuine first-mode collar ODE, derived from the literal closed
Cartesian PDE on the same source and solution. -/
theorem pureProfile_center_equation (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (frequency : ℝ) (field source : ClosedJet 1)
    (fieldPure : angularClosedJet mode field = field) (sourcePure : angularClosedJet mode source = source)
    (equation : laplacianJet field + ((3 * frequency ^ 2 : ℝ) : ℂ) • field = -source)
    (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1) :
    deriv (deriv (pureProfile mode field)) radius =
      -(radius⁻¹ • deriv (pureProfile mode field) radius) +
        radius⁻¹ ^ 2 • pureProfile mode field radius +
        (-3 * frequency ^ 2) • pureProfile mode field radius - pureProfile mode source radius := by
  let point := Grad.SourceCollarDivision.polarClosedPoint radius 0 positive.le bounded
  have laplace := laplacianJet_global_literal (pureExtension mode field) (pureExtension_smooth mode field) point
  rw [pureExtension_jet mode field fieldPure] at laplace
  have evaluated := congrArg (fun jet : ClosedJet 1 => jet.value point) equation
  simp only [closedJet_value_add, closedJet_value_smul, closedJet_value_neg,
    ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.neg_apply] at evaluated
  rw [Complex.coe_smul] at evaluated
  dsimp only [point] at evaluated laplace
  rw [laplace, ← pureProfile_value mode field fieldPure radius positive.le bounded,
    ← pureProfile_value mode source sourcePure radius positive.le bounded] at evaluated
  have solved : diskLaplacian (pureExtension mode field) (polarPlane (radius, 0)) =
      -pureProfile mode source radius - (3 * frequency ^ 2) • pureProfile mode field radius :=
    (eq_sub_iff_add_eq).mpr evaluated
  have formula := pureProfile_laplacian mode center field radius
  apply smul_right_injective (ComplexEuclidean 1) (pow_ne_zero 2 positive.ne')
  have first : radius ^ 2 * radius⁻¹ = radius := by field_simp
  have second : radius ^ 2 * (radius⁻¹ ^ 2) = 1 := by field_simp
  calc
    radius ^ 2 • deriv (deriv (pureProfile mode field)) radius =
        radius ^ 2 • diskLaplacian (pureExtension mode field) (polarPlane (radius, 0)) -
          radius • deriv (pureProfile mode field) radius + pureProfile mode field radius := by
      rw [formula]
      module
    _ = _ := by
      rw [solved]
      simp only [smul_add, smul_sub, smul_neg, smul_smul, first, second, one_smul]
      module

theorem pureProfile_center_within_equation (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (frequency : ℝ) (field source : ClosedJet 1)
    (fieldPure : angularClosedJet mode field = field) (sourcePure : angularClosedJet mode source = source)
    (equation : laplacianJet field + ((3 * frequency ^ 2 : ℝ) : ℂ) • field = -source)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    EqOn (derivWithin (derivWithin (pureProfile mode field) (Icc lower 1)) (Icc lower 1))
      (fun radius => -(radius⁻¹ • derivWithin (pureProfile mode field) (Icc lower 1) radius) +
        radius⁻¹ ^ 2 • pureProfile mode field radius +
        (-3 * frequency ^ 2) • pureProfile mode field radius - pureProfile mode source radius) (Icc lower 1) := by
  intro radius inside
  have within (order : ℕ) := iteratedDerivWithin_eq_iteratedDeriv (n := order) (uniqueDiffOn_Icc bounded)
    ((pureProfile_smooth mode field).contDiffAt.of_le (by exact_mod_cast le_top)) inside
  have first : derivWithin (pureProfile mode field) (Icc lower 1) radius = deriv (pureProfile mode field) radius := by
    simpa only [iteratedDerivWithin_succ', iteratedDerivWithin_zero, iteratedDeriv_succ', iteratedDeriv_zero] using within 1
  have second : derivWithin (derivWithin (pureProfile mode field) (Icc lower 1)) (Icc lower 1) radius =
      deriv (deriv (pureProfile mode field)) radius := by
    simpa only [iteratedDerivWithin_succ', iteratedDerivWithin_zero, iteratedDeriv_succ', iteratedDeriv_zero] using within 2
  dsimp only
  rw [first, second]
  exact pureProfile_center_equation mode center frequency field source fieldPure sourcePure equation radius
    (positive.trans_le inside.1) inside.2

end Grad.ActualCenterBounds
