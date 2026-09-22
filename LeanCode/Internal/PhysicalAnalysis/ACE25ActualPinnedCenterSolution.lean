import ACE24PinnedCenterUniqueness

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.NonlinearDivision (closedOrigin IsRotationInvariant laplacianJet laplacianJet_value)

/-- The actual AN6a center solution: Θ = z_m Σ_j (-3k²)^j T^(j+1)(-Q_m F).
Every operation is the compact closed-disk construction proved above. -/
def pinnedCenterSolution {dimension : ℕ} (mode : ℤ) (frequency : ℝ) (source : ClosedJet dimension) :
    ClosedJet dimension :=
  coordinateMultiplyJet (mode : ℝ)
    (volterraResolventJet (-3 * frequency ^ 2) (-centerQuotientJet mode source))

theorem pinnedCenterSolution_series {dimension : ℕ} (mode : ℤ) (frequency : ℝ)
    (source : ClosedJet dimension) (point : ClosedDisk) :
    (pinnedCenterSolution mode frequency source).value point =
      signedComplexCoordinate (mode : ℝ) point.val •
        ∑' count : ℕ, (-3 * frequency ^ 2) ^ count •
          (volterraPower (count + 1) (-centerQuotientJet mode source)).value point := by
  rw [pinnedCenterSolution, coordinateMultiplyJet_value, volterraResolventJet_value]

theorem pinnedCenterSolution_pure {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (frequency : ℝ) (source : ClosedJet dimension) (pure : angularClosedJet mode source = source) :
    angularClosedJet mode (pinnedCenterSolution mode frequency source) = pinnedCenterSolution mode frequency source := by
  unfold pinnedCenterSolution
  rw [centerCoordinate_shift mode center,
    radial_angularMean _ (volterraResolvent_radial _ _ (radial_neg _ (centerQuotient_radial mode center source pure)))]

theorem pinnedCenterSolution_pinned {dimension : ℕ} (mode : ℤ) (frequency : ℝ) (source : ClosedJet dimension) :
    CenterPinned (pinnedCenterSolution mode frequency source) :=
  centerResolvent_pinned (mode : ℝ) (-3 * frequency ^ 2) (-centerQuotientJet mode source)

theorem pinnedCenterSolution_equation {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (frequency : ℝ) (source : ClosedJet dimension) (pure : angularClosedJet mode source = source) :
    laplacianJet (pinnedCenterSolution mode frequency source) +
      ((3 * frequency ^ 2 : ℝ) : ℂ) • pinnedCenterSolution mode frequency source = -source := by
  have equation := volterraResolvent_equation mode center (-3 * frequency ^ 2) (-centerQuotientJet mode source)
    (radial_neg _ (centerQuotient_radial mode center source pure))
  rw [centerSigned_neg, centerQuotient_factor mode center source pure] at equation
  change laplacianJet (pinnedCenterSolution mode frequency source) =
    -source + ((-3 * frequency ^ 2 : ℝ) : ℂ) • pinnedCenterSolution mode frequency source at equation
  rw [equation]
  push_cast
  module

/-- Literal second Cartesian derivatives, at every closed-disk point. -/
theorem pinnedCenterSolution_literal {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (frequency : ℝ) (source : ClosedJet dimension) (pure : angularClosedJet mode source = source)
    (point : ClosedDisk) :
    closedDerivative (pinnedCenterSolution mode frequency source) 2 (fun _ => 0) point +
      closedDerivative (pinnedCenterSolution mode frequency source) 2 (fun _ => 1) point +
        ((3 * frequency ^ 2 : ℝ) : ℂ) • (pinnedCenterSolution mode frequency source).value point = -source.value point := by
  have equality := congrArg (fun field : ClosedJet dimension => field.value point)
    (pinnedCenterSolution_equation mode center frequency source pure)
  simpa only [closedJet_value_add, closedJet_value_smul, closedJet_value_neg, ContinuousMap.add_apply,
    ContinuousMap.smul_apply, ContinuousMap.neg_apply, laplacianJet_value, laplacianCoefficient] using equality

theorem pinnedCenterSolution_unique {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (frequency : ℝ) (source : ClosedJet dimension) (pure : angularClosedJet mode source = source)
    (candidate : ClosedJet dimension) (candidatePure : angularClosedJet mode candidate = candidate)
    (candidatePinned : CenterPinned candidate)
    (candidateEquation : laplacianJet candidate + ((3 * frequency ^ 2 : ℝ) : ℂ) • candidate = -source) :
    candidate = pinnedCenterSolution mode frequency source :=
  pinnedCenter_unique mode center frequency source candidate (pinnedCenterSolution mode frequency source)
    candidatePure (pinnedCenterSolution_pure mode center frequency source pure)
    candidatePinned (pinnedCenterSolution_pinned mode frequency source)
    candidateEquation (pinnedCenterSolution_equation mode center frequency source pure)

theorem volterraResolvent_zero {dimension : ℕ} (source : ClosedJet dimension) :
    volterraResolventJet 0 source = volterraJet source := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [volterraResolventJet_value, tsum_eq_single 0]
  · simp only [pow_zero, one_smul, volterraPower_succ, volterraPower_zero]
  · intro count nonzero
    simp only [zero_pow nonzero, zero_smul]

theorem pinnedCenterSolution_zero_frequency {dimension : ℕ} (mode : ℤ) (source : ClosedJet dimension) :
    pinnedCenterSolution mode 0 source = coordinateMultiplyJet (mode : ℝ) (volterraJet (-centerQuotientJet mode source)) := by
  simp only [pinnedCenterSolution, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, volterraResolvent_zero]

/-- AN6a on the original scalar closed-jet carrier, including k = 0. -/
theorem actual_pinned_center_solution (mode : ℤ) (center : mode = 1 ∨ mode = -1) (frequency : ℝ)
    (source : ClosedJet 1) (pure : angularClosedJet mode source = source) :
    ∃! solution : ClosedJet 1, angularClosedJet mode solution = solution ∧ CenterPinned solution ∧
      laplacianJet solution + ((3 * frequency ^ 2 : ℝ) : ℂ) • solution = -source := by
  refine ⟨pinnedCenterSolution mode frequency source,
    ⟨pinnedCenterSolution_pure mode center frequency source pure,
      pinnedCenterSolution_pinned mode frequency source, pinnedCenterSolution_equation mode center frequency source pure⟩, ?_⟩
  intro candidate properties
  exact pinnedCenterSolution_unique mode center frequency source pure candidate properties.1 properties.2.1 properties.2.2

end Grad.ActualCenterVolterra
