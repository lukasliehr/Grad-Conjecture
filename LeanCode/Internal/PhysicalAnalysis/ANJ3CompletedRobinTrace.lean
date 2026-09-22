import ANJ2CompletedHighScalar
import ANL14ExactNormalConsumer

noncomputable section
set_option maxHeartbeats 1200000
open Set
open scoped Topology
namespace Grad.InhomogeneousHighRobin
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.OrdinaryDiskCalculus Grad.ActualUniformGlobal Grad.ActualSmoothRobin Grad.CircularNormalLift
open Grad.GaugeCoefficients.Physical.WeightedTrace
local instance (priority := 2000) robinUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade
local instance (priority := 2000) robinBoundarySpace (grade : ℕ) : NormedSpace ℂ (normalBoundaryGrade grade) :=
  (normalBoundaryGrade grade).normedSpace

/-- Actual outward normal plus twice the value, in the original trace grade. -/
def ordinaryRobinTrace (order : ℕ) : unitDiskSobolev (order + 2) →L[ℂ] APBoundaryGrade 1 0 0 1 1 (order + 1) :=
  ordinaryNormalTrace order + (2 : ℂ) •
    ((ordinaryBoundaryTrace (order + 1) (by omega)).comp (unitLower (show order + 1 ≤ order + 2 by omega)))

theorem ordinaryRobinTrace_core (order : ℕ) (core : ClosedJet 1) :
    ordinaryRobinTrace order (unitDiskCoreInto (order + 2) core) =
      ordinaryBoundaryTrace (order + 1) (by omega)
        (unitDiskCoreInto (order + 1) (robinResidualJet core)) := by
  let trace := ordinaryBoundaryTrace (order + 1) (show 1 ≤ order + 1 by omega)
  let mapping : ClosedJet 1 →ₗ[ℂ] APBoundaryGrade 1 0 0 1 1 (order + 1) :=
    trace.toLinearMap.comp (unitDiskCoreInto (order + 1))
  have first := congrArg trace (ordinaryEuler_core (order + 1) core)
  have second := congrArg trace (unitLower_core (show order + 1 ≤ order + 2 by omega) core)
  have expanded := (mapping.map_add (Grad.NonlinearRange.eulerJet core) ((2 : ℂ) • core)).trans
    (congrArg (fun value => mapping (Grad.NonlinearRange.eulerJet core) + value) (mapping.map_smul (2 : ℂ) core))
  exact (congrArg₂ (fun first second : APBoundaryGrade 1 0 0 1 1 (order + 1) => first + (2 : ℂ) • second)
    first second).trans expanded.symm

theorem ordinaryBoundaryTrace_zero_of_boundary (grade : ℕ) (positive : 1 ≤ grade) (core : ClosedJet 1)
    (zeroBoundary : closedBoundaryValue core = 0) :
    ordinaryBoundaryTrace grade positive (unitDiskCoreInto grade core) = 0 := by
  have values : (fun angle : CellCircle => core.value (Grad.BoundaryTrace.boundaryDiskPoint angle)) = fun _ => 0 := by
    funext angle
    exact congrArg (fun field : C(CellCircle, ComplexEuclidean 1) => field angle) zeroBoundary
  apply lp.ext
  funext output
  rw [← apBoundary_weighted_coefficient 1 0 0 1 grade _ output,
    ordinaryBoundaryTrace_core_coefficient, values]
  simp [fourierCoeff]

theorem actualCompletedInverse_robin_zero (order : ℕ) (parameters : PhaseParameters)
    (parameter : ℝ) (source : unitDiskSobolev order) :
    ordinaryRobinTrace order (actualCompletedInverse order parameters parameter source) = 0 := by
  apply isClosed_property (unitDiskCoreInto_denseRange order)
    (isClosed_eq ((ordinaryRobinTrace order).continuous.comp (actualCompletedInverse order parameters parameter).continuous)
      continuous_const) _ source
  intro core
  exact (congrArg (ordinaryRobinTrace order) (actualSmoothInverse_grade parameters parameter core order).symm).trans
    ((ordinaryRobinTrace_core order (actualSmoothInverse parameters parameter core)).trans
      (ordinaryBoundaryTrace_zero_of_boundary (order + 1) (by omega) _
        (sameH1_robin_boundary_zero parameter (highL2Core core) _ (actualSmoothInverse_H1 parameters parameter core))))

theorem completedNormalLift_lower_value_zero (order : ℕ) (field : normalBoundaryGrade (order + 2)) :
    ordinaryBoundaryTrace (order + 1) (by omega)
      (unitLower (show order + 1 ≤ order + 2 by omega) (completedNormalLift (order + 2) field)) = 0 := by
  let trace := ordinaryBoundaryTrace (order + 1) (show 1 ≤ order + 1 by omega)
  let lower := unitLower (show order + 1 ≤ order + 2 by omega)
  apply isClosed_property (normalBoundaryInto_denseRange (order + 2))
    (isClosed_eq (trace.continuous.comp (lower.continuous.comp (completedNormalLift (order + 2)).continuous))
      continuous_const) _ field
  intro values
  have lift := congrArg (fun source : unitDiskSobolev (order + 2) => trace (lower source))
    (completedNormalLift_finite (order + 2) (by omega) values)
  have lowered := congrArg trace (unitLower_core (show order + 1 ≤ order + 2 by omega) (finiteNormalLinear values))
  have boundary : closedBoundaryValue (finiteNormalLinear values) = 0 := by
    rw [finiteNormalLinear_eq]
    apply ContinuousMap.ext
    exact finiteNormalJet_boundary values.support values
  exact lift.trans (lowered.trans (ordinaryBoundaryTrace_zero_of_boundary (order + 1) (by omega) _ boundary))

theorem completedNormalLift_robin_trace (order : ℕ) (field : normalBoundaryGrade (order + 2)) :
    ordinaryRobinTrace order (completedNormalLift (order + 2) field) = field.val := by
  have equality := congrArg₂ (fun first second : APBoundaryGrade 1 0 0 1 1 (order + 1) => first + (2 : ℂ) • second)
    (completedNormalLift_normal_trace order field) (completedNormalLift_lower_value_zero order field)
  exact equality.trans (by simp only [smul_zero, add_zero])

end Grad.InhomogeneousHighRobin
