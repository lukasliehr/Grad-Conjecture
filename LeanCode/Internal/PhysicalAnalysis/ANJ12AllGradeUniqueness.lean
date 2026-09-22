import ANJ11CompletedUniqueness
import GQE11LiteralEndpoint

noncomputable section
set_option maxHeartbeats 1200000
namespace Grad.InhomogeneousHighRobin
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.OrdinaryDiskCalculus Grad.OrdinaryDiskFaithfulness Grad.CircularNormalLift
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.GaugeCoefficients.Physical.Compensated (apBoundaryCoefficientCLM)
local instance (priority := 2000) allGradeUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade

theorem unitScalarOperator_lower (parameters : PhaseParameters) (grade : ℕ) (parameter : ℝ)
    (field : unitDiskSobolev (grade + 2)) :
    unitScalarOperator 0 parameter (unitLower (show 2 ≤ grade + 2 by omega) field) =
      unitLower (show 0 ≤ grade by omega) (unitScalarOperator grade parameter field) := by
  apply isClosed_property (unitDiskCoreInto_denseRange (grade + 2))
    (isClosed_eq ((unitScalarOperator 0 parameter).continuous.comp (unitLower (show 2 ≤ grade + 2 by omega)).continuous)
      ((unitLower (show 0 ≤ grade by omega)).continuous.comp (unitScalarOperator grade parameter).continuous)) _ field
  intro core
  have first := (congrArg (unitScalarOperator 0 parameter) (unitLower_core (show 2 ≤ grade + 2 by omega) core)).trans
    (unitScalarOperator_core parameters 0 parameter core)
  have second := (congrArg (unitLower (show 0 ≤ grade by omega)) (unitScalarOperator_core parameters grade parameter core)).trans
    (unitLower_core (show 0 ≤ grade by omega) (Grad.ActualSmoothPDE.scalarResidualJet parameter core))
  exact first.trans second.symm

theorem ordinaryRobinTrace_lower_coefficient (grade : ℕ) (field : unitDiskSobolev (grade + 2)) (output : ℤ × ℤ) :
    apBoundaryCoefficient 1 0 0 1 1
      (ordinaryRobinTrace 0 (unitLower (show 2 ≤ grade + 2 by omega) field)) output =
    apBoundaryCoefficient 1 0 0 1 (grade + 1) (ordinaryRobinTrace grade field) output := by
  let first := apBoundaryCoefficientCLM (dimension := 1) 1 0 0 1 1 output
  let second := apBoundaryCoefficientCLM (dimension := 1) 1 0 0 1 (grade + 1) output
  have identity : first (ordinaryRobinTrace 0 (unitLower (show 2 ≤ grade + 2 by omega) field)) =
      second (ordinaryRobinTrace grade field) := by
    apply isClosed_property (unitDiskCoreInto_denseRange (grade + 2))
      (isClosed_eq (first.continuous.comp ((ordinaryRobinTrace 0).continuous.comp
        (unitLower (show 2 ≤ grade + 2 by omega)).continuous))
        (second.continuous.comp (ordinaryRobinTrace grade).continuous)) _ field
    intro core
    have left := congrArg (fun value : unitDiskSobolev 2 => first (ordinaryRobinTrace 0 value))
      (unitLower_core (show 2 ≤ grade + 2 by omega) core)
    have leftTrace := (congrArg first (ordinaryRobinTrace_core 0 core)).trans
      (ordinaryBoundaryTrace_core_coefficient 1 (by omega) (Grad.ActualSmoothRobin.robinResidualJet core) output)
    have rightTrace := (congrArg second (ordinaryRobinTrace_core grade core)).trans
      (ordinaryBoundaryTrace_core_coefficient (grade + 1) (by omega) (Grad.ActualSmoothRobin.robinResidualJet core) output)
    exact left.trans (leftTrace.trans rightTrace.symm)
  exact identity

theorem ordinaryRobinTrace_lower_equal (grade : ℕ) (first second : unitDiskSobolev (grade + 2))
    (same : ordinaryRobinTrace grade first = ordinaryRobinTrace grade second) :
    ordinaryRobinTrace 0 (unitLower (show 2 ≤ grade + 2 by omega) first) =
      ordinaryRobinTrace 0 (unitLower (show 2 ≤ grade + 2 by omega) second) := by
  apply lp.ext
  funext output
  have equality := (ordinaryRobinTrace_lower_coefficient grade first output).trans
    ((congrArg (fun value => apBoundaryCoefficient 1 0 0 1 (grade + 1) value output) same).trans
      (ordinaryRobinTrace_lower_coefficient grade second output).symm)
  exact (apBoundary_weighted_coefficient 1 0 0 1 1 _ output).symm.trans
    ((congrArg (fun value : ComplexEuclidean 1 => (apBoundaryWeight 1 0 0 1 1 output : ℂ) • value) equality).trans
      (apBoundary_weighted_coefficient 1 0 0 1 1 _ output))

/-- The original completed scalar and Robin equations determine the high
solution uniquely at every grade, including the base H2 grade. -/
theorem completedGrade_unique (parameters : PhaseParameters) (grade : ℕ) (parameter : ℝ)
    (first second : unitDiskSobolev (grade + 2))
    (firstHigh : unitDiskBulk (grade + 2) first ∈ highDiskL2)
    (secondHigh : unitDiskBulk (grade + 2) second ∈ highDiskL2)
    (samePDE : unitScalarOperator grade parameter first = unitScalarOperator grade parameter second)
    (sameRobin : ordinaryRobinTrace grade first = ordinaryRobinTrace grade second) : first = second := by
  let lower := unitLower (show 2 ≤ grade + 2 by omega)
  have firstLow : unitDiskBulk 2 (lower first) ∈ highDiskL2 :=
    (congrArg (fun value : DiskL2 1 => value ∈ highDiskL2) (unitLower_bulk (show 2 ≤ grade + 2 by omega) first)).mpr firstHigh
  have secondLow : unitDiskBulk 2 (lower second) ∈ highDiskL2 :=
    (congrArg (fun value : DiskL2 1 => value ∈ highDiskL2) (unitLower_bulk (show 2 ≤ grade + 2 by omega) second)).mpr secondHigh
  have scalar := (unitScalarOperator_lower parameters grade parameter first).trans
    ((congrArg (unitLower (show 0 ≤ grade by omega)) samePDE).trans
      (unitScalarOperator_lower parameters grade parameter second).symm)
  have equal := completedH2_unique parameters parameter (lower first) (lower second) firstLow secondLow scalar
    (ordinaryRobinTrace_lower_equal grade first second sameRobin)
  apply ordinaryBulk_injective parameters (grade + 2)
  exact (unitLower_bulk (show 2 ≤ grade + 2 by omega) first).symm.trans
    ((congrArg (unitDiskBulk 2) equal).trans (unitLower_bulk (show 2 ≤ grade + 2 by omega) second))

end Grad.InhomogeneousHighRobin
