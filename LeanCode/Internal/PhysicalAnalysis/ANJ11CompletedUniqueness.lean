import ANJ10CompletedGreen

noncomputable section
set_option maxHeartbeats 1200000
namespace Grad.InhomogeneousHighRobin
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.OrdinaryDiskCalculus Grad.OrdinaryDiskFaithfulness Grad.CircularNormalLift
local instance (priority := 2000) uniqueUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade

private theorem coercive_separates {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (form : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive form)
    (first second : V) (equal : ∀ test, form first test = form second test) : first = second := by
  apply coercive.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro test
  rw [IsCoercive.continuousLinearEquivOfBilin_apply, IsCoercive.continuousLinearEquivOfBilin_apply]
  exact equal test

private theorem robinValue_separates (parameter : ℝ) (first second : highDiskGrade)
    (equal : ∀ test, robinValue parameter first test = robinValue parameter second test) : first = second := by
  apply coercive_separates (robinForm parameter) (robinForm_isCoercive parameter) first second
  intro test
  exact (robinForm_literal parameter first test).trans
    ((congrArg Complex.re (equal test)).trans (robinForm_literal parameter second test).symm)

/-- Uniqueness in the actual completed H2 space from the actual scalar
operator and ordinary outward Robin trace, without a smoothness assumption. -/
theorem completedH2_unique (parameters : PhaseParameters) (parameter : ℝ)
    (first second : unitDiskSobolev 2)
    (firstHigh : unitDiskBulk 2 first ∈ highDiskL2) (secondHigh : unitDiskBulk 2 second ∈ highDiskL2)
    (samePDE : unitScalarOperator 0 parameter first = unitScalarOperator 0 parameter second)
    (sameRobin : ordinaryRobinTrace 0 first = ordinaryRobinTrace 0 second) : first = second := by
  have highFirst : diskBulk (completedH1 0 first) ∈ highDiskL2 :=
    (congrArg (fun value : DiskL2 1 => value ∈ highDiskL2) (completedH1_bulk 0 first)).mpr firstHigh
  have highSecond : diskBulk (completedH1 0 second) ∈ highDiskL2 :=
    (congrArg (fun value : DiskL2 1 => value ∈ highDiskL2) (completedH1_bulk 0 second)).mpr secondHigh
  let firstH1 : highDiskGrade := ⟨completedH1 0 first, diskGrade_high_of_bulk parameters _ highFirst⟩
  let secondH1 : highDiskGrade := ⟨completedH1 0 second, diskGrade_high_of_bulk parameters _ highSecond⟩
  have scalar := congrArg (unitDiskBulk 0) samePDE
  have boundary := completedRobinL2_equal_of_trace first second sameRobin
  have equal : firstH1 = secondH1 := by
    apply robinValue_separates parameter
    intro test
    exact (completedRobin_weak_identity parameter first firstH1 rfl test).trans
      ((congrArg₂ (fun first second : ℂ => first + second)
        (congrArg (fun value : DiskL2 1 => inner ℂ (highDiskBulk test) value) scalar)
        (congrArg (fun value : BoundaryL2 => inner ℂ (robinTrace test) value) boundary)).trans
          (completedRobin_weak_identity parameter second secondH1 rfl test).symm)
  apply ordinaryBulk_injective parameters 2
  exact (completedH1_bulk 0 first).symm.trans
    ((congrArg (fun value : highDiskGrade => diskBulk value.val) equal).trans (completedH1_bulk 0 second))

theorem inhomogeneousCompletedInverse_unique_H2 (parameters : PhaseParameters) (parameter : ℝ)
    (source : unitDiskSobolev 0) (sourceHigh : unitDiskBulk 0 source ∈ highDiskL2)
    (boundary : normalBoundaryGrade 2)
    (boundaryHigh : ∀ mode ∈ lowAngularModes, normalBoundaryCoefficient 2 boundary mode = 0)
    (candidate : unitDiskSobolev 2) (candidateHigh : unitDiskBulk 2 candidate ∈ highDiskL2)
    (equation : unitScalarOperator 0 parameter candidate = source)
    (robin : ordinaryRobinTrace 0 candidate = boundary.val) :
    candidate = inhomogeneousCompletedInverse 0 parameters parameter (source, boundary) :=
  completedH2_unique parameters parameter candidate _ candidateHigh
    (inhomogeneousCompletedInverse_high 0 parameters parameter source boundary boundaryHigh)
    (equation.trans (inhomogeneousCompletedInverse_scalar 0 parameters parameter source sourceHigh boundary boundaryHigh).symm)
    (robin.trans (inhomogeneousCompletedInverse_robin 0 parameters parameter source boundary).symm)

end Grad.InhomogeneousHighRobin
