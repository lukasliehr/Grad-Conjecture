import ASU3FullSmoothGreen

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.SmoothRobinUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.BoundaryTrace
open Grad.CircularHighRegularity Grad.CircularHighWeak Grad.NonlinearDivision Grad.NonlinearRange

/-- The actual completed scalar expression, using the accepted diskB. -/
def strongResidualBulk (parameter : ℝ) (field : ClosedJet 1) : DiskL2 1 :=
  -closedL2Core (laplacianJet field) + ((parameter ^ 2 : ℝ) : ℂ) • diskB (closedL2Core field)

/-- Ordinary dθ Robin datum, with the actual outward Euler derivative and +2. -/
def strongRobinBoundary (field : ClosedJet 1) : BoundaryL2 :=
  coreBoundaryL2 (eulerJet field) + (2 : ℂ) • coreBoundaryL2 field

theorem smoothHigh_fixed (field : ClosedJet 1) (high : closedL2Core field ∈ highDiskL2) :
    excludedAngularJet lowAngularModes field = field := by
  apply closedL2Core_injective
  exact (highL2Projection_core field).symm.trans (highL2Projection_fixed ⟨closedL2Core field, high⟩)

theorem highDiskCoreInto_actual (field : ClosedJet 1) (high : closedL2Core field ∈ highDiskL2) :
    (highDiskCoreInto field).val = diskCoreInto field :=
  congrArg diskCoreInto (smoothHigh_fixed field high)

private theorem green_robin_algebra (gradient laplacian normal mass trace parameter : ℂ)
    (green : gradient + laplacian = normal) :
    gradient + parameter * mass + 2 * trace =
      (-laplacian + parameter * mass) + (normal + 2 * trace) := by
  linear_combination green

/-- Strong scalar data and ordinary Robin data give the exact completed weak form. -/
theorem strongRobin_weak_identity (parameter : ℝ) (core : ClosedJet 1)
    (field : highDiskGrade) (same : field.val = diskCoreInto core) (test : highDiskGrade) :
    robinValue parameter field test =
      inner ℂ (highDiskBulk test) (strongResidualBulk parameter core) +
        inner ℂ (robinTrace test) (strongRobinBoundary core) := by
  have x : highGradX field = diskGradX (diskCoreInto core) := congrArg diskGradX same
  have y : highGradY field = diskGradY (diskCoreInto core) := congrArg diskGradY same
  have bulk : highDiskBulk field = closedL2Core core := (congrArg diskBulk same).trans (diskBulk_core core)
  have boundary : robinTrace field = coreBoundaryL2 core := (congrArg diskBoundary same).trans (diskBoundary_core core)
  have green := completedTest_Green test.val core
  have algebra := green_robin_algebra
    (inner ℂ (diskGradX test.val) (diskGradX (diskCoreInto core)) +
      inner ℂ (diskGradY test.val) (diskGradY (diskCoreInto core)))
    (inner ℂ (diskBulk test.val) (closedL2Core (laplacianJet core)))
    (inner ℂ (diskBoundary test.val) (coreBoundaryL2 (eulerJet core)))
    (inner ℂ (diskBulk test.val) (diskB (closedL2Core core)))
    (inner ℂ (diskBoundary test.val) (coreBoundaryL2 core)) ((parameter ^ 2 : ℝ) : ℂ) green
  have value : robinValue parameter field test =
      (inner ℂ (diskGradX test.val) (diskGradX (diskCoreInto core)) +
        inner ℂ (diskGradY test.val) (diskGradY (diskCoreInto core))) +
      ((parameter ^ 2 : ℝ) : ℂ) * inner ℂ (diskBulk test.val) (diskB (closedL2Core core)) +
      2 * inner ℂ (diskBoundary test.val) (coreBoundaryL2 core) :=
    congrArg₂ (fun first second : ℂ => first + second)
      (congrArg₂ (fun first second : ℂ => first + second)
        (congrArg₂ (fun first second : ℂ => first + second)
          (congrArg (fun slope : DiskL2 1 => inner ℂ (highGradX test) slope) x)
          (congrArg (fun slope : DiskL2 1 => inner ℂ (highGradY test) slope) y))
        (congrArg (fun source : DiskL2 1 => ((parameter ^ 2 : ℝ) : ℂ) *
          inner ℂ (highDiskBulk test) (diskB source)) bulk))
      (congrArg (fun trace : BoundaryL2 => (2 : ℂ) * inner ℂ (robinTrace test) trace) boundary)
  have sourcePairing : inner ℂ (highDiskBulk test) (strongResidualBulk parameter core) =
      -inner ℂ (diskBulk test.val) (closedL2Core (laplacianJet core)) +
        ((parameter ^ 2 : ℝ) : ℂ) * inner ℂ (diskBulk test.val) (diskB (closedL2Core core)) :=
    (inner_add_right (𝕜 := ℂ) _ _ _).trans
      (congrArg₂ (fun first second : ℂ => first + second) (inner_neg_right _ _)
        (inner_smul_right _ _ _))
  have tracePairing : inner ℂ (robinTrace test) (strongRobinBoundary core) =
      inner ℂ (diskBoundary test.val) (coreBoundaryL2 (eulerJet core)) +
        2 * inner ℂ (diskBoundary test.val) (coreBoundaryL2 core) :=
    (inner_add_right (𝕜 := ℂ) _ _ _).trans
      (congrArg (fun second : ℂ => inner ℂ (robinTrace test) (coreBoundaryL2 (eulerJet core)) + second)
        (inner_smul_right _ _ _))
  exact value.trans (algebra.trans (congrArg₂ (fun first second : ℂ => first + second) sourcePairing tracePairing).symm)

theorem strongRobinBoundary_equal (first second : ClosedJet 1)
    (same : ∀ angle : CellCircle,
      (eulerJet first).value (boundaryDiskPoint angle) + (2 : ℂ) • first.value (boundaryDiskPoint angle) =
        (eulerJet second).value (boundaryDiskPoint angle) + (2 : ℂ) • second.value (boundaryDiskPoint angle)) :
    strongRobinBoundary first = strongRobinBoundary second := by
  have continuousEqual : closedBoundaryValue (eulerJet first + (2 : ℂ) • first) =
      closedBoundaryValue (eulerJet second + (2 : ℂ) • second) := by
    apply ContinuousMap.ext
    intro angle
    exact same angle
  have lifted := congrArg ((ContinuousMap.toLp 2 (volume : Measure CellCircle) ℂ).toLinearMap) continuousEqual
  change coreBoundaryL2 (eulerJet first + (2 : ℂ) • first) =
    coreBoundaryL2 (eulerJet second + (2 : ℂ) • second) at lifted
  simpa only [map_add, map_smul, strongRobinBoundary] using lifted

theorem strongRobinBoundary_zero (field : ClosedJet 1)
    (zero : ∀ angle : CellCircle,
      (eulerJet field).value (boundaryDiskPoint angle) + (2 : ℂ) • field.value (boundaryDiskPoint angle) = 0) :
    strongRobinBoundary field = 0 := by
  have continuousZero : closedBoundaryValue (eulerJet field + (2 : ℂ) • field) = 0 := by
    apply ContinuousMap.ext
    intro angle
    exact zero angle
  have lifted := congrArg ((ContinuousMap.toLp 2 (volume : Measure CellCircle) ℂ).toLinearMap) continuousZero
  change coreBoundaryL2 (eulerJet field + (2 : ℂ) • field) = 0 at lifted
  simpa only [map_add, map_smul, strongRobinBoundary] using lifted

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

/-- Full smooth high uniqueness for equal actual scalar PDE and Robin data.
No weak equation or generic uniqueness premise is supplied. -/
theorem strongRobin_unique (parameter : ℝ) (first second : ClosedJet 1)
    (firstHigh : closedL2Core first ∈ highDiskL2) (secondHigh : closedL2Core second ∈ highDiskL2)
    (samePDE : strongResidualBulk parameter first = strongResidualBulk parameter second)
    (sameRobin : ∀ angle : CellCircle,
      (eulerJet first).value (boundaryDiskPoint angle) + (2 : ℂ) • first.value (boundaryDiskPoint angle) =
        (eulerJet second).value (boundaryDiskPoint angle) + (2 : ℂ) • second.value (boundaryDiskPoint angle)) :
    first = second := by
  have firstCore := highDiskCoreInto_actual first firstHigh
  have secondCore := highDiskCoreInto_actual second secondHigh
  have boundary := strongRobinBoundary_equal first second sameRobin
  have weakEqual : highDiskCoreInto first = highDiskCoreInto second := by
    apply robinValue_separates parameter
    intro test
    exact (strongRobin_weak_identity parameter first (highDiskCoreInto first) firstCore test).trans
      ((congrArg₂ (fun pde trace : ℂ => pde + trace)
        (congrArg (fun source : DiskL2 1 => inner ℂ (highDiskBulk test) source) samePDE)
        (congrArg (fun source : BoundaryL2 => inner ℂ (robinTrace test) source) boundary)).trans
        (strongRobin_weak_identity parameter second (highDiskCoreInto second) secondCore test).symm)
  apply diskCoreInto_injective
  exact firstCore.symm.trans ((congrArg Subtype.val weakEqual).trans secondCore)

/-- A smooth high homogeneous-Robin strong solution is the actual ANH inverse. -/
theorem strongRobin_is_weakInverse (parameter : ℝ) (source : highDiskL2) (field : ClosedJet 1)
    (high : closedL2Core field ∈ highDiskL2) (pde : strongResidualBulk parameter field = source.val)
    (robin : ∀ angle : CellCircle,
      (eulerJet field).value (boundaryDiskPoint angle) + (2 : ℂ) • field.value (boundaryDiskPoint angle) = 0) :
    diskCoreInto field = (highRobinWeakInverse parameter source).val := by
  have same := highDiskCoreInto_actual field high
  have boundary := strongRobinBoundary_zero field robin
  have weak : highDiskCoreInto field = weakSolution parameter source := by
    apply weakSolution_unique
    intro test
    have identity := strongRobin_weak_identity parameter field (highDiskCoreInto field) same test
    have sourcePairing := congrArg (fun value : DiskL2 1 => inner ℂ (highDiskBulk test) value) pde
    have tracePairing := (congrArg (fun value : BoundaryL2 => inner ℂ (robinTrace test) value) boundary).trans
      (inner_zero_right _)
    exact identity.trans ((congrArg₂ (fun first second : ℂ => first + second) sourcePairing tracePairing).trans (add_zero _))
  exact same.symm.trans (congrArg Subtype.val weak)

end Grad.SmoothRobinUniqueness
