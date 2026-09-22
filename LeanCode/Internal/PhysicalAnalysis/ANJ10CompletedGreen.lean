import ANJ9CompletedPhysicalTrace
import ASU5LiteralStrongConsumer

noncomputable section
set_option maxHeartbeats 1200000
open Set
namespace Grad.InhomogeneousHighRobin
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.OrdinaryDiskCalculus Grad.CircularNormalLift Grad.NonlinearRange Grad.NonlinearDivision
open Grad.SmoothRobinUniqueness
local instance (priority := 2000) greenUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade

def completedLaplacianL2 : unitDiskSobolev 2 →L[ℂ] DiskL2 1 := (unitDiskBulk 0).comp (unitCartesianLaplacian 0)

/-- Full Green identity for every original H2 field and every H1 test. -/
theorem completedH2_Green (test : diskGrade) (field : unitDiskSobolev 2) :
    inner ℂ (diskGradX test) (diskGradX (completedH1 0 field)) +
      inner ℂ (diskGradY test) (diskGradY (completedH1 0 field)) +
      inner ℂ (diskBulk test) (completedLaplacianL2 field) =
      inner ℂ (diskBoundary test) (diskBoundary (completedEulerH1 field)) := by
  apply isClosed_property (unitDiskCoreInto_denseRange 2)
    (isClosed_eq (((continuous_const.inner (diskGradX.continuous.comp (completedH1 0).continuous)).add
      (continuous_const.inner (diskGradY.continuous.comp (completedH1 0).continuous))).add
      (continuous_const.inner completedLaplacianL2.continuous))
      (continuous_const.inner (diskBoundary.continuous.comp completedEulerH1.continuous))) _ field
  intro core
  have first := congrArg (fun value : diskGrade =>
    inner ℂ (diskGradX test) (diskGradX value) + inner ℂ (diskGradY test) (diskGradY value)) (completedH1_core 0 core)
  have second := congrArg (fun value : DiskL2 1 => inner ℂ (diskBulk test) value) (unitCartesianLaplacian_core_bulk 0 core)
  have boundary := congrArg (fun value : BoundaryL2 => inner ℂ (diskBoundary test) value)
    ((congrArg diskBoundary (completedEulerH1_core core)).trans (diskBoundary_core (eulerJet core)))
  exact (congrArg₂ (fun first second : ℂ => first + second) first second).trans
    ((completedTest_Green test core).trans boundary.symm)

private theorem green_robin_algebra (gradient laplacian normal mass trace parameter : ℂ)
    (green : gradient + laplacian = normal) :
    gradient + parameter * mass + 2 * trace =
      (parameter * mass - laplacian) + (normal + 2 * trace) := by
  linear_combination green

/-- Actual H2 scalar and Robin traces give the original coercive weak form. -/
theorem completedRobin_weak_identity (parameter : ℝ) (field : unitDiskSobolev 2)
    (highField : highDiskGrade) (same : highField.val = completedH1 0 field) (test : highDiskGrade) :
    robinValue parameter highField test =
      inner ℂ (highDiskBulk test) (unitDiskBulk 0 (unitScalarOperator 0 parameter field)) +
        inner ℂ (robinTrace test) (completedRobinL2 field) := by
  have x := congrArg diskGradX same
  have y := congrArg diskGradY same
  have bulk := (congrArg diskBulk same).trans (completedH1_bulk 0 field)
  have boundary := congrArg diskBoundary same
  have green := completedH2_Green test.val field
  have algebra := green_robin_algebra
    (inner ℂ (diskGradX test.val) (diskGradX (completedH1 0 field)) +
      inner ℂ (diskGradY test.val) (diskGradY (completedH1 0 field)))
    (inner ℂ (diskBulk test.val) (completedLaplacianL2 field))
    (inner ℂ (diskBoundary test.val) (diskBoundary (completedEulerH1 field)))
    (inner ℂ (diskBulk test.val) (diskB (unitDiskBulk 2 field)))
    (inner ℂ (diskBoundary test.val) (diskBoundary (completedH1 0 field))) ((parameter ^ 2 : ℝ) : ℂ) green
  have left := congrArg₂ (fun first second : DiskL2 1 =>
    inner ℂ (highGradX test) first + inner ℂ (highGradY test) second) x y
  have mass := congrArg (fun value : DiskL2 1 =>
    ((parameter ^ 2 : ℝ) : ℂ) * inner ℂ (highDiskBulk test) (diskB value)) bulk
  have trace := congrArg (fun value : BoundaryL2 => (2 : ℂ) * inner ℂ (robinTrace test) value) boundary
  have changed := congrArg₂ (fun first second : ℂ => first + second)
    (congrArg₂ (fun first second : ℂ => first + second) left mass) trace
  have scalar := congrArg (fun value : DiskL2 1 => inner ℂ (highDiskBulk test) value)
    (unitScalarOperator_bulk 0 parameter field)
  have normal := (diskBoundary.map_add (completedEulerH1 field) ((2 : ℂ) • completedH1 0 field)).trans
    (congrArg (fun value => diskBoundary (completedEulerH1 field) + value)
      (diskBoundary.map_smul (2 : ℂ) (completedH1 0 field)))
  have robin := congrArg (fun value : BoundaryL2 => inner ℂ (robinTrace test) value) normal
  simp only [inner_sub_right, inner_smul_right] at scalar
  simp only [inner_add_right, inner_smul_right] at robin
  exact changed.trans (algebra.trans (congrArg₂ (fun first second : ℂ => first + second) scalar robin).symm)

end Grad.InhomogeneousHighRobin
