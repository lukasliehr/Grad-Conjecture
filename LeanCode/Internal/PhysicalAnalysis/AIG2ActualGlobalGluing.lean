import AIG1ActualInteriorInduction

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory
open scoped ContDiff
namespace Grad.ActualInverseInduction
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.OrdinaryDiskCalculus Grad.OrdinaryInteriorBootstrap Grad.InteriorLocalization Grad.PDEBootstrap
attribute [local instance] unitNormedSpace

/-- Literal complement of the already accepted fixed interior cutoff. -/
def outerCutoffScalar (point : Spatial) : ℝ := 1 - interiorCutoff.toFun point

theorem outerCutoffScalar_smooth : ContDiff ℝ ∞ outerCutoffScalar :=
  contDiff_const.sub interiorCutoff.smooth

theorem actualCutoff_partition (field : DiskL2 1) :
    diskScalar interiorCutoff.toFun interiorCutoff.smooth field +
      diskScalar outerCutoffScalar outerCutoffScalar_smooth field = field := by
  apply Lp.ext
  filter_upwards [diskScalar_ae interiorCutoff.toFun interiorCutoff.smooth field,
    diskScalar_ae outerCutoffScalar outerCutoffScalar_smooth field,
    Lp.coeFn_add (diskScalar interiorCutoff.toFun interiorCutoff.smooth field)
      (diskScalar outerCutoffScalar outerCutoffScalar_smooth field)] with point inner outer addition
  rw [addition, Pi.add_apply, inner, outer, ← add_smul]
  change (interiorCutoff.toFun point + (1 - interiorCutoff.toFun point)) • field point = field point
  rw [add_sub_cancel, one_smul]

/-- A conditional global induction step: the interior representative is
constructed from the preceding global state and forcing; the SAME actual
outer (1−χ)u representative at q+2 is a separate, explicit collar obligation.
No construction or bound for that collar representative is asserted here. -/
theorem actualGlobal_inductionStep (parameters : PhaseParameters) (grade : ℕ)
    (parameter : ℝ) (source : highDiskL2)
    (state : unitDiskSobolev (grade + 1)) (forcing : unitDiskSobolev grade)
    (stateSame : unitDiskBulk (grade + 1) state = highDiskBulk (highRobinWeakInverse parameter source))
    (sourceSame : unitDiskBulk grade forcing = source.val)
    (outer : unitDiskSobolev (grade + 2))
    (outerSame : unitDiskBulk (grade + 2) outer =
      diskScalar outerCutoffScalar outerCutoffScalar_smooth (highDiskBulk (highRobinWeakInverse parameter source))) :
    ∃ global : unitDiskSobolev (grade + 2),
      unitDiskBulk (grade + 2) global = highDiskBulk (highRobinWeakInverse parameter source) ∧
      HasDiskWeakLaplacian (unitDiskBulk (grade + 2) global) (weakLaplacianValue parameter source) ∧
      ‖global‖ ≤ inverseInteriorStateConstant grade parameter * ‖state‖ +
        ordinaryInteriorSourceConstant grade * ‖forcing‖ + ‖outer‖ := by
  have interiorExists : ∃ interior : unitDiskSobolev (grade + 2),
      unitDiskBulk (grade + 2) interior = diskScalar interiorCutoff.toFun interiorCutoff.smooth
        (highDiskBulk (highRobinWeakInverse parameter source)) ∧
      ‖interior‖ ≤ inverseInteriorStateConstant grade parameter * ‖state‖ +
        ordinaryInteriorSourceConstant grade * ‖forcing‖ :=
    actualInterior_inductionStep parameters grade parameter source state forcing stateSame sourceSame
  obtain ⟨interior, interiorSame, interiorBound⟩ := interiorExists
  have globalSame : unitDiskBulk (grade + 2) (interior + outer) =
      highDiskBulk (highRobinWeakInverse parameter source) :=
    ((unitDiskBulk (grade + 2)).map_add interior outer).trans
      ((congrArg₂ (fun first second : DiskL2 1 => first + second) interiorSame outerSame).trans
        (actualCutoff_partition _))
  exact ⟨interior + outer, globalSame,
    (congrArg (fun field => HasDiskWeakLaplacian field (weakLaplacianValue parameter source)) globalSame).mpr
      (weakInverse_distribution parameter source),
    (norm_add_le interior outer).trans (add_le_add interiorBound le_rfl)⟩

end Grad.ActualInverseInduction
