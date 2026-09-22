import ABG7ActualMultiplierConsumer
import ANR8WeakDistribution

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Grad.OrdinaryWeakLaplacian
open Grad.CartesianState Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.OrdinaryDiskCalculus Grad.OrdinaryDiskMultiplier
attribute [local instance] unitNormedSpace

/-- The literal k²Bz−F expression in the same ordinary Sobolev grade. -/
def ordinaryLaplacian (grade : ℕ) (parameter : ℝ)
    (state forcing : unitDiskSobolev grade) : unitDiskSobolev grade :=
  ((parameter ^ 2 : ℝ) : ℂ) • unitB grade state - forcing

theorem ordinaryLaplacian_bulk (grade : ℕ) (parameter : ℝ) (state forcing : unitDiskSobolev grade) :
    unitDiskBulk grade (ordinaryLaplacian grade parameter state forcing) =
      ((parameter ^ 2 : ℝ) : ℂ) • diskB (unitDiskBulk grade state) - unitDiskBulk grade forcing := by
  exact ((unitDiskBulk grade).map_sub (((parameter ^ 2 : ℝ) : ℂ) • unitB grade state) forcing).trans
    (congrArg (fun value : DiskL2 1 => value - unitDiskBulk grade forcing)
      (((unitDiskBulk grade).map_smul (((parameter ^ 2 : ℝ) : ℂ)) (unitB grade state)).trans
        (congrArg (fun value : DiskL2 1 => ((parameter ^ 2 : ℝ) : ℂ) • value)
          (unitB_bulk grade state))))

private theorem scaledDifference_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (parameter constant : ℝ) (image state forcing : E) (bound : ‖image‖ ≤ constant * ‖state‖) :
    ‖((parameter ^ 2 : ℝ) : ℂ) • image - forcing‖ ≤ parameter ^ 2 * constant * ‖state‖ + ‖forcing‖ := by
  have triangle := norm_sub_le (((parameter ^ 2 : ℝ) : ℂ) • image) forcing
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg parameter)] at triangle
  exact triangle.trans ((add_le_add (mul_le_mul_of_nonneg_left bound (sq_nonneg parameter)) le_rfl).trans_eq
    (by rw [mul_assoc]))

theorem ordinaryLaplacian_bound (grade : ℕ) (parameter : ℝ) (state forcing : unitDiskSobolev grade) :
    ‖ordinaryLaplacian grade parameter state forcing‖ ≤
      parameter ^ 2 * unitBConstant grade * ‖state‖ + ‖forcing‖ :=
  @scaledDifference_bound (unitDiskSobolev grade) inferInstance (unitNormedSpace grade)
    parameter (unitBConstant grade) (unitB grade state) state forcing (unitB_bound grade state)

theorem ordinaryLaplacian_actual (grade : ℕ) (parameter : ℝ) (source : highDiskL2)
    (state forcing : unitDiskSobolev grade)
    (stateSame : unitDiskBulk grade state = highDiskBulk (highRobinWeakInverse parameter source))
    (sourceSame : unitDiskBulk grade forcing = source.val) :
    unitDiskBulk grade (ordinaryLaplacian grade parameter state forcing) = weakLaplacianValue parameter source := by
  exact (ordinaryLaplacian_bulk grade parameter state forcing).trans
    (congrArg₂ (fun first second : DiskL2 1 => ((parameter ^ 2 : ℝ) : ℂ) • diskB first - second)
      stateSame sourceSame)

theorem ordinaryLaplacian_weakInverse (grade : ℕ) (parameter : ℝ) (source : highDiskL2)
    (state forcing : unitDiskSobolev grade)
    (stateSame : unitDiskBulk grade state = highDiskBulk (highRobinWeakInverse parameter source))
    (sourceSame : unitDiskBulk grade forcing = source.val) :
    HasDiskWeakLaplacian (highDiskBulk (highRobinWeakInverse parameter source))
      (unitDiskBulk grade (ordinaryLaplacian grade parameter state forcing)) :=
  (congrArg (fun laplacian => HasDiskWeakLaplacian
    (highDiskBulk (highRobinWeakInverse parameter source)) laplacian)
      (ordinaryLaplacian_actual grade parameter source state forcing stateSame sourceSame)).mpr
        (weakInverse_distribution parameter source)

theorem ordinaryLaplacian_equation (grade : ℕ) (parameter : ℝ) (source : highDiskL2)
    (state forcing : unitDiskSobolev grade)
    (stateSame : unitDiskBulk grade state = highDiskBulk (highRobinWeakInverse parameter source))
    (sourceSame : unitDiskBulk grade forcing = source.val) :
    HasDiskWeakLaplacian (unitDiskBulk grade state)
      (unitDiskBulk grade (ordinaryLaplacian grade parameter state forcing)) :=
  (congrArg (fun field => HasDiskWeakLaplacian field
    (unitDiskBulk grade (ordinaryLaplacian grade parameter state forcing))) stateSame).mpr
      (ordinaryLaplacian_weakInverse grade parameter source state forcing stateSame sourceSame)

end Grad.OrdinaryWeakLaplacian
