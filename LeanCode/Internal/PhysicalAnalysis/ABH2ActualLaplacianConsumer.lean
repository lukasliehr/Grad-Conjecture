import ABH1RepresentedWeakLaplacian

noncomputable section
set_option maxHeartbeats 800000
namespace Grad.OrdinaryWeakLaplacian
open Grad.CartesianState Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.OrdinaryDiskCalculus Grad.OrdinaryDiskMultiplier
open Grad.GaugeCoefficients.Physical.RadialLedger
attribute [local instance] unitNormedSpace

/-- The same actual inverse and original high source, conditional only on
explicit ordinary Hq representatives supplied by the preceding induction step. -/
theorem actualWeakLaplacian_consumer (grade : ℕ) (parameter : ℝ) (source : highDiskL2)
    (state forcing : unitDiskSobolev grade)
    (stateSame : unitDiskBulk grade state = highDiskBulk (highRobinWeakInverse parameter source))
    (sourceSame : unitDiskBulk grade forcing = source.val) :
    ∃ laplacian : unitDiskSobolev grade,
      unitDiskBulk grade laplacian = weakLaplacianValue parameter source ∧
      HasDiskWeakLaplacian (highDiskBulk (highRobinWeakInverse parameter source)) (unitDiskBulk grade laplacian) ∧
      HasDiskWeakLaplacian (unitDiskBulk grade state) (unitDiskBulk grade laplacian) ∧
      ‖laplacian‖ ≤ parameter ^ 2 * unitBConstant grade * ‖state‖ + ‖forcing‖ :=
  ⟨ordinaryLaplacian grade parameter state forcing,
    ordinaryLaplacian_actual grade parameter source state forcing stateSame sourceSame,
    ordinaryLaplacian_weakInverse grade parameter source state forcing stateSame sourceSame,
    ordinaryLaplacian_equation grade parameter source state forcing stateSame sourceSame,
    ordinaryLaplacian_bound grade parameter state forcing⟩

/-- The direct source for the accepted localization step when its state is
at grade q+1 and the forcing is at grade q. No higher regularity is inferred
merely from these representation premises. -/
theorem higherStateLaplacian_consumer (grade : ℕ) (parameter : ℝ) (source : highDiskL2)
    (state : unitDiskSobolev (grade + 1)) (forcing : unitDiskSobolev grade)
    (stateSame : unitDiskBulk (grade + 1) state = highDiskBulk (highRobinWeakInverse parameter source))
    (sourceSame : unitDiskBulk grade forcing = source.val) :
    ∃ laplacian : unitDiskSobolev grade,
      unitDiskBulk grade laplacian = weakLaplacianValue parameter source ∧
      HasDiskWeakLaplacian (unitDiskBulk (grade + 1) state) (unitDiskBulk grade laplacian) ∧
      ‖laplacian‖ ≤
        (parameter ^ 2 * unitBConstant grade * apLoweringConstant grade) * ‖state‖ + ‖forcing‖ := by
  let lowered := unitLower (Nat.le_succ grade) state
  have lowerSame : unitDiskBulk grade lowered = highDiskBulk (highRobinWeakInverse parameter source) :=
    (unitLower_bulk (Nat.le_succ grade) state).trans stateSame
  refine ⟨ordinaryLaplacian grade parameter lowered forcing,
    ordinaryLaplacian_actual grade parameter source lowered forcing lowerSame sourceSame, ?_, ?_⟩
  · exact (congrArg (fun field => HasDiskWeakLaplacian field
      (unitDiskBulk grade (ordinaryLaplacian grade parameter lowered forcing))) stateSame).mpr
        (ordinaryLaplacian_weakInverse grade parameter source lowered forcing lowerSame sourceSame)
  · exact (ordinaryLaplacian_bound grade parameter lowered forcing).trans
      ((add_le_add (mul_le_mul_of_nonneg_left (unitLower_bound (Nat.le_succ grade) state)
        (mul_nonneg (sq_nonneg parameter) (unitBConstant_nonnegative grade))) le_rfl).trans_eq
          (by rw [mul_assoc (parameter ^ 2 * unitBConstant grade)]))

end Grad.OrdinaryWeakLaplacian
