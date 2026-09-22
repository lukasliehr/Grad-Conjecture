import ABH2ActualLaplacianConsumer
import AIB3InteriorEstimateConsumer

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Grad.ActualInverseInduction
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.OrdinaryDiskCalculus Grad.OrdinaryDiskMultiplier Grad.OrdinaryWeakLaplacian
open Grad.OrdinaryInteriorBootstrap Grad.InteriorLocalization Grad.COR12Extension
open Grad.GaugeCoefficients.Physical.RadialLedger
attribute [local instance] unitNormedSpace

theorem interiorSourceConstant_nonnegative (grade : ℕ) : 0 ≤ ordinaryInteriorSourceConstant grade :=
  mul_nonneg (mul_nonneg (sameGradeConstant_nonnegative (grade + 2)) (sameGradeConstant_nonnegative grade))
    (unitProductConstant_nonnegative grade _)

def inverseInteriorStateConstant (grade : ℕ) (parameter : ℝ) : ℝ :=
  ordinaryInteriorSourceConstant grade *
    (parameter ^ 2 * unitBConstant grade * apLoweringConstant grade) + ordinaryInteriorStateConstant grade

/-- One genuine interior regularity step for the SAME accepted weak inverse.
The preceding global H^(q+1) representative and forcing Hq representative
are explicit induction inputs, not asserted regularity of the inverse. -/
theorem actualInterior_inductionStep (parameters : PhaseParameters) (grade : ℕ)
    (parameter : ℝ) (source : highDiskL2)
    (state : unitDiskSobolev (grade + 1)) (forcing : unitDiskSobolev grade)
    (stateSame : unitDiskBulk (grade + 1) state = highDiskBulk (highRobinWeakInverse parameter source))
    (sourceSame : unitDiskBulk grade forcing = source.val) :
    ∃ interior : unitDiskSobolev (grade + 2),
      unitDiskBulk (grade + 2) interior = diskScalar interiorCutoff.toFun interiorCutoff.smooth
        (highDiskBulk (highRobinWeakInverse parameter source)) ∧
      ‖interior‖ ≤ inverseInteriorStateConstant grade parameter * ‖state‖ +
        ordinaryInteriorSourceConstant grade * ‖forcing‖ := by
  have laplacianExists : ∃ laplacian : unitDiskSobolev grade,
      unitDiskBulk grade laplacian = weakLaplacianValue parameter source ∧
      HasDiskWeakLaplacian (unitDiskBulk (grade + 1) state) (unitDiskBulk grade laplacian) ∧
      ‖laplacian‖ ≤
        (parameter ^ 2 * unitBConstant grade * apLoweringConstant grade) * ‖state‖ + ‖forcing‖ :=
    higherStateLaplacian_consumer grade parameter source state forcing stateSame sourceSame
  obtain ⟨laplacian, _literal, equation, laplacianBound⟩ := laplacianExists
  have interiorExists : ∃ interior : unitDiskSobolev (grade + 2),
      unitDiskBulk (grade + 2) interior =
        diskScalar interiorCutoff.toFun interiorCutoff.smooth (unitDiskBulk (grade + 1) state) ∧
      ‖interior‖ ≤ ordinaryInteriorSourceConstant grade * ‖laplacian‖ +
        ordinaryInteriorStateConstant grade * ‖state‖ :=
    ordinaryInterior_estimate parameters grade state laplacian equation
  obtain ⟨interior, same, bound⟩ := interiorExists
  refine ⟨interior, same.trans (congrArg (diskScalar interiorCutoff.toFun interiorCutoff.smooth) stateSame), ?_⟩
  exact bound.trans ((add_le_add
    (mul_le_mul_of_nonneg_left laplacianBound (interiorSourceConstant_nonnegative grade)) le_rfl).trans_eq (by
      unfold inverseInteriorStateConstant
      ring))

end Grad.ActualInverseInduction
