import ABG3ActualDiskMultiplier

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Grad.OrdinaryDiskMultiplier
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.OrdinaryDiskCalculus
attribute [local instance] unitNormedSpace

local instance unitComplete (grade : ℕ) : CompleteSpace (unitDiskSobolev grade) := by
  unfold unitDiskSobolev
  infer_instance

/-- Literal U1 multiplier on every ordinary Cartesian Sobolev grade. -/
def unitB (grade : ℕ) : unitDiskSobolev grade →L[ℂ] unitDiskSobolev grade :=
  @correctedOperator (unitDiskSobolev grade) inferInstance (unitNormedSpace grade)
    (unitMode grade)

def unitBConstant (grade : ℕ) : ℝ := 1 + correctionMass * orthogonalGradeConstant grade

theorem unitBConstant_nonnegative (grade : ℕ) : 0 ≤ unitBConstant grade :=
  add_nonneg zero_le_one (mul_nonneg correctionMass_nonnegative (orthogonalGradeConstant_nonnegative grade))

theorem unitB_bound (grade : ℕ) (field : unitDiskSobolev grade) :
    ‖unitB grade field‖ ≤ unitBConstant grade * ‖field‖ :=
  @correctedOperator_bound (unitDiskSobolev grade) inferInstance (unitNormedSpace grade)
    (unitMode grade) (orthogonalGradeConstant grade) (unitMode_opNorm grade) field

theorem unitB_bulk (grade : ℕ) (field : unitDiskSobolev grade) :
    unitDiskBulk grade (unitB grade field) = diskB (unitDiskBulk grade field) :=
  (@correctedOperator_natural (unitDiskSobolev grade) inferInstance (unitNormedSpace grade) (unitComplete grade)
    (DiskL2 1) inferInstance inferInstance inferInstance
    (unitMode grade) diskMode (orthogonalGradeConstant grade) 1 (unitMode_opNorm grade) diskMode_opNorm
    (unitDiskBulk grade) (unitMode_bulk grade) field).trans (correctedDisk_actual _)

theorem unitB_core_bulk (grade : ℕ) (core : ClosedJet 1) :
    unitDiskBulk grade (unitB grade (unitDiskCoreInto grade core)) = diskB (closedL2Core core) :=
  (unitB_bulk grade _).trans (congrArg diskB (unitDiskBulk_core grade core))

theorem unitB_lower {low high : ℕ} (ordered : low ≤ high) (field : unitDiskSobolev high) :
    unitLower ordered (unitB high field) = unitB low (unitLower ordered field) :=
  @correctedOperator_natural (unitDiskSobolev high) inferInstance (unitNormedSpace high) (unitComplete high)
    (unitDiskSobolev low) inferInstance (unitNormedSpace low) (unitComplete low)
    (unitMode high) (unitMode low) (orthogonalGradeConstant high) (orthogonalGradeConstant low)
    (unitMode_opNorm high) (unitMode_opNorm low) (unitLower ordered)
    (unitMode_lower ordered) field

end Grad.OrdinaryDiskMultiplier
