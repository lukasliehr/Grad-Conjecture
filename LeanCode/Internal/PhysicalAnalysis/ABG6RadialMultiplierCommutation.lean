import ABG4OrdinaryMultiplier
import ABG5RadialScalarModes

noncomputable section
set_option maxHeartbeats 800000
open scoped ContDiff
namespace Grad.OrdinaryDiskMultiplier
open Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.OrdinaryDiskCalculus
open Grad.InteriorLocalization Grad.PDEBootstrap
attribute [local instance] unitNormedSpace

theorem unitB_scalar (grade : ℕ) (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (radial : RadialScalar scalar) (field : unitDiskSobolev grade) :
    unitScalar grade scalar smooth (unitB grade field) =
      unitB grade (unitScalar grade scalar smooth field) :=
  @correctedOperator_natural (unitDiskSobolev grade) inferInstance (unitNormedSpace grade) (unitComplete grade)
    (unitDiskSobolev grade) inferInstance (unitNormedSpace grade) (unitComplete grade)
    (unitMode grade) (unitMode grade) (orthogonalGradeConstant grade) (orthogonalGradeConstant grade)
    (unitMode_opNorm grade) (unitMode_opNorm grade) (unitScalar grade scalar smooth)
    (unitMode_scalar grade scalar smooth radial) field

theorem diskB_scalar (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (radial : RadialScalar scalar) (field : DiskL2 1) :
    diskScalar scalar smooth (diskB field) = diskB (diskScalar scalar smooth field) :=
  (congrArg (diskScalar scalar smooth) (correctedDisk_actual field).symm).trans
    ((correctedOperator_natural diskMode diskMode 1 1 diskMode_opNorm diskMode_opNorm
      (diskScalar scalar smooth) (diskMode_scalar scalar smooth radial) field).trans
      (correctedDisk_actual _))

/-- T4 on the actual ordinary Cartesian completion, with the same L2 bulk.
The radial scalar clause uses proved rotation invariance of its literal function. -/
theorem ordinaryMultiplier_consumer (grade : ℕ) (field : unitDiskSobolev grade)
    (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar) (radial : RadialScalar scalar) :
    unitDiskBulk grade (unitB grade field) = diskB (unitDiskBulk grade field) ∧
    ‖unitB grade field‖ ≤ unitBConstant grade * ‖field‖ ∧
    unitScalar grade scalar smooth (unitB grade field) = unitB grade (unitScalar grade scalar smooth field) ∧
    diskScalar scalar smooth (diskB (unitDiskBulk grade field)) =
      diskB (diskScalar scalar smooth (unitDiskBulk grade field)) :=
  ⟨unitB_bulk grade field, unitB_bound grade field, unitB_scalar grade scalar smooth radial field,
    diskB_scalar scalar smooth radial _⟩

end Grad.OrdinaryDiskMultiplier
