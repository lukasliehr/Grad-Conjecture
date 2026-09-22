import AIM3CompletedDerivatives

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Grad.OrdinaryDiskMultiplier
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.OrdinaryDiskCalculus
attribute [local instance] unitNormedSpace

theorem unitMode_exists (grade : ℕ) (mode : ℤ) :
    ∃ completed : unitDiskSobolev grade →L[ℂ] unitDiskSobolev grade,
      (∀ core, completed (unitDiskCoreInto grade core) = unitDiskCoreInto grade (angularClosedJet mode core)) ∧
      (∀ field, ‖completed field‖ ≤ orthogonalGradeConstant grade * ‖field‖) :=
  unitCore_extension grade grade (angularClosedJetLinear 1 mode) _
    (orthogonalGradeConstant_nonnegative grade) (apAngular_row_bound 1 0 0 1 0 mode)

/-- Actual angular mode projector in the full ordinary Cartesian H^q norm. -/
def unitMode (grade : ℕ) (mode : ℤ) : unitDiskSobolev grade →L[ℂ] unitDiskSobolev grade :=
  (unitMode_exists grade mode).choose

theorem unitMode_core (grade : ℕ) (mode : ℤ) (core : ClosedJet 1) :
    unitMode grade mode (unitDiskCoreInto grade core) = unitDiskCoreInto grade (angularClosedJet mode core) :=
  (unitMode_exists grade mode).choose_spec.1 core

theorem unitMode_bound (grade : ℕ) (mode : ℤ) (field : unitDiskSobolev grade) :
    ‖unitMode grade mode field‖ ≤ orthogonalGradeConstant grade * ‖field‖ :=
  (unitMode_exists grade mode).choose_spec.2 field

theorem unitMode_opNorm (grade : ℕ) (mode : ℤ) :
    ‖unitMode grade mode‖ ≤ orthogonalGradeConstant grade :=
  @ContinuousLinearMap.opNorm_le_bound ℂ ℂ (unitDiskSobolev grade) (unitDiskSobolev grade)
    inferInstance inferInstance inferInstance inferInstance
    (unitNormedSpace grade) (unitNormedSpace grade) (RingHom.id ℂ) _ (orthogonalGradeConstant grade)
    (orthogonalGradeConstant_nonnegative grade)
    (unitMode_bound grade mode)

theorem unitMode_bulk (grade : ℕ) (mode : ℤ) (field : unitDiskSobolev grade) :
    unitDiskBulk grade (unitMode grade mode field) = diskMode mode (unitDiskBulk grade field) := by
  apply isClosed_property (unitDiskCoreInto_denseRange grade)
    (isClosed_eq ((unitDiskBulk grade).continuous.comp (unitMode grade mode).continuous)
      ((diskMode mode).continuous.comp (unitDiskBulk grade).continuous)) _ field
  intro core
  exact (congrArg (unitDiskBulk grade) (unitMode_core grade mode core)).trans
    ((unitDiskBulk_core grade (angularClosedJet mode core)).trans
      ((diskMode_core mode core).symm.trans
        (congrArg (diskMode mode) (unitDiskBulk_core grade core).symm)))

theorem unitMode_lower {low high : ℕ} (ordered : low ≤ high) (mode : ℤ)
    (field : unitDiskSobolev high) :
    unitLower ordered (unitMode high mode field) = unitMode low mode (unitLower ordered field) := by
  apply isClosed_property (unitDiskCoreInto_denseRange high)
    (isClosed_eq ((unitLower ordered).continuous.comp (unitMode high mode).continuous)
      ((unitMode low mode).continuous.comp (unitLower ordered).continuous)) _ field
  intro core
  exact (congrArg (unitLower ordered) (unitMode_core high mode core)).trans
    ((unitLower_core ordered (angularClosedJet mode core)).trans
      ((unitMode_core low mode core).symm.trans
        (congrArg (unitMode low mode) (unitLower_core ordered core).symm)))

end Grad.OrdinaryDiskMultiplier
