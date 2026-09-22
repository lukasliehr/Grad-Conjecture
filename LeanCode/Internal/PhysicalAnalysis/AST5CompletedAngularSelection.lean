import AST4CoreProjectionEnergy

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open Set Filter MeasureTheory
open scoped Topology BigOperators
namespace Grad.AngularSobolevTruncation
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.OrdinaryDiskCalculus
attribute [local instance] unitNormedSpace

theorem ordinaryMode_exists (grade : ℕ) (mode : ℤ) :
    ∃ completed : unitDiskSobolev grade →L[ℂ] unitDiskSobolev grade,
      (∀ core, completed (unitDiskCoreInto grade core) = unitDiskCoreInto grade (angularClosedJet mode core)) ∧
      (∀ field, ‖completed field‖ ≤ orthogonalGradeConstant grade * ‖field‖) := by
  apply unitCore_extension grade grade (angularClosedJetLinear 1 mode) (orthogonalGradeConstant grade)
    (orthogonalGradeConstant_nonnegative grade)
  intro core
  exact apAngular_row_bound 1 0 0 1 0 mode core

def ordinaryMode (grade : ℕ) (mode : ℤ) : unitDiskSobolev grade →L[ℂ] unitDiskSobolev grade :=
  (ordinaryMode_exists grade mode).choose

theorem ordinaryMode_core (grade : ℕ) (mode : ℤ) (core : ClosedJet 1) :
    ordinaryMode grade mode (unitDiskCoreInto grade core) = unitDiskCoreInto grade (angularClosedJet mode core) :=
  (ordinaryMode_exists grade mode).choose_spec.1 core

theorem ordinaryMode_bound (grade : ℕ) (mode : ℤ) (field : unitDiskSobolev grade) :
    ‖ordinaryMode grade mode field‖ ≤ orthogonalGradeConstant grade * ‖field‖ :=
  (ordinaryMode_exists grade mode).choose_spec.2 field

theorem ordinaryMode_bulk (grade : ℕ) (mode : ℤ) (field : unitDiskSobolev grade) :
    unitDiskBulk grade (ordinaryMode grade mode field) = diskMode mode (unitDiskBulk grade field) := by
  apply isClosed_property (unitDiskCoreInto_denseRange grade)
    (isClosed_eq ((unitDiskBulk grade).continuous.comp (ordinaryMode grade mode).continuous)
      ((diskMode mode).continuous.comp (unitDiskBulk grade).continuous)) _ field
  intro core
  exact (congrArg (unitDiskBulk grade) (ordinaryMode_core grade mode core)).trans
    ((unitDiskBulk_core grade (angularClosedJet mode core)).trans
      ((diskMode_core mode core).symm.trans
        (congrArg (diskMode mode) (unitDiskBulk_core grade core).symm)))

def ordinarySelected (grade : ℕ) (modes : Finset ℤ) : unitDiskSobolev grade →L[ℂ] unitDiskSobolev grade :=
  ∑ mode ∈ modes, ordinaryMode grade mode

theorem ordinarySelected_apply (grade : ℕ) (modes : Finset ℤ) (field : unitDiskSobolev grade) :
    ordinarySelected grade modes field = ∑ mode ∈ modes, ordinaryMode grade mode field := by
  simp only [ordinarySelected, sum_apply]

theorem ordinarySelected_core (grade : ℕ) (modes : Finset ℤ) (core : ClosedJet 1) :
    ordinarySelected grade modes (unitDiskCoreInto grade core) =
      unitDiskCoreInto grade (selectedAngularJet modes core) := by
  calc
    _ = ∑ mode ∈ modes, ordinaryMode grade mode (unitDiskCoreInto grade core) := ordinarySelected_apply _ _ _
    _ = ∑ mode ∈ modes, unitDiskCoreInto grade (angularClosedJet mode core) :=
      Finset.sum_congr rfl (fun mode _ => ordinaryMode_core grade mode core)
    _ = unitDiskCoreInto grade (∑ mode ∈ modes, angularClosedJet mode core) := (map_sum _ _ _).symm
    _ = _ := congrArg (unitDiskCoreInto grade) (selectedAngularJet_eq modes core).symm

theorem ordinarySelected_bulk (grade : ℕ) (modes : Finset ℤ) (field : unitDiskSobolev grade) :
    unitDiskBulk grade (ordinarySelected grade modes field) = diskSelectedModes modes (unitDiskBulk grade field) := by
  calc
    _ = unitDiskBulk grade (∑ mode ∈ modes, ordinaryMode grade mode field) :=
      congrArg (unitDiskBulk grade) (ordinarySelected_apply grade modes field)
    _ = ∑ mode ∈ modes, unitDiskBulk grade (ordinaryMode grade mode field) := map_sum _ _ _
    _ = ∑ mode ∈ modes, diskMode mode (unitDiskBulk grade field) :=
      Finset.sum_congr rfl (fun mode _ => ordinaryMode_bulk grade mode field)
    _ = _ := (diskSelectedModes_apply modes _).symm

theorem ordinaryMode_square_sum (grade : ℕ) (modes : Finset ℤ) (field : unitDiskSobolev grade) :
    (∑ mode ∈ modes, ‖ordinaryMode grade mode field‖ ^ 2) ≤ orthogonalGradeConstant grade ^ 2 * ‖field‖ ^ 2 := by
  apply isClosed_property (unitDiskCoreInto_denseRange grade)
    (isClosed_le (continuous_finsetSum modes (fun mode _ => (ordinaryMode grade mode).continuous.norm.pow 2))
      (continuous_const.mul (continuous_norm.pow 2))) _ field
  intro core
  change (∑ mode ∈ modes, ‖ordinaryMode grade mode (unitDiskCoreInto grade core)‖ ^ 2) ≤
    orthogonalGradeConstant grade ^ 2 * ‖unitDiskCoreInto grade core‖ ^ 2
  simp only [ordinaryMode_core, unitDiskCore_norm]
  exact coreAngular_square_sum grade modes core

theorem ordinarySelected_square_bound (grade : ℕ) (modes : Finset ℤ) (field : unitDiskSobolev grade) :
    ‖ordinarySelected grade modes field‖ ^ 2 ≤
      orthogonalGradeConstant grade ^ 2 * ∑ mode ∈ modes, ‖ordinaryMode grade mode field‖ ^ 2 := by
  apply isClosed_property (unitDiskCoreInto_denseRange grade)
    (isClosed_le ((ordinarySelected grade modes).continuous.norm.pow 2)
      (continuous_const.mul (continuous_finsetSum modes (fun mode _ => (ordinaryMode grade mode).continuous.norm.pow 2)))) _ field
  intro core
  change ‖ordinarySelected grade modes (unitDiskCoreInto grade core)‖ ^ 2 ≤
    orthogonalGradeConstant grade ^ 2 * ∑ mode ∈ modes, ‖ordinaryMode grade mode (unitDiskCoreInto grade core)‖ ^ 2
  simp only [ordinarySelected_core, ordinaryMode_core, unitDiskCore_norm]
  exact coreSelected_square_bound grade modes core

/-- The finite angular selection is bounded independently of its cardinality,
with the actual ordinary Cartesian Sobolev norm. -/
theorem ordinarySelected_uniform_bound (grade : ℕ) (modes : Finset ℤ) (field : unitDiskSobolev grade) :
    ‖ordinarySelected grade modes field‖ ≤ orthogonalGradeConstant grade ^ 2 * ‖field‖ := by
  apply isClosed_property (unitDiskCoreInto_denseRange grade)
    (isClosed_le (ordinarySelected grade modes).continuous.norm (continuous_const.mul continuous_norm)) _ field
  intro core
  change ‖ordinarySelected grade modes (unitDiskCoreInto grade core)‖ ≤
    orthogonalGradeConstant grade ^ 2 * ‖unitDiskCoreInto grade core‖
  simp only [ordinarySelected_core, unitDiskCore_norm]
  exact coreSelected_uniform_bound grade modes core

end Grad.AngularSobolevTruncation
