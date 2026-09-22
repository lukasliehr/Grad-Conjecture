import ANH16HighL2
import ANH5PhysicalBoundary

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace Grad.CircularHighWeak
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger

abbrev diskComplexNormedSpace : NormedSpace ℂ diskGrade := diskGrade.normedSpace
attribute [local instance] diskComplexNormedSpace

private theorem ambientAngular_exists (L sigma gamma ell : ℝ) (dimension grade : ℕ) (mode : ℤ) :
    ∃ completed : apGrade L sigma gamma ell dimension grade →L[ℂ]
        apGrade L sigma gamma ell dimension grade,
      (∀ core, completed (apFiniteInto L sigma gamma ell core) =
        apFiniteInto L sigma gamma ell (apFiniteJetMap (angularClosedJetLinear dimension mode) core)) ∧
      (∀ field, ‖completed field‖ ≤ orthogonalGradeConstant grade * ‖field‖) :=
  apDense_extension (apFiniteInto L sigma gamma ell)
    (apFiniteInto_injective L sigma gamma ell) (apFiniteInto_denseRange L sigma gamma ell)
    ((apFiniteInto L sigma gamma ell).comp (apFiniteJetMap (angularClosedJetLinear dimension mode)))
    (orthogonalGradeConstant grade) (orthogonalGradeConstant_nonnegative grade)
    (apFiniteJetMap_bound L sigma gamma ell _ _ (orthogonalGradeConstant_nonnegative grade)
      (fun cell field => apAngular_row_bound L sigma gamma ell cell mode field))

private def ambientAngular (mode : ℤ) : DiskAmbient →L[ℂ] DiskAmbient :=
  (ambientAngular_exists 1 0 0 1 1 1 mode).choose

private theorem ambientAngular_core (mode : ℤ) (core : ClosedJet 1) :
    ambientAngular mode (diskCore core) = diskCore (angularClosedJet mode core) := by
  have coreLaw := (ambientAngular_exists 1 0 0 1 1 1 mode).choose_spec.1 (Finsupp.single 0 core)
  change ambientAngular mode (diskCore core) = _ at coreLaw
  rw [coreLaw]
  change apFiniteInto 1 0 0 1 (apFiniteJetMap (angularClosedJetLinear 1 mode) (Finsupp.single 0 core)) =
    apFiniteInto 1 0 0 1 (Finsupp.single 0 (angularClosedJet mode core))
  congr 1
  apply Finsupp.ext
  intro cell
  by_cases same : cell = 0
  · subst cell
    simp [apFiniteJetMap_apply]
    rfl
  · simp [apFiniteJetMap_apply, Finsupp.single_eq_of_ne same]

private theorem ambientAngular_mem (mode : ℤ) (field : diskGrade) :
    ambientAngular mode field.val ∈ diskGrade := by
  apply isClosed_property diskCoreInto_denseRange
    (diskCore.range.isClosed_topologicalClosure.preimage
      ((ambientAngular mode).continuous.comp diskGrade.subtypeL.continuous)) _ field
  intro core
  change ambientAngular mode (diskCore core) ∈ diskGrade
  rw [ambientAngular_core]
  exact Submodule.le_topologicalClosure _ ⟨angularClosedJet mode core, rfl⟩

/-- Completed angular projection on the actual full-disk H1 closure. -/
def diskAngularMode (mode : ℤ) : diskGrade →L[ℂ] diskGrade :=
  ((ambientAngular mode).comp diskGrade.subtypeL).codRestrict _ (ambientAngular_mem mode)

theorem diskAngularMode_core (mode : ℤ) (core : ClosedJet 1) :
    diskAngularMode mode (diskCoreInto core) = diskCoreInto (angularClosedJet mode core) :=
  Subtype.ext (ambientAngular_core mode core)

theorem diskAngularMode_bound (mode : ℤ) (field : diskGrade) :
    ‖diskAngularMode mode field‖ ≤ orthogonalGradeConstant 1 * ‖field‖ :=
  (ambientAngular_exists 1 0 0 1 1 1 mode).choose_spec.2 field.val

theorem diskBulk_core (field : ClosedJet 1) :
    diskBulk (diskCoreInto field) = closedL2Core field := by
  rw [diskBulk, diskCoordinate_core]
  change closedContinuousToDiskL2 (closedMultiDerivative field (0, 0)) = _
  rw [closedMultiDerivative_zero]
  rfl

theorem diskAngularMode_bulk (mode : ℤ) (field : diskGrade) :
    diskBulk (diskAngularMode mode field) = diskMode mode (diskBulk field) := by
  apply isClosed_property diskCoreInto_denseRange
    (isClosed_eq (diskBulk.continuous.comp (diskAngularMode mode).continuous)
      ((diskMode mode).continuous.comp diskBulk.continuous)) _ field
  intro core
  change diskBulk (diskAngularMode mode (diskCoreInto core)) = diskMode mode (diskBulk (diskCoreInto core))
  exact ((congrArg (fun value : diskGrade => diskBulk value) (diskAngularMode_core mode core)).trans
    (diskBulk_core (angularClosedJet mode core))).trans
    ((diskMode_core mode core).symm.trans (congrArg (diskMode mode) (diskBulk_core core).symm))

theorem diskAngularMode_projection (first second : ℤ) (field : diskGrade) :
    diskAngularMode first (diskAngularMode second field) =
      if first = second then diskAngularMode first field else 0 := by
  apply diskBulk_injective
  have equality := (diskAngularMode_bulk first (diskAngularMode second field)).trans
    ((congrArg (diskMode first) (diskAngularMode_bulk second field)).trans
      (diskMode_projection first second (diskBulk field)))
  refine equality.trans ?_
  split_ifs
  · exact (diskAngularMode_bulk first field).symm
  · exact (diskBulk.map_zero).symm

theorem diskAngularMode_commute (first second : ℤ) (field : diskGrade) :
    diskAngularMode first (diskAngularMode second field) =
      diskAngularMode second (diskAngularMode first field) := by
  by_cases equal : first = second
  · subst second
    rfl
  · exact ((diskAngularMode_projection first second field).trans (if_neg equal)).trans
      ((diskAngularMode_projection second first field).trans (if_neg (Ne.symm equal))).symm

end Grad.CircularHighWeak
