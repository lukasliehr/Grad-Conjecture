import APF2CompletedInsertion
import AIP3CompactExtension
import APR3FourierRetraction

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Grad.OrdinaryDiskForward
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.CompatibleCompletion
open Grad.Constraints
open Grad.OrdinaryDiskReconstruction Grad.InteriorPeriodization
open Grad.FourierGrade Grad.COR12Extension Grad.COR13Completion Grad.DiskExtension.Operator
attribute [local instance] ordinaryDiskNormedSpace

/-- The actual original Fourier extension of an ordinary disk H^q field,
with the unchanged inverse-phase normalized single-cell insertion. -/
def ordinaryFourier (parameters : PhaseParameters) (grade : ℕ) :
    unitDiskSobolev grade →L[ℂ] JGrade (ComplexEuclidean 1) grade :=
  (completedExtension parameters).comp (ordinaryInsertion parameters grade)

theorem ordinaryFourier_bound (parameters : PhaseParameters) (grade : ℕ) (field : unitDiskSobolev grade) :
    ‖ordinaryFourier parameters grade field‖ ≤ sameGradeConstant grade * ‖field‖ :=
  ((completedExtension parameters).le_opNorm (ordinaryInsertion parameters grade field)).trans
    ((mul_le_mul_of_nonneg_right (completedExtension_norm_le parameters) (norm_nonneg _)).trans_eq
      (congrArg (fun value : ℝ => sameGradeConstant grade * value) (ordinaryInsertion_norm parameters grade field)))

theorem ordinaryFourier_core (parameters : PhaseParameters) (grade : ℕ) (field : ClosedJet 1) :
    ordinaryFourier parameters grade (unitDiskCoreInto grade field) =
      coreToGrade grade (weightedFourierExtension parameters (normalizedSingleCore parameters field)) :=
  (congrArg (completedExtension parameters) (ordinaryInsertion_core parameters grade field)).trans
    (completedExtension_apply_eta parameters (normalizedGradeCore parameters grade field))

/-- Exact physical-torus core identity, with the phase explicitly cancelled
before the one accepted P09 extension of the constant cell field. -/
theorem ordinaryFourier_core_literal (parameters : PhaseParameters) (grade : ℕ) (field : ClosedJet 1) :
    ordinaryFourier parameters grade (unitDiskCoreInto grade field) =
      coreToGrade grade (torusSmoothFourierCore
        (ordinaryExtensionRetraction.extension 1 (constantDiskCellJet field))) := by
  have literal : weightedFourierExtension parameters (normalizedSingleCore parameters field) =
      torusSmoothFourierCore (ordinaryExtensionRetraction.extension 1 (constantDiskCellJet field)) := by
    change torusSmoothFourierCore (ordinaryExtensionRetraction.extension 1
      (weightedSmoothEquiv parameters (normalizedSingleCore parameters field))) = _
    rw [normalizedSingleCore_weighted]
  exact (ordinaryFourier_core parameters grade field).trans (congrArg (coreToGrade grade) literal)

/-- The all-grade Fourier map has exactly AIP's already-constructed
grade-zero Fourier realization of the same literal disk bulk. -/
theorem ordinaryFourier_zero_coherent (parameters : PhaseParameters) (grade : ℕ)
    (field : unitDiskSobolev grade) :
    inclusion grade 0 (Nat.zero_le grade) (ordinaryFourier parameters grade field) =
      diskFourier parameters (unitDiskBulk grade field) := by
  have natural := DFunLike.congr_fun (extension_inclusion_naturality (dimension := 1)
    parameters (Nat.zero_le grade)) (ordinaryInsertion parameters grade field)
  exact natural.symm.trans (congrArg (completedExtension parameters)
    (ordinaryInsertion_zero_coherent parameters grade field))

theorem fourierDisk_ordinaryFourier (parameters : PhaseParameters) (grade : ℕ)
    (field : unitDiskSobolev grade) :
    fourierDisk parameters grade (ordinaryFourier parameters grade field) = field :=
  (congrArg (originalDisk parameters grade)
    (completedRetraction_extension_apply parameters (ordinaryInsertion parameters grade field))).trans
      (originalDisk_insertion parameters grade field)

/-- Immediate all-grade source consumer for the accepted AIF gain-two map:
the input has the original norm, exact grade-zero field and exact retraction. -/
theorem actualFourierForward_consumer (parameters : PhaseParameters) (grade : ℕ)
    (field : unitDiskSobolev grade) :
    ∃ values : JGrade (ComplexEuclidean 1) grade,
      inclusion grade 0 (Nat.zero_le grade) values = diskFourier parameters (unitDiskBulk grade field) ∧
      fourierDisk parameters grade values = field ∧
      ‖values‖ ≤ sameGradeConstant grade * ‖field‖ :=
  ⟨ordinaryFourier parameters grade field, ordinaryFourier_zero_coherent parameters grade field,
    fourierDisk_ordinaryFourier parameters grade field, ordinaryFourier_bound parameters grade field⟩

end Grad.OrdinaryDiskForward
