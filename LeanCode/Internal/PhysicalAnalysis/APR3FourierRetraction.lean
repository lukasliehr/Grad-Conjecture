import APR2CompletedOrdinaryDisk

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace Grad.OrdinaryDiskReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.CompatibleCompletion
open Grad.FourierGrade Grad.COR12Extension Grad.COR13Completion Grad.DiskExtension.Operator
attribute [local instance] ordinaryDiskNormedSpace

/-- Retraction to the actual ordinary H^q disk completion. Cell zero is the
zero Fourier coefficient in the cell circle, with no point evaluation there. -/
def fourierDisk (parameters : PhaseParameters) (grade : ℕ) :
    JGrade (ComplexEuclidean 1) grade →L[ℂ] unitDiskSobolev grade :=
  (originalDisk parameters grade).comp (completedRetraction parameters)

theorem fourierDisk_bound (parameters : PhaseParameters) (grade : ℕ)
    (values : JGrade (ComplexEuclidean 1) grade) :
    ‖fourierDisk parameters grade values‖ ≤ sameGradeConstant grade * ‖values‖ :=
  (originalDisk_bound parameters grade (completedRetraction parameters values)).trans
    (((completedRetraction parameters).le_opNorm values).trans
      (mul_le_mul_of_nonneg_right (completedRetraction_norm_le parameters) (norm_nonneg values)))

/-- Literal smooth Fourier core: reconstruct on the original physical torus,
restrict through the accepted P09 map and take its actual cell-zero jet. -/
theorem fourierDisk_core (parameters : PhaseParameters) (grade : ℕ)
    (values : JCore (ComplexEuclidean 1)) :
    fourierDisk parameters grade (coreToGrade grade values) =
      unitDiskCoreInto grade (diskCellFourierCoefficientJet
        (ordinaryExtensionRetraction.restriction 1 (reconstructedTorusSmoothField values)) 0) := by
  have phase : phaseZeroCore parameters grade (GradeCore.ofCoreLinear (weightedFourierRetraction parameters values)) =
      diskCellFourierCoefficientJet
        (ordinaryExtensionRetraction.restriction 1 (reconstructedTorusSmoothField values)) 0 := by
    change phaseWeightedJet parameters 0 (((weightedSmoothEquiv parameters).symm
      (ordinaryExtensionRetraction.restriction 1 (reconstructedTorusSmoothField values))).val 0) = _
    rw [weightedSmoothEquiv_symm_apply, phaseWeightedJet_inverse_left]
  exact (congrArg (originalDisk parameters grade) (completedRetraction_apply_core parameters values)).trans
    ((originalDisk_core parameters grade (GradeCore.ofCoreLinear (weightedFourierRetraction parameters values))).trans
      (congrArg (unitDiskCoreInto grade) phase))

theorem fourierDisk_bulk_coherent (parameters : PhaseParameters) (grade : ℕ)
    (values : JGrade (ComplexEuclidean 1) grade) :
    unitDiskBulk grade (fourierDisk parameters grade values) =
      unitDiskBulk 0 (fourierDisk parameters 0 (inclusion grade 0 (Nat.zero_le grade) values)) := by
  have natural := DFunLike.congr_fun (retraction_inclusion_naturality (dimension := 1)
    parameters (Nat.zero_le grade)) values
  exact (originalDisk_bulk_coherent parameters grade (completedRetraction parameters values)).trans
    (congrArg (fun value : AGrade parameters 1 0 => unitDiskBulk 0 (originalDisk parameters 0 value)) natural)

/-- The completed restriction recovers the same original grade-zero field
whenever its Fourier extension is the lowered higher-grade input. -/
theorem fourierDisk_reconstructs (parameters : PhaseParameters) (grade : ℕ)
    (values : JGrade (ComplexEuclidean 1) grade) (original : AGrade parameters 1 0)
    (same : inclusion grade 0 (Nat.zero_le grade) values = completedExtension parameters original) :
    unitDiskBulk grade (fourierDisk parameters grade values) =
      unitDiskBulk 0 (originalDisk parameters 0 original) :=
  (fourierDisk_bulk_coherent parameters grade values).trans
    ((congrArg (fun value : JGrade (ComplexEuclidean 1) 0 => unitDiskBulk 0 (fourierDisk parameters 0 value)) same).trans
      (congrArg (fun value : AGrade parameters 1 0 => unitDiskBulk 0 (originalDisk parameters 0 value))
        (completedRetraction_extension_apply parameters original)))

end Grad.OrdinaryDiskReconstruction
