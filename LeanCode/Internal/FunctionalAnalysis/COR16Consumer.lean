import COR16Proof

noncomputable section

namespace Grad.CompatibleCompletion.Consumer

open Grad.ClosedJets Grad.CartesianState Grad.FourierGrade Grad.COR12Extension Grad.COR13Completion

/-- Every compatible family is represented by exactly one actual smooth
original field at every completed grade simultaneously. -/
theorem unique_smooth_representative {dimension : ℕ} (parameters : PhaseParameters)
    (family : CompatibleAGrades parameters dimension) :
    ∃! field : ACore parameters dimension, ∀ grade : ℕ,
      aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field) = family.1 grade := by
  refine ⟨compatibleToCore parameters family, compatibleToCore_component parameters family, ?_⟩
  intro field representation
  have equality : aGradeEta parameters (GradeCore.ofCoreLinear (grade := 0) field) =
      aGradeEta parameters (GradeCore.ofCoreLinear (grade := 0) (compatibleToCore parameters family)) :=
    (representation 0).trans (compatibleToCore_component parameters family 0).symm
  exact congrArg GradeCore.toCore (aGradeEta_injective parameters equality)

/-- Reconstruction has exactly each prescribed original component norm. -/
theorem reconstructed_original_norm {dimension : ℕ} (parameters : PhaseParameters)
    (family : CompatibleAGrades parameters dimension) (grade : ℕ) :
    cartesianGradeSeminorm parameters (GradeCore.ofCoreLinear (grade := grade)
      (compatibleToCore parameters family)) = ‖family.1 grade‖ := by
  rw [← aGradeEta_norm_eq_cartesianGradeSeminorm, compatibleToCore_component]

/-- The same reconstructed smooth field works in a chosen pair of grades;
their contraction retains the literal lower and upper original norms. -/
theorem compatible_component_norm_mono {dimension lower upper : ℕ}
    (parameters : PhaseParameters) (family : CompatibleAGrades parameters dimension)
    (ordered : lower ≤ upper) : ‖family.1 lower‖ ≤ ‖family.1 upper‖ := by
  rw [← family.property lower upper ordered]
  simpa only [one_mul] using (completedInclusion parameters ordered).le_of_opNorm_le
    (completedInclusion_norm_le_one parameters ordered) (family.1 upper)

/-- There is one common all-grade Fourier coefficient sequence, so the
reconstructed field is not a family of grade-dependent representatives. -/
theorem common_fourier_reconstruction {dimension : ℕ} (parameters : PhaseParameters)
    (family : CompatibleAGrades parameters dimension) :
    (∀ grade : ℕ, coreToGrade grade (compatibleFourierCore parameters family) =
      completedExtension parameters (family.1 grade)) ∧
    compatibleToCore parameters family =
      weightedFourierRetraction parameters (compatibleFourierCore parameters family) :=
  ⟨compatibleFourierCore_grade parameters family, rfl⟩

end Grad.CompatibleCompletion.Consumer
