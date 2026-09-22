import COR14Inclusion

noncomputable section

namespace Grad.CompatibleCompletion

open Grad.ClosedJets Grad.CartesianState Grad.FourierGrade Grad.COR12Extension Grad.COR13Completion

/-- Dependent families in the actual original completions, compatible under
the constructed canonical inclusions at every ordered pair of grades. -/
def compatibleAGradesSubmodule (parameters : PhaseParameters) (dimension : ℕ) :
    Submodule ℂ (∀ grade : ℕ, AGrade parameters dimension grade) where
  carrier family := ∀ lower upper (ordered : lower ≤ upper),
    completedInclusion parameters ordered (family upper) = family lower
  zero_mem' := by
    intro lower upper ordered
    exact (completedInclusion (dimension := dimension) parameters ordered).map_zero
  add_mem' := by
    intro first second firstCompatible secondCompatible lower upper ordered
    change completedInclusion parameters ordered (first upper + second upper) = _
    rw [map_add, firstCompatible lower upper ordered, secondCompatible lower upper ordered]
    rfl
  smul_mem' := by
    intro scalar family compatible lower upper ordered
    change completedInclusion parameters ordered (scalar • family upper) = _
    rw [map_smul, compatible lower upper ordered]
    rfl

abbrev CompatibleAGrades (parameters : PhaseParameters) (dimension : ℕ) :=
  compatibleAGradesSubmodule parameters dimension

/-- Evaluation at one actual completed grade, with the inherited product topology. -/
def compatibleCoordinate {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ) :
    CompatibleAGrades parameters dimension →L[ℂ] AGrade parameters dimension grade :=
  (ContinuousLinearMap.proj grade).comp (compatibleAGradesSubmodule parameters dimension).subtypeL

/-- Embed one original smooth field into all its original completions simultaneously. -/
def coreToCompatible {dimension : ℕ} (parameters : PhaseParameters) :
    ACore parameters dimension →ₗ[ℂ] CompatibleAGrades parameters dimension where
  toFun field := ⟨fun grade => aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field), by
    intro lower upper ordered
    rw [completedInclusion_apply_eta]
    rfl⟩
  map_add' first second := by
    apply Subtype.ext
    funext grade
    exact map_add ((aGradeEta parameters).toLinearMap.comp GradeCore.ofCoreLinear) first second
  map_smul' scalar field := by
    apply Subtype.ext
    funext grade
    exact map_smul ((aGradeEta parameters).toLinearMap.comp GradeCore.ofCoreLinear) scalar field

theorem coreToCompatible_apply {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (grade : ℕ) :
    (coreToCompatible parameters field).1 grade =
      aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) field) := rfl

theorem compatible_fourier_coefficient {dimension : ℕ} (parameters : PhaseParameters)
    (family : CompatibleAGrades parameters dimension) (grade : ℕ) (mode : FourierMode) :
    coefficient grade (completedExtension parameters (family.1 grade)) mode =
      coefficient 0 (completedExtension parameters (family.1 0)) mode := by
  have natural := DFunLike.congr_fun
    (extension_inclusion_naturality parameters (Nat.zero_le grade)) (family.1 grade)
  simp only [ContinuousLinearMap.comp_apply, family.property 0 grade (Nat.zero_le grade)] at natural
  rw [natural, inclusion_coefficient]

/-- The single common coefficient sequence of a compatible family belongs
to every Fourier grade, not merely to a grade-dependent choice of representative. -/
def compatibleFourierCore {dimension : ℕ} (parameters : PhaseParameters) :
    CompatibleAGrades parameters dimension →ₗ[ℂ] JCore (ComplexEuclidean dimension) where
  toFun family := ⟨fun mode => coefficient 0 (completedExtension parameters (family.1 0)) mode, by
    intro grade
    have coordinateEquality : (fun mode => (frequencyWeight mode : ℂ) ^ grade •
        coefficient 0 (completedExtension parameters (family.1 0)) mode) =
        fun mode => completedExtension parameters (family.1 grade) mode := by
      funext mode
      rw [← compatible_fourier_coefficient parameters family grade mode, weighted_coefficient]
    rw [coordinateEquality]
    exact (completedExtension parameters (family.1 grade)).property⟩
  map_add' first second := by
    apply Subtype.ext
    funext mode
    change coefficient 0 (completedExtension parameters (first.1 0 + second.1 0)) mode = _
    simp only [map_add, coefficient, lp.coeFn_add, Pi.add_apply,
      smul_add]
    rfl
  map_smul' scalar family := by
    apply Subtype.ext
    funext mode
    change coefficient 0 (completedExtension parameters (scalar • family.1 0)) mode = _
    simp [map_smul, coefficient]

theorem compatibleFourierCore_grade {dimension : ℕ} (parameters : PhaseParameters)
    (family : CompatibleAGrades parameters dimension) (grade : ℕ) :
    coreToGrade grade (compatibleFourierCore parameters family) =
      completedExtension parameters (family.1 grade) := by
  apply ext_coefficients
  intro mode
  rw [coreToGrade_coefficient]
  exact (compatible_fourier_coefficient parameters family grade mode).symm

/-- Reconstruct through the actual COR12 inverse Fourier/P09 restriction/W inverse. -/
def compatibleToCore {dimension : ℕ} (parameters : PhaseParameters) :
    CompatibleAGrades parameters dimension →ₗ[ℂ] ACore parameters dimension :=
  (weightedFourierRetraction parameters).comp (compatibleFourierCore parameters)

theorem compatibleToCore_component {dimension : ℕ} (parameters : PhaseParameters)
    (family : CompatibleAGrades parameters dimension) (grade : ℕ) :
    aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade)
      (compatibleToCore parameters family)) = family.1 grade := by
  change aGradeEta parameters (GradeCore.ofCoreLinear
    (weightedFourierRetraction parameters (compatibleFourierCore parameters family))) = _
  rw [← completedRetraction_apply_core, compatibleFourierCore_grade,
    completedRetraction_extension_apply]

theorem compatibleToCore_toCompatible {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) :
    compatibleToCore parameters (coreToCompatible parameters field) = field := by
  have equalEta := compatibleToCore_component parameters (coreToCompatible parameters field) 0
  have equalTagged := aGradeEta_injective parameters equalEta
  exact congrArg GradeCore.toCore equalTagged

theorem coreToCompatible_toCore {dimension : ℕ} (parameters : PhaseParameters)
    (family : CompatibleAGrades parameters dimension) :
    coreToCompatible parameters (compatibleToCore parameters family) = family := by
  apply Subtype.ext
  funext grade
  exact compatibleToCore_component parameters family grade

/-- The actual original smooth core is linearly equivalent to the compatible
inverse limit of the genuine original norm completions. -/
def coreCompatibleEquiv {dimension : ℕ} (parameters : PhaseParameters) :
    ACore parameters dimension ≃ₗ[ℂ] CompatibleAGrades parameters dimension where
  toLinearMap := coreToCompatible parameters
  invFun := compatibleToCore parameters
  left_inv := compatibleToCore_toCompatible parameters
  right_inv := coreToCompatible_toCore parameters

theorem coreCompatibleEquiv_component_norm {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (grade : ℕ) :
    ‖(coreCompatibleEquiv parameters field).1 grade‖ =
      cartesianGradeSeminorm parameters (GradeCore.ofCoreLinear (grade := grade) field) :=
  aGradeEta_norm_eq_cartesianGradeSeminorm parameters _

end Grad.CompatibleCompletion
