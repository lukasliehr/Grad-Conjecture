import COR13Proof

noncomputable section

namespace Grad.COR13Completion.Consumer

open Grad.ClosedJets Grad.CartesianState Grad.FourierGrade Grad.COR12Extension

/-- The realization and its inverse control exactly the source completion
norm and the inherited Fourier subspace norm, in both directions. -/
theorem completedRealization_two_sided_norm {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : AGrade parameters dimension grade) :
    ‖completedRealizationEquiv parameters field‖ ≤ sameGradeConstant grade * ‖field‖ ∧
    ‖field‖ ≤ sameGradeConstant grade * ‖completedRealizationEquiv parameters field‖ := by
  constructor
  · exact (completedRealizationEquiv parameters).toContinuousLinearMap.le_of_opNorm_le
      (completedRealizationEquiv_norm_le parameters) field
  · have bound := (completedRealizationEquiv parameters).symm.toContinuousLinearMap.le_of_opNorm_le
      (completedRealizationEquiv_symm_norm_le parameters) (completedRealizationEquiv parameters field)
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using bound

/-- The closed realization restricts on the original core to Fourier of
the single extension of W_gamma h, not Fourier of the unweighted field. -/
theorem completedRealization_exact_core {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension grade) :
    (completedRealizationEquiv parameters (aGradeEta parameters field)).1 =
      coreToGrade grade (weightedFourierExtension parameters field.toCore) ∧
    ‖aGradeEta parameters field‖ = cartesianGradeSeminorm parameters field := by
  exact ⟨completedExtension_apply_eta parameters field,
    aGradeEta_norm_eq_cartesianGradeSeminorm parameters field⟩

/-- An actual complementary decomposition obtained from the proved
projection: its first summand lies in the closed realization and its second
is killed by the completed retraction. -/
theorem completedFourier_splitting {dimension grade : ℕ} (parameters : PhaseParameters)
    (values : JGrade (ComplexEuclidean dimension) grade) :
    realizationProjection parameters values ∈ fixedRealization parameters ∧
    completedRetraction parameters (values - realizationProjection parameters values) = 0 ∧
    values = realizationProjection parameters values +
      (values - realizationProjection parameters values) := by
  refine ⟨?_, ?_, ?_⟩
  · apply (mem_fixedRealization_iff parameters _).2
    exact DFunLike.congr_fun (realizationProjection_idempotent parameters) values
  · rw [map_sub, realizationProjection_apply, completedRetraction_extension_apply, sub_self]
  · abel

/-- No second completed forward map can have the same literal dense-core law. -/
theorem completedExtension_unique {dimension grade : ℕ} (parameters : PhaseParameters)
    (candidate : AGrade parameters dimension grade →L[ℂ] JGrade (ComplexEuclidean dimension) grade)
    (coreLaw : ∀ field : GradeCore parameters dimension grade,
      candidate (aGradeEta parameters field) =
        coreToGrade grade (weightedFourierExtension parameters field.toCore)) :
    candidate = completedExtension parameters := by
  apply denseCoreContinuousLinearMap_ext parameters
  intro field
  rw [coreLaw, completedExtension_apply_eta]

/-- The actual reverse extension is also determined by its dense Fourier-core law. -/
theorem completedRetraction_unique {dimension grade : ℕ} (parameters : PhaseParameters)
    (candidate : JGrade (ComplexEuclidean dimension) grade →L[ℂ] AGrade parameters dimension grade)
    (coreLaw : ∀ values : JCore (ComplexEuclidean dimension),
      candidate (coreToGrade grade values) = aGradeEta parameters
        (GradeCore.ofCoreLinear (weightedFourierRetraction parameters values))) :
    candidate = completedRetraction parameters := by
  apply DFunLike.ext
  have equalFunctions := (fourierCore_denseRange dimension grade).equalizer
    candidate.continuous (completedRetraction parameters).continuous (by
      funext values
      rw [Function.comp_apply, Function.comp_apply, coreLaw, completedRetraction_apply_core])
  exact congrFun equalFunctions

end Grad.COR13Completion.Consumer
