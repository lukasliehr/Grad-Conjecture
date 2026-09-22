import RadialIntegralCore

noncomputable section

namespace Grad.NonlinearRadial

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct

def radialGradeCore {dimension grade : ℕ} (parameters : PhaseParameters) :
    GradeCore parameters dimension grade →ₗ[ℂ] GradeCore parameters dimension grade :=
  GradeCore.ofCoreLinear.comp ((radialCore parameters).comp GradeCore.toCoreLinear)

theorem radialGradeCore_bound {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension grade) :
    ‖radialGradeCore parameters field‖ ≤ dilationGradeConstant grade * ‖field‖ := by
  exact radialCore_bound parameters grade field.toCore

def radialCompleted {dimension grade : ℕ} (parameters : PhaseParameters) :
    AGrade parameters dimension grade →L[ℂ] AGrade parameters dimension grade :=
  denseCoreExtension parameters
    ((aGradeEta parameters).toLinearMap.comp (radialGradeCore parameters))
    (dilationGradeConstant grade) (fun field => by
      change ‖aGradeEta parameters (radialGradeCore parameters field)‖ ≤ _
      rw [aGradeEta_norm]
      exact radialGradeCore_bound parameters field)

theorem radialCompleted_eta {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) :
    radialCompleted (grade := grade) parameters (aGradeEta parameters (GradeCore.ofCoreLinear field)) =
      aGradeEta parameters (GradeCore.ofCoreLinear (radialCore parameters field)) :=
  denseCoreExtension_apply_eta parameters _ _ _ _

theorem radialCompleted_bound {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : AGrade parameters dimension grade) :
    ‖radialCompleted parameters field‖ ≤ dilationGradeConstant grade * ‖field‖ :=
  denseCoreExtension_apply_norm_le parameters _ _ _ field

theorem radialCompleted_unique {dimension grade : ℕ} (parameters : PhaseParameters)
    (other : AGrade parameters dimension grade →L[ℂ] AGrade parameters dimension grade)
    (coreLaw : ∀ field : ACore parameters dimension,
      other (aGradeEta parameters (GradeCore.ofCoreLinear field)) =
        aGradeEta parameters (GradeCore.ofCoreLinear (radialCore parameters field))) :
    other = radialCompleted parameters := by
  apply denseCoreContinuousLinearMap_ext parameters
  intro field
  exact (coreLaw field.toCore).trans (radialCompleted_eta parameters field.toCore).symm

theorem actual_radial_completed : RadialCompletedGoal := by
  refine ⟨dilationGradeConstant, dilationGradeConstant_nonnegative, ?_⟩
  intro parameters dimension
  refine ⟨radialCore parameters, radialCore_actual parameters, ?_⟩
  intro grade
  exact ⟨radialCompleted parameters, radialCompleted_eta parameters, radialCompleted_bound parameters⟩

theorem radialWeightedBlock : RadialWeightedBlockGoal :=
  ⟨actual_radial_core, actual_dilation, actual_radial_completed⟩

/-- Immediate consumer: the very same integral-defined coefficient map is
bounded in the original core and represented by the actual AGrade map. -/
theorem actual_radial_core_and_completion {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (grade : ℕ) :
    IsActualRadialIntegral field (radialCore parameters field) ∧
    originalGradeNorm grade (radialCore parameters field) ≤
      dilationGradeConstant grade * originalGradeNorm grade field ∧
    radialCompleted (grade := grade) parameters (aGradeEta parameters (GradeCore.ofCoreLinear field)) =
      aGradeEta parameters (GradeCore.ofCoreLinear (radialCore parameters field)) :=
  ⟨radialCore_actual parameters field, radialCore_bound parameters grade field, radialCompleted_eta parameters field⟩

end Grad.NonlinearRadial
