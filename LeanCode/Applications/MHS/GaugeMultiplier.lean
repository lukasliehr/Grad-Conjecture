import SeedConsumer
import COR16Consumer

noncomputable section

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.CompatibleCompletion
open Grad.Constraints.Multipliers

theorem completedModes_summable {sourceDimension targetDimension grade : ℕ}
    (phase : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (summable : Summable (envelopeTerm phase grade coefficients)) :
    Summable (fun shift => singleModeCompleted (grade := grade) phase shift (coefficients shift)) :=
  Summable.of_norm (f := fun shift => singleModeCompleted (grade := grade) phase shift (coefficients shift))
    (singleModeCompleted_norm_summable (grade := grade) phase coefficients summable)

theorem singleMode_inclusion {sourceDimension targetDimension lower upper : ℕ}
    (phase : PhaseParameters) (ordered : lower ≤ upper) (shift : ℤ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) :
    (completedInclusion phase ordered).comp (singleModeCompleted phase shift mapping) =
      (singleModeCompleted phase shift mapping).comp (completedInclusion phase ordered) := by
  apply denseCoreContinuousLinearMap_ext phase
  intro field
  simp only [ContinuousLinearMap.comp_apply, singleModeCompleted_eta,
    completedInclusion_apply_eta]
  rfl

theorem multiplier_inclusion {sourceDimension targetDimension lower upper : ℕ}
    (phase : PhaseParameters) (ordered : lower ≤ upper)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (lowerSummable : Summable (envelopeTerm phase lower coefficients))
    (upperSummable : Summable (envelopeTerm phase upper coefficients))
    (field : AGrade phase sourceDimension upper) :
    completedInclusion phase ordered (completedMultiplier phase coefficients field) =
      completedMultiplier phase coefficients (completedInclusion phase ordered field) := by
  let upperModes : ℤ → AGrade phase sourceDimension upper →L[ℂ] AGrade phase targetDimension upper :=
    fun shift => singleModeCompleted phase shift (coefficients shift)
  let lowerModes : ℤ → AGrade phase sourceDimension lower →L[ℂ] AGrade phase targetDimension lower :=
    fun shift => singleModeCompleted phase shift (coefficients shift)
  have upperSeries : Summable upperModes :=
    completedModes_summable (grade := upper) phase coefficients upperSummable
  have lowerSeries : Summable lowerModes :=
    completedModes_summable (grade := lower) phase coefficients lowerSummable
  have upperSum := (ContinuousLinearMap.apply ℂ (AGrade phase targetDimension upper) field).hasSum upperSeries.hasSum
  have lowerSum := (ContinuousLinearMap.apply ℂ (AGrade phase targetDimension lower)
    (completedInclusion phase ordered field)).hasSum lowerSeries.hasSum
  have includedSum := (completedInclusion (dimension := targetDimension) phase ordered).hasSum upperSum
  change HasSum (fun shift => completedInclusion phase ordered
    (singleModeCompleted phase shift (coefficients shift) field)) _ at includedSum
  have equality (shift : ℤ) := DFunLike.congr_fun
    (singleMode_inclusion phase ordered shift (coefficients shift)) field
  simp only [ContinuousLinearMap.comp_apply] at equality
  simp only [equality] at includedSum
  exact includedSum.unique lowerSum

/-- One compatible family, not unrelated grade-dependent smooth representatives. -/
def multipliedCompatible {sourceDimension targetDimension : ℕ}
    (phase : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (summable : ∀ grade, Summable (envelopeTerm phase grade coefficients)) :
    ACore phase sourceDimension →ₗ[ℂ] CompatibleAGrades phase targetDimension where
  toFun field := ⟨fun grade => completedMultiplier phase coefficients
    (aGradeEta phase (GradeCore.ofCoreLinear (grade := grade) field)), by
      intro lower upper ordered
      rw [multiplier_inclusion phase ordered coefficients (summable lower) (summable upper),
        completedInclusion_apply_eta]
      rfl⟩
  map_add' first second := by
    apply Subtype.ext
    funext grade
    exact map_add ((completedMultiplier phase coefficients).toLinearMap.comp
      ((aGradeEta phase).toLinearMap.comp (GradeCore.ofCoreLinear (grade := grade)))) first second
  map_smul' scalar field := by
    apply Subtype.ext
    funext grade
    exact map_smul ((completedMultiplier phase coefficients).toLinearMap.comp
      ((aGradeEta phase).toLinearMap.comp (GradeCore.ofCoreLinear (grade := grade)))) scalar field

def smoothMultiplier {sourceDimension targetDimension : ℕ}
    (phase : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (summable : ∀ grade, Summable (envelopeTerm phase grade coefficients)) :
    ACore phase sourceDimension →ₗ[ℂ] ACore phase targetDimension :=
  (compatibleToCore phase).comp (multipliedCompatible phase coefficients summable)

theorem smoothMultiplier_eta {sourceDimension targetDimension : ℕ}
    (phase : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (summable : ∀ grade, Summable (envelopeTerm phase grade coefficients))
    (field : ACore phase sourceDimension) (grade : ℕ) :
    aGradeEta phase (GradeCore.ofCoreLinear (grade := grade)
      (smoothMultiplier phase coefficients summable field)) =
      completedMultiplier phase coefficients (aGradeEta phase (GradeCore.ofCoreLinear field)) :=
  compatibleToCore_component phase (multipliedCompatible phase coefficients summable field) grade

theorem smoothMultiplier_bound {sourceDimension targetDimension : ℕ}
    (phase : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (summable : ∀ grade, Summable (envelopeTerm phase grade coefficients))
    (field : ACore phase sourceDimension) (grade : ℕ) :
    ‖GradeCore.ofCoreLinear (grade := grade) (smoothMultiplier phase coefficients summable field)‖ ≤
      multiplierConstant grade phase.gamma * envelope phase grade coefficients *
        ‖GradeCore.ofCoreLinear (grade := grade) field‖ := by
  rw [← aGradeEta_norm phase, smoothMultiplier_eta]
  simpa only [aGradeEta_norm] using completedMultiplier_bound phase coefficients
    (summable grade) (aGradeEta phase (GradeCore.ofCoreLinear (grade := grade) field))

theorem smoothMultiplier_rows {sourceDimension targetDimension : ℕ}
    (phase : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (summable : ∀ grade, Summable (envelopeTerm phase grade coefficients))
    (field : ACore phase sourceDimension) (grade : ℕ) (output : ℤ) :
    HasSum (multiplierRow phase coefficients (GradeCore.ofCoreLinear (grade := grade) field) output)
      (completedCoordinates phase
        (aGradeEta phase (GradeCore.ofCoreLinear (grade := grade)
          (smoothMultiplier phase coefficients summable field))) output) := by
  rw [smoothMultiplier_eta]
  exact completedMultiplier_rows phase coefficients (summable grade) _ output

end Grad.Constraints.Gauges
