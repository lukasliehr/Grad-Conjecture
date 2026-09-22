import GaugeTraceCollapse

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers

theorem valueMapCore_smul_map {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (scalar : ℂ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ACore parameters sourceDimension) :
    valueMapCore (scalar • mapping) parameters field =
      scalar • valueMapCore mapping parameters field := by
  apply Subtype.ext
  funext cell
  exact valueMapJet_smul_map scalar mapping (field.1 cell)

theorem shiftCore_comp {dimension : ℕ} (parameters : PhaseParameters)
    (first second : ℤ) (field : ACore parameters dimension) :
    shiftCore parameters first (shiftCore parameters second field) =
      shiftCore parameters (first + second) field := by
  apply Subtype.ext
  funext cell
  change field.1 (cell - first - second) = field.1 (cell - (first + second))
  rw [sub_sub]

theorem shiftCore_valueMapCore {sourceDimension targetDimension : ℕ}
    (parameters : PhaseParameters) (shift : ℤ)
    (mapping : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (field : ACore parameters sourceDimension) :
    shiftCore parameters shift (valueMapCore mapping parameters field) =
      valueMapCore mapping parameters (shiftCore parameters shift field) := by
  apply Subtype.ext
  funext cell
  rfl

/-- Composition of two single completed modes is one completed mode at the sum
shift carrying the composed value operator. -/
theorem singleModeGradeCore_comp {grade : ℕ} (parameters : PhaseParameters)
    (firstShift secondShift : ℤ)
    (firstMapping secondMapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (field : GradeCore parameters 2 grade) :
    singleModeGradeCore parameters firstShift firstMapping
        (singleModeGradeCore parameters secondShift secondMapping field) =
      singleModeGradeCore (grade := grade) parameters (firstShift + secondShift)
        (firstMapping.comp secondMapping) field := by
  apply GradeCore.toCore_injective
  apply Subtype.ext
  funext cell
  change valueMapJet firstMapping
      (valueMapJet secondMapping (field.toCore.1 (cell - firstShift - secondShift))) =
    valueMapJet (firstMapping.comp secondMapping)
      (field.toCore.1 (cell - (firstShift + secondShift)))
  rw [valueMapJet_comp, sub_sub]

theorem singleModeCompleted_comp {grade : ℕ} (parameters : PhaseParameters)
    (firstShift secondShift : ℤ)
    (firstMapping secondMapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2) :
    (singleModeCompleted (grade := grade) parameters firstShift firstMapping).comp
        (singleModeCompleted parameters secondShift secondMapping) =
      singleModeCompleted parameters (firstShift + secondShift)
        (firstMapping.comp secondMapping) := by
  apply denseCoreContinuousLinearMap_ext parameters
  intro field
  rw [ContinuousLinearMap.comp_apply, singleModeCompleted_eta, singleModeCompleted_eta,
    singleModeCompleted_eta, singleModeGradeCore_comp]

theorem singleModeGradeCore_zero_id {grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters 2 grade) :
    singleModeGradeCore parameters 0 (ContinuousLinearMap.id ℂ (ComplexEuclidean 2)) field =
      field := by
  apply GradeCore.toCore_injective
  apply Subtype.ext
  funext cell
  change valueMapJet (ContinuousLinearMap.id ℂ (ComplexEuclidean 2))
      (field.toCore.1 (cell - 0)) = field.toCore.1 cell
  rw [valueMapJet_id, sub_zero]

theorem singleModeCompleted_zero_id {grade : ℕ} (parameters : PhaseParameters) :
    singleModeCompleted (grade := grade) parameters 0
        (ContinuousLinearMap.id ℂ (ComplexEuclidean 2)) =
      ContinuousLinearMap.id ℂ (AGrade parameters 2 grade) := by
  apply denseCoreContinuousLinearMap_ext parameters
  intro field
  rw [singleModeCompleted_eta, singleModeGradeCore_zero_id, ContinuousLinearMap.id_apply]

theorem singleModeGradeCore_add_map {grade : ℕ} (parameters : PhaseParameters)
    (shift : ℤ) (firstMapping secondMapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (field : GradeCore parameters 2 grade) :
    singleModeGradeCore parameters shift (firstMapping + secondMapping) field =
      singleModeGradeCore parameters shift firstMapping field +
        singleModeGradeCore (grade := grade) parameters shift secondMapping field := by
  apply GradeCore.toCore_injective
  apply Subtype.ext
  funext cell
  exact congrFun (congrArg Subtype.val (valueMapCore_add_map parameters firstMapping
    secondMapping (shiftCore parameters shift field.toCore))) cell

theorem singleModeGradeCore_smul_map {grade : ℕ} (parameters : PhaseParameters)
    (shift : ℤ) (scalar : ℂ)
    (mapping : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (field : GradeCore parameters 2 grade) :
    singleModeGradeCore parameters shift (scalar • mapping) field =
      scalar • singleModeGradeCore (grade := grade) parameters shift mapping field := by
  apply GradeCore.toCore_injective
  apply Subtype.ext
  funext cell
  exact congrFun (congrArg Subtype.val (valueMapCore_smul_map parameters scalar
    mapping (shiftCore parameters shift field.toCore))) cell

end Grad.Constraints.Gauges
