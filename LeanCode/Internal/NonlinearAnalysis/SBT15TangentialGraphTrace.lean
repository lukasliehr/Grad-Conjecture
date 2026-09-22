import SBT14PolarEndpointFormula

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceBoundaryTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.SourceCollarAngular Grad.BoundaryTrace Grad.Constraints.Gauges

def polarEndpointCombination (power : ℕ) (mode : ℤ × ℤ)
    (endpoint : ℤ × ℤ → ComplexEuclidean 2) : ComplexEuclidean 1 :=
  planarComponentMap 1 ((2 : ℂ)⁻¹ •
    (annularShiftScalar power 1 mode • endpoint (mode.1 - 1, mode.2) +
      annularShiftScalar power (-1) mode • endpoint (mode.1 + 1, mode.2))) -
  planarComponentMap 0 ((2 * Complex.I : ℂ)⁻¹ •
    (annularShiftScalar power 1 mode • endpoint (mode.1 - 1, mode.2) -
      annularShiftScalar power (-1) mode • endpoint (mode.1 + 1, mode.2)))

theorem annularTangentialContraction_endpoint (lower : ℝ) (positive : 0 < lower) (power : ℕ)
    (field : annularDerivativeGraph 2 lower positive 1)
    (endpoint : ℤ × ℤ → ComplexEuclidean 2)
    (traceLaw : ∀ mode, ((field.val 0 mode, field.val 1 mode), endpoint mode) ∈ radialEndpointGraph 2 lower)
    (mode : ℤ × ℤ) :
    (((annularTangentialContraction lower positive power field).val 0 mode,
      (annularTangentialContraction lower positive power field).val 1 mode),
      polarEndpointCombination power mode endpoint) ∈ radialEndpointGraph 1 lower := by
  have first := radialEndpointGraph_complex_smul lower (annularShiftScalar power 1 mode) _
    (traceLaw (mode.1 - 1, mode.2))
  have second := radialEndpointGraph_complex_smul lower (annularShiftScalar power (-1) mode) _
    (traceLaw (mode.1 + 1, mode.2))
  have cosine := radialEndpointGraph_complex_smul lower ((2 : ℂ)⁻¹) _
    ((radialEndpointGraph 2 lower).add_mem first second)
  have sine := radialEndpointGraph_complex_smul lower ((2 * Complex.I : ℂ)⁻¹) _
    ((radialEndpointGraph 2 lower).sub_mem first second)
  have combined := (radialEndpointGraph 1 lower).sub_mem
    (radialEndpointGraph_valueMap lower (planarComponentMap 1) _ cosine)
    (radialEndpointGraph_valueMap lower (planarComponentMap 0) _ sine)
  change (((annularTangentialContraction lower positive power field).val 0 mode,
    (annularTangentialContraction lower positive power field).val 1 mode),
    polarEndpointCombination power mode endpoint) ∈ radialEndpointGraph 1 lower at combined
  exact combined

theorem polarEndpointCombination_core (parameters : PhaseParameters) (power : ℕ)
    (field : ACore parameters 2) (mode : ℤ × ℤ) :
    polarEndpointCombination power mode (fun next =>
      (sourceBoundaryWeight parameters power next : ℂ) • originalBoundaryCoefficient parameters field next) =
      (sourceBoundaryWeight parameters power mode : ℂ) •
        originalBoundaryCoefficient parameters (tangentialBoundaryCore parameters field) mode := by
  have first := annularShiftScalar_boundaryWeight parameters power 1 mode
  have second := annularShiftScalar_boundaryWeight parameters power (-1) mode
  simp only [sub_neg_eq_add] at second
  rw [polarEndpointCombination, smul_smul, first, smul_smul, second,
    tangentialBoundaryCoefficient_formula]
  simp only [smul_add, smul_sub, map_add, map_sub, map_smul, smul_smul]
  module

theorem polarEndpointCombination_continuous (power : ℕ) (mode : ℤ × ℤ) :
    Continuous (fun field : SourceBoundary 2 => polarEndpointCombination power mode field) := by
  have first := (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 2) 2 (mode.1 - 1, mode.2)).continuous
  have second := (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 2) 2 (mode.1 + 1, mode.2)).continuous
  have plus := first.const_smul (annularShiftScalar power 1 mode)
  have minus := second.const_smul (annularShiftScalar power (-1) mode)
  exact ((planarComponentMap 1).continuous.comp ((plus.add minus).const_smul ((2 : ℂ)⁻¹))).sub
    ((planarComponentMap 0).continuous.comp ((plus.sub minus).const_smul ((2 * Complex.I : ℂ)⁻¹)))

theorem polarEndpointCombination_completed (parameters : PhaseParameters) (power : ℕ)
    (field : AGrade parameters 2 (power + 1)) (mode : ℤ × ℤ) :
    polarEndpointCombination power mode (integerSourceTrace parameters power field) =
      integerSourceTrace parameters power (tangentialBoundaryCompleted parameters (power + 1) field) mode := by
  have first := (polarEndpointCombination_continuous power mode).comp (integerSourceTrace parameters power).continuous
  have second := ((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode).continuous).comp
    ((integerSourceTrace parameters power).continuous.comp
      (tangentialBoundaryCompleted parameters (power + 1)).continuous)
  refine UniformSpace.Completion.induction_on field (isClosed_eq first second) ?_
  intro core
  change polarEndpointCombination power mode (integerSourceTrace parameters power (aGradeEta parameters core)) =
    integerSourceTrace parameters power
      (tangentialBoundaryCompleted parameters (power + 1) (aGradeEta parameters core)) mode
  rw [tangentialBoundaryCompleted_core]
  have endpoints : (fun next => integerSourceTrace parameters power (aGradeEta parameters core) next) =
      (fun next => (sourceBoundaryWeight parameters power next : ℂ) • originalBoundaryCoefficient parameters core.toCore next) := by
    funext next
    rw [← sourceBoundary_weighted parameters power, integerSourceTrace_core]
  change polarEndpointCombination power mode
    (fun next => integerSourceTrace parameters power (aGradeEta parameters core) next) = _
  rw [endpoints, ← sourceBoundary_weighted parameters power, integerSourceTrace_core,
    GradeCore.toCore_ofCore]
  exact polarEndpointCombination_core parameters power core.toCore mode

/-- The bounded original boundary operator is the unique actual endpoint
of the completed polar F0 derivative graph, not just a matching label. -/
theorem completedTangentialContraction_endpoint (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (parameters : PhaseParameters) (power : ℕ)
    (field : AGrade parameters 2 (power + 1)) (mode : ℤ × ℤ) :
    (((completedTangentialContraction lower positive bounded parameters power 1 field).val 0 mode,
      (completedTangentialContraction lower positive bounded parameters power 1 field).val 1 mode),
      integerSourceTrace parameters power (tangentialBoundaryCompleted parameters (power + 1) field) mode) ∈
      radialEndpointGraph 1 lower := by
  have actual := annularTangentialContraction_endpoint lower positive power
    (completedRestriction lower positive bounded parameters power 1 field)
    (integerSourceTrace parameters power field)
    (completedRestriction_endpoint lower positive bounded parameters power field) mode
  rwa [polarEndpointCombination_completed] at actual

end Grad.SourceBoundaryTrace
