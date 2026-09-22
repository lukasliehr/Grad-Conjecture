import MultiplierSeries
import AveragesConsumer

noncomputable section

open scoped BigOperators

namespace Grad.Constraints.Multipliers

open Grad.ClosedJets Grad.CartesianState

theorem singleModeGradeCore_zero {sourceDimension targetDimension grade : ℕ}
    (parameters : PhaseParameters) (shift : ℤ)
    (field : GradeCore parameters sourceDimension grade) :
    singleModeGradeCore parameters shift
      (0 : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) field = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  simpa only [norm_zero, mul_zero, zero_mul] using singleModeGradeCore_norm_le parameters shift
    (0 : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) field

theorem singleModeCompleted_zero {sourceDimension targetDimension grade : ℕ}
    (parameters : PhaseParameters) (shift : ℤ) :
    singleModeCompleted (grade := grade) parameters shift
      (0 : ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension) = 0 := by
  apply denseCoreContinuousLinearMap_ext parameters
  intro field
  rw [singleModeCompleted_eta, singleModeGradeCore_zero, map_zero, zero_apply]

def finiteModeGradeCore {sourceDimension targetDimension grade : ℕ} (parameters : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (support : Finset ℤ) :
    GradeCore parameters sourceDimension grade →ₗ[ℂ] GradeCore parameters targetDimension grade :=
  ∑ shift ∈ support, singleModeGradeCore parameters shift (coefficients shift)

def coreCellLinear {dimension grade : ℕ} (parameters : PhaseParameters) (cell : ℤ) :
    GradeCore parameters dimension grade →ₗ[ℂ] ClosedJet dimension where
  toFun field := field.toCore.1 cell
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem finiteModeGradeCore_cell {sourceDimension targetDimension grade : ℕ} (parameters : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (support : Finset ℤ) (field : GradeCore parameters sourceDimension grade) (output : ℤ) :
    (finiteModeGradeCore parameters coefficients support field).toCore.1 output =
      ∑ shift ∈ support, valueMapJet (coefficients shift) (field.toCore.1 (output - shift)) := by
  change coreCellLinear parameters output
    ((∑ shift ∈ support, singleModeGradeCore parameters shift (coefficients shift)) field) = _
  rw [LinearMap.sum_apply, map_sum]
  rfl

theorem completedMultiplier_finite {sourceDimension targetDimension grade : ℕ} (parameters : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (support : Finset ℤ) (supported : ∀ shift, shift ∉ support → coefficients shift = 0)
    (field : GradeCore parameters sourceDimension grade) :
    completedMultiplier parameters coefficients (aGradeEta parameters field) =
      aGradeEta parameters (finiteModeGradeCore parameters coefficients support field) := by
  have finiteSum : completedMultiplier (grade := grade) parameters coefficients =
      ∑ shift ∈ support, singleModeCompleted parameters shift (coefficients shift) := by
    apply tsum_eq_sum
    intro shift outside
    rw [supported shift outside, singleModeCompleted_zero]
  rw [finiteSum, sum_apply]
  simp only [singleModeCompleted_eta]
  change (∑ shift ∈ support, aGradeEta parameters
    (singleModeGradeCore parameters shift (coefficients shift) field)) =
    aGradeEta parameters ((∑ shift ∈ support, singleModeGradeCore parameters shift (coefficients shift)) field)
  rw [LinearMap.sum_apply, map_sum]

theorem finite_envelope_summable {sourceDimension targetDimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (support : Finset ℤ) (supported : ∀ shift, shift ∉ support → coefficients shift = 0) :
    Summable (envelopeTerm parameters grade coefficients) := by
  apply summable_of_ne_finset_zero (s := support)
  intro shift outside
  simp only [envelopeTerm, supported shift outside, norm_zero, mul_zero]

/-- Immediate actual smooth-core consumer: finite Fourier multiplication
retains every closed derivative, its original same-grade bound and the zero
first-jet gauge. Arbitrary finite rectangular coefficient matrices are allowed. -/
theorem finite_multiplier_gauge_consumer {sourceDimension targetDimension grade : ℕ}
    (parameters : PhaseParameters)
    (coefficients : ℤ → ComplexEuclidean sourceDimension →L[ℂ] ComplexEuclidean targetDimension)
    (support : Finset ℤ) (supported : ∀ shift, shift ∉ support → coefficients shift = 0)
    (field : GradeCore parameters sourceDimension grade)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.toCore.1 cell)) :
    ‖finiteModeGradeCore parameters coefficients support field‖ ≤
        multiplierConstant grade parameters.gamma * envelope parameters grade coefficients * ‖field‖ ∧
      ∀ cell, ZeroCartesianFirstJets ((finiteModeGradeCore parameters coefficients support field).toCore.1 cell) := by
  constructor
  · have bound := completedMultiplier_bound parameters coefficients
      (finite_envelope_summable parameters grade coefficients support supported) (aGradeEta parameters field)
    rw [completedMultiplier_finite parameters coefficients support supported, aGradeEta_norm, aGradeEta_norm] at bound
    exact bound
  · intro cell order orderBound word
    let origin : ClosedDisk := ⟨0, by simp [closedUnitDisk]⟩
    rw [finiteModeGradeCore_cell]
    change (closedDerivativeLinear order word
      (∑ shift ∈ support, valueMapJet (coefficients shift) (field.toCore.1 (cell - shift)))) origin = 0
    rw [map_sum]
    change (ContinuousMap.evalCLM ℂ origin)
      (∑ shift ∈ support, closedDerivativeLinear order word
        (valueMapJet (coefficients shift) (field.toCore.1 (cell - shift)))) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro shift _
    change closedDerivative (valueMapJet (coefficients shift) (field.toCore.1 (cell - shift))) order word _ = 0
    rw [valueMapJet_derivative]
    change coefficients shift (closedDerivative (field.toCore.1 (cell - shift)) order word _) = 0
    rw [zeroJets (cell - shift) order orderBound word, map_zero]

end Grad.Constraints.Multipliers
