import GC18APScalarJet
import GC18APAllocation

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.AnalyticWeights.Higher Grad.AnalyticWeights.Calculus

theorem apRatio_weight_cancel (sigma gamma ell : ℝ) (input shift : ℤ) (point : SpatialPlane) :
    weightRatio sigma gamma ell (input + shift) input point * originalWeight sigma gamma ell input point =
      originalWeight sigma gamma ell (input + shift) point := by
  have nonzero : physicalWeight sigma gamma ell input point ≠ 0 := by
    rw [physicalWeight_exp]
    exact (Real.exp_pos _).ne'
  unfold weightRatio originalWeight inverseWeight
  rw [mul_assoc, inv_mul_cancel₀ nonzero, mul_one]

theorem apWeightedProduct_eq {inputDimension outputDimension : ℕ} (sigma gamma ell : ℝ)
    (input shift : ℤ) (coefficient : SmoothOperatorJet inputDimension outputDimension) (field : ClosedJet inputDimension) :
    apWeightedJet sigma gamma ell (input + shift) (apProductJet coefficient field) =
      smoothScalarWeightedJet (weightRatio sigma gamma ell (input + shift) input)
        (weightRatio_contDiff sigma gamma ell (input + shift) input)
        (apProductJet coefficient (apWeightedJet sigma gamma ell input field)) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [apWeightedJet_value, apProductJet_value]
  change originalWeight sigma gamma ell (input + shift) point.val • coefficient.value point (field.value point) =
    weightRatio sigma gamma ell (input + shift) input point.val •
      (apProductJet coefficient (apWeightedJet sigma gamma ell input field)).value point
  rw [apProductJet_value, apWeightedJet_value]
  have scalarLaw := ((coefficient.value point).restrictScalars ℝ).map_smul
    (originalWeight sigma gamma ell input point.val) (field.value point)
  change coefficient.value point (originalWeight sigma gamma ell input point.val • field.value point) =
    originalWeight sigma gamma ell input point.val • coefficient.value point (field.value point) at scalarLaw
  rw [scalarLaw, smul_smul, apRatio_weight_cancel]

def apRawAllocationTerm {inputDimension outputDimension grade : ℕ} (sigma gamma ell : ℝ)
    (input shift : ℤ) (coefficient : SmoothOperatorJet inputDimension outputDimension) (field : ClosedJet inputDimension)
    (allocation : APAllocation grade) (point : ClosedDisk) : ComplexEuclidean outputDimension :=
  (apMultiplicity allocation : ℂ) •
    ((apRatioDerivative sigma gamma ell (derivativeOrder (apPhaseIndex allocation)) (apPhaseWord allocation)
      input shift point : ℂ) •
      (smoothOperatorDerivative coefficient (derivativeMultiIndex (apCoefficientIndex allocation)) point)
        (closedMultiDerivative (apWeightedJet sigma gamma ell input field) (derivativeMultiIndex (apInputIndex allocation)) point))

/-- Exact AP23 on every closed-disk point, including the axis. This is the
literal differentiated field product, not an abstract multiplier premise. -/
theorem apWeightedProduct_derivative {inputDimension outputDimension grade : ℕ} (sigma gamma ell : ℝ)
    (input shift : ℤ) (coefficient : SmoothOperatorJet inputDimension outputDimension) (field : ClosedJet inputDimension)
    (index : DerivativeIndex grade) (point : ClosedDisk) :
    closedMultiDerivative (apWeightedJet sigma gamma ell (input + shift) (apProductJet coefficient field))
      (derivativeMultiIndex index) point =
      ∑ firstSplit : DerivativeSplit index,
        ∑ secondSplit : DerivativeSplit (upperDerivativeIndex index firstSplit),
          apRawAllocationTerm sigma gamma ell input shift coefficient field ⟨index, firstSplit, secondSplit⟩ point := by
  rw [apWeightedProduct_eq, apScalarWeightedJet_derivative]
  apply Finset.sum_congr rfl
  intro firstSplit _
  rw [apProductJet_derivative, Finset.smul_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro secondSplit _
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  dsimp only [apRawAllocationTerm, apMultiplicity, apPhaseIndex, apCoefficientIndex, apInputIndex,
    apPhaseWord, apRatioDerivative, ContinuousMap.coe_mk]
  rw [Nat.cast_mul]
  simp only [smul_smul]
  congr 1
  have reorder (a b c : ℂ) : a * (b * c) = a * c * b := by ring
  exact reorder _ _ _

end Grad.GaugeCoefficients.Physical.RadialLedger
