import AKAA4ActualFullCellKernel
import GC18APScalarJet

noncomputable section

set_option maxHeartbeats 1200000

open scoped BigOperators ContDiff

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Compensated
open Grad.AnalyticWeights.Higher Grad.GaugeCoefficients.Radial

/-- The phase conjugate of the SAME coherent completed coefficient. -/
def startupConjugatedCoefficientJet {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (input shift : ℤ) :
    SmoothOperatorJet inputDimension outputDimension :=
  smoothOperatorCompose
    (apScalarOperatorJet outputDimension (weightRatio sigma gamma ell (input + shift) input)
      (weightRatio_contDiff sigma gamma ell (input + shift) input))
    (actualCoefficientJet admissible family coherent shift)

theorem startupConjugatedCoefficientJet_value {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (input shift : ℤ) (point : ClosedDisk) :
    (startupConjugatedCoefficientJet admissible family coherent input shift).value point =
      (weightRatio sigma gamma ell (input + shift) input point.val : ℂ) •
        (actualCoefficientJet admissible family coherent shift).value point := by
  apply ContinuousLinearMap.ext
  intro vector
  change weightRatio sigma gamma ell (input + shift) input point.val •
    ((actualCoefficientJet admissible family coherent shift).value point vector) = _
  rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

theorem startupConjugatedCoefficientJet_derivative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (input shift : ℤ)
    (index : DerivativeIndex grade) (point : ClosedDisk) :
    smoothOperatorDerivative (startupConjugatedCoefficientJet admissible family coherent input shift)
      (derivativeMultiIndex index) point =
      ∑ split : DerivativeSplit index, (splitMultiplicity index split : ℂ) •
        ((apRatioDerivative sigma gamma ell (derivativeOrder (lowerDerivativeIndex index split))
          (cartesianMultiIndexWord (derivativeMultiIndex (lowerDerivativeIndex index split)))
          input shift point : ℂ) •
          coefficientDerivative (family grade) shift (upperDerivativeIndex index split) point) := by
  rw [startupConjugatedCoefficientJet, smoothOperatorCompose_derivative]
  change (∑ split : DerivativeSplit index, (splitMultiplicity index split : ℂ) •
    continuousOperatorComposition
      (smoothOperatorDerivative
        (apScalarOperatorJet outputDimension (weightRatio sigma gamma ell (input + shift) input)
          (weightRatio_contDiff sigma gamma ell (input + shift) input))
        (derivativeMultiIndex (lowerDerivativeIndex index split)))
      (smoothOperatorDerivative (actualCoefficientJet admissible family coherent shift)
        (derivativeMultiIndex (upperDerivativeIndex index split)))) point = _
  rw [continuousMap_sum_apply]
  apply Finset.sum_congr rfl
  intro split _
  change (splitMultiplicity index split : ℂ) • (_ : OperatorValue inputDimension outputDimension) = _
  congr 1
  apply ContinuousLinearMap.ext
  intro vector
  change (smoothOperatorDerivative
    (apScalarOperatorJet outputDimension (weightRatio sigma gamma ell (input + shift) input)
      (weightRatio_contDiff sigma gamma ell (input + shift) input))
    (derivativeMultiIndex (lowerDerivativeIndex index split)) point)
      (smoothOperatorDerivative (actualCoefficientJet admissible family coherent shift)
        (derivativeMultiIndex (upperDerivativeIndex index split)) point vector) = _
  rw [apScalarOperatorJet_derivative, actualCoefficientJet_coherent, smul_apply,
    ContinuousLinearMap.id_apply, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

end Grad.GaugeCoefficients.Physical.RadialLedger
