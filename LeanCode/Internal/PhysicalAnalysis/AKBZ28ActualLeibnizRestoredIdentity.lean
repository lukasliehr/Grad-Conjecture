import AKBZ27AllPositiveAllocationsPayment

noncomputable section
set_option maxHeartbeats 1300000
open scoped BigOperators
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation
open Grad.CartesianState Grad.NonlinearProduct Grad.GenericCarriers

def phaseSplitOrder {grade : ℕ} (index : DerivativeIndex grade) (split : DerivativeSplit index) : ℕ :=
  derivativeOrder (lowerDerivativeIndex index split)

def rawSplitIndex {grade : ℕ} (index : DerivativeIndex grade) (split : DerivativeSplit index) : CartesianMultiIndex :=
  derivativeMultiIndex (upperDerivativeIndex index split)

def phaseSplitWord {grade : ℕ} (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    CartesianWord (phaseSplitOrder index split) :=
  cartesianMultiIndexWord (derivativeMultiIndex (lowerDerivativeIndex index split))

theorem phaseSplit_total {grade : ℕ} (index : DerivativeIndex grade) (split : DerivativeSplit index) :
    phaseSplitOrder index split+cartesianOrder (rawSplitIndex index split)=derivativeOrder index :=
  derivative_split_order index split

/-- Every term is the literal same coefficient family, at its exact total
allocated grade, with the accepted input normalization left visible. -/
def originalLeibnizCoefficient {L sigma gamma ell : ℝ} {inputDimension outputDimension grade : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (index : DerivativeIndex grade) (split : DerivativeSplit index) (input shift : ℤ) :
    C(ClosedDisk,OperatorValue inputDimension outputDimension) :=
  startupAllocatedCoefficient
    (family (cartesianOrder (rawSplitIndex index split)+phaseSplitOrder index split))
    (phaseSplitOrder index split) (phaseSplitWord index split)
    (sharpCoefficientIndex (rawSplitIndex index split) (phaseSplitOrder index split)) input shift

/-- Exact full original conjugated coefficient derivative, including phase
rank zero. This identifies all finite Leibniz terms before any norm bound. -/
theorem originalDerivativeCoefficient_restored {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension grade : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade) (input shift : ℤ) :
    ((scaledCellWeight L ell input^(derivativeOrder index-1):ℝ):ℂ) •
      startupDerivativeCoefficient admissible family coherent index input shift=
    ∑ split : DerivativeSplit index,(splitMultiplicity index split:ℂ) •
      (((scaledCellWeight L ell input^(phaseSplitOrder index split-1):ℝ):ℂ) •
        originalLeibnizCoefficient family index split input shift) := by
  have positive : 0<scaledCellWeight L ell input^(derivativeOrder index-1) :=
    pow_pos (zero_lt_one.trans_le (scaledCellWeight_one_le L ell input)) _
  have nonzero : ((scaledCellWeight L ell input^(derivativeOrder index-1):ℝ):ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr positive.ne'
  apply ContinuousMap.ext
  intro point
  simp only [ContinuousMap.smul_apply,ContinuousMap.sum_apply,startupDerivativeCoefficient,smul_smul,mul_inv_cancel₀ nonzero,one_smul]
  rw [startupConjugatedCoefficientJet_derivative]
  apply Finset.sum_congr rfl
  intro split membership
  rw [←smul_smul]
  change (splitMultiplicity index split:ℂ) • _=(splitMultiplicity index split:ℂ) •
    (((scaledCellWeight L ell input^(phaseSplitOrder index split-1):ℝ):ℂ) •
      startupAllocatedCoefficient
        (family (cartesianOrder (rawSplitIndex index split)+phaseSplitOrder index split))
        (phaseSplitOrder index split) (phaseSplitWord index split)
        (sharpCoefficientIndex (rawSplitIndex index split) (phaseSplitOrder index split)) input shift point)
  rw [←startupAllocatedCoefficient_unreserve]
  rw [coherent_derivative_raw family coherent,coherent_derivative_raw family coherent]
  rfl

theorem originalDerivativeOperator_restored {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension grade : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (index : DerivativeIndex grade) (input shift : ℤ)
    (field : DiskL2 inputDimension) :
    closedOperatorL2 (startupDerivativeCoefficient admissible family coherent index input shift)
      (((scaledCellWeight L ell input^(derivativeOrder index-1):ℝ):ℂ) • field)=
    ∑ split : DerivativeSplit index,(splitMultiplicity index split:ℂ) •
      closedOperatorL2 (originalLeibnizCoefficient family index split input shift)
        (((scaledCellWeight L ell input^(phaseSplitOrder index split-1):ℝ):ℂ) • field) := by
  have same := congrArg (fun coefficient : C(ClosedDisk,OperatorValue inputDimension outputDimension) =>
    closedOperatorAction inputDimension outputDimension coefficient field)
    (originalDerivativeCoefficient_restored admissible family coherent index input shift)
  simp only [map_smul,_root_.map_sum,_root_.smul_apply,_root_.sum_apply] at same
  have applied (coefficient : C(ClosedDisk,OperatorValue inputDimension outputDimension)) :
      closedOperatorAction inputDimension outputDimension coefficient=closedOperatorL2 coefficient := rfl
  simp_rw [applied] at same
  simpa only [map_smul] using same

end Grad.OriginalCartesianTameEstimate
