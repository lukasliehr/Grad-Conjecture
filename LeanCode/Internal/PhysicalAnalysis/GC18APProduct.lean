import GC18APSpace
import GC18JetBridge

noncomputable section

set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.Ledger

theorem operatorJetColumn_multi {input output : ℕ} (coefficient : SmoothOperatorJet input output)
    (column : PhysicalValue input) (index : CartesianMultiIndex) (point : ClosedDisk) :
    closedMultiDerivative (operatorJetColumn coefficient column) index point =
      smoothOperatorDerivative coefficient index point column := by
  let candidate : C(ClosedDisk, PhysicalValue output) :=
    ⟨fun point => smoothOperatorDerivative coefficient index point column,
      (ContinuousLinearMap.apply ℂ (PhysicalValue output) column).continuous.comp
        (smoothOperatorDerivative coefficient index).continuous⟩
  suffices identity : closedMultiDerivative (operatorJetColumn coefficient column) index = candidate from
    congrArg (fun mapping : C(ClosedDisk, PhysicalValue output) => mapping point) identity
  apply continuousMap_eq_of_openDisk
  intro point inside
  rw [closedMultiDerivative, closedDerivative_spec _ _ _ point inside]
  change iteratedFDeriv ℝ (cartesianOrder index)
    (closedDiskLift (operatorJetColumnValue coefficient column)) point.val
      (fun position => spatialBasis (cartesianMultiIndexWord index position)) = _
  rw [closedDiskLift_operatorJetColumnValue]
  change iteratedFDeriv ℝ (cartesianOrder index)
    (((ContinuousLinearMap.apply ℂ (PhysicalValue output) column).restrictScalars ℝ) ∘ closedDiskLift coefficient.value)
      point.val (fun position => spatialBasis (cartesianMultiIndexWord index position)) = _
  rw [((ContinuousLinearMap.apply ℂ (PhysicalValue output) column).restrictScalars ℝ).iteratedFDeriv_comp_left
    (coefficient.smoothInterior.contDiffAt (openUnitDisk_isOpen.mem_nhds inside))
    (by exact_mod_cast (le_top : (cartesianOrder index : ℕ∞) ≤ ⊤))]
  exact congrArg (fun mapping : OperatorValue input output => mapping column)
    ((Classical.choose_spec (coefficient.derivativeExists index)) point inside).symm

/-- The literal product of a smooth operator coefficient and a genuine
closed data jet, constructed with all Cartesian derivative extensions. -/
def apProductJet {input output : ℕ} (coefficient : SmoothOperatorJet input output)
    (field : ClosedJet input) : ClosedJet output :=
  operatorJetColumn (smoothOperatorCompose coefficient
    (mappedSmoothOperatorJet (columnEmbedding 1 input 0) field)) (operatorBasis 0)

theorem apProductJet_value {input output : ℕ} (coefficient : SmoothOperatorJet input output)
    (field : ClosedJet input) (point : ClosedDisk) :
    (apProductJet coefficient field).value point = coefficient.value point (field.value point) := by
  change coefficient.value point ((columnEmbedding 1 input 0) (field.value point) (operatorBasis 0)) = _
  rw [columnEmbedding_apply]
  simp [operatorBasis]

theorem apProductJet_derivative {input output grade : ℕ} (coefficient : SmoothOperatorJet input output)
    (field : ClosedJet input) (index : DerivativeIndex grade) (point : ClosedDisk) :
    closedMultiDerivative (apProductJet coefficient field) (derivativeMultiIndex index) point =
      ∑ split : DerivativeSplit index, (splitMultiplicity index split : ℂ) •
        (smoothOperatorDerivative coefficient (derivativeMultiIndex (lowerDerivativeIndex index split)) point)
          (closedMultiDerivative field (derivativeMultiIndex (upperDerivativeIndex index split)) point) := by
  rw [apProductJet, operatorJetColumn_multi, smoothOperatorCompose_derivative]
  change (∑ split : DerivativeSplit index, (splitMultiplicity index split : ℂ) •
      continuousOperatorComposition
        (smoothOperatorDerivative coefficient (derivativeMultiIndex (lowerDerivativeIndex index split)))
        (smoothOperatorDerivative (mappedSmoothOperatorJet (columnEmbedding 1 input 0) field)
          (derivativeMultiIndex (upperDerivativeIndex index split)))) point (operatorBasis 0) = _
  rw [continuousMap_sum_apply]
  simp only [ContinuousMap.smul_apply]
  rw [sum_apply]
  apply Finset.sum_congr rfl
  intro split _
  rw [smul_apply]
  change (splitMultiplicity index split : ℂ) •
    (smoothOperatorDerivative coefficient (derivativeMultiIndex (lowerDerivativeIndex index split)) point)
      (smoothOperatorDerivative (mappedSmoothOperatorJet (columnEmbedding 1 input 0) field)
        (derivativeMultiIndex (upperDerivativeIndex index split)) point (operatorBasis 0)) = _
  rw [mappedSmoothOperatorJet_derivative, columnEmbedding_apply]
  simp [operatorBasis]

end Grad.GaugeCoefficients.Physical.RadialLedger
