import AKAA15LiteralCurrentRowKernels
import RKWD1Consumer

noncomputable section

set_option maxHeartbeats 1200000

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ContDiff Topology

namespace Grad.CartesianStartup

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- On each fixed pair of cells the actual conjugated jet has all finite
 Cartesian derivative bounds. This does not assert an unreserved bound
 uniform in the input cell for second or higher phase derivatives. -/
theorem startupJetDerivative_ae {inputDimension outputDimension : ℕ}
    (jet : SmoothOperatorJet inputDimension outputDimension) (index : ℕ × ℕ) :
    (fun pair : ℝ × Grad.PDEBootstrap.Spatial =>
      Grad.RepresentedKernel.coefficientDerivative index
        (fun pair => closedDiskLift jet.value pair.2) pair) =ᵐ[
          (Measure.dirac (0 : ℝ)).prod (volume.restrict openUnitDisk)]
      (fun pair => closedDiskLift (smoothOperatorDerivative jet index) pair.2) := by
  filter_upwards [quasiMeasurePreserving_snd.ae
    (ae_restrict_mem openUnitDisk_isOpen.measurableSet)] with pair inside
  have specification := Classical.choose_spec (jet.derivativeExists index)
  have identity := specification ⟨pair.2, openDiskMembershipClosed pair.2 inside⟩ inside
  change cartesianMultiDerivative index (closedDiskLift jet.value) pair.2 = _
  simp only [closedDiskLift, openDiskMembershipClosed pair.2 inside, dite_true]
  exact identity.symm

def startupSingleEntryCoefficient {inputDimension outputDimension : ℕ}
    (jet : SmoothOperatorJet inputDimension outputDimension) (outputCell inputCell output input : ℤ)
    : ℝ × Grad.PDEBootstrap.Spatial → OperatorValue inputDimension outputDimension :=
  if output = outputCell ∧ input = inputCell then (fun pair => closedDiskLift jet.value pair.2) else (fun _ => 0)

def startupSingleEntryBound {inputDimension outputDimension : ℕ}
    (jet : SmoothOperatorJet inputDimension outputDimension) (outputCell inputCell : ℤ)
    (index : ℕ × ℕ) (moment : ℕ) : ℝ :=
  ‖smoothOperatorDerivative jet index‖ * Grad.CellWeights.cellWeight (outputCell - inputCell) ^ moment

/-- A genuine represented kernel for one entry, ready for the accepted
 compact-test weak differentiation theorem. All cell moments remain literal. -/
def startupSingleEntryData {inputDimension outputDimension : ℕ}
    (jet : SmoothOperatorJet inputDimension outputDimension) (outputCell inputCell : ℤ) :
    Grad.RepresentedKernel.RawKernelData (Measure.dirac (0 : ℝ))
      inputDimension outputDimension openUnitDisk where
  domainOpen := openUnitDisk_isOpen
  orthogonal := fun _ => LinearIsometryEquiv.refl ℝ _
  invariant := fun _ => by intro point; rfl
  actionMeasurable := measurable_snd
  coefficient := startupSingleEntryCoefficient jet outputCell inputCell
  coefficientSmooth := fun output input _ => by
    by_cases same : output = outputCell ∧ input = inputCell
    · simpa only [startupSingleEntryCoefficient, if_pos same] using jet.smoothInterior
    · simpa only [startupSingleEntryCoefficient, if_neg same] using
        (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Grad.PDEBootstrap.Spatial =>
          (0 : OperatorValue inputDimension outputDimension)) openUnitDisk)
  derivativeMeasurable := fun index output input => by
    by_cases same : output = outputCell ∧ input = inputCell
    · simp only [startupSingleEntryCoefficient, if_pos same]
      exact ((closedOperator_measurable (smoothOperatorDerivative jet index)).comp_quasiMeasurePreserving
        quasiMeasurePreserving_snd).congr (startupJetDerivative_ae jet index).symm
    · simp only [startupSingleEntryCoefficient, if_neg same]
      have equality : Grad.RepresentedKernel.coefficientDerivative index
          (fun _ : ℝ × Grad.PDEBootstrap.Spatial => (0 : OperatorValue inputDimension outputDimension)) = 0 := by
        funext pair
        simp [Grad.RepresentedKernel.coefficientDerivative]
      rw [equality]
      exact aestronglyMeasurable_const
  envelope := fun _ _ _ => 1
  envelopeOneLe := fun _ _ => Filter.Eventually.of_forall (fun _ => le_rfl)
  majorant := fun index moment output input _ =>
    if output = outputCell ∧ input = inputCell then startupSingleEntryBound jet outputCell inputCell index moment else 0
  majorantMeasurable := fun _ _ _ _ => measurable_const
  majorantNonnegative := fun index moment output input _ => by
    split_ifs
    · exact mul_nonneg (norm_nonneg (smoothOperatorDerivative jet index)) (pow_nonneg (Grad.CellWeights.cellWeight_pos _).le _)
    · exact le_rfl
  majorantIntegrable := fun _ _ _ _ => integrable_const _
  domination := fun index moment output input => by
    by_cases same : output = outputCell ∧ input = inputCell
    · rcases same with ⟨rfl, rfl⟩
      filter_upwards [startupJetDerivative_ae jet index,
        quasiMeasurePreserving_snd.ae (closedOperator_bound (smoothOperatorDerivative jet index))]
        with pair identity bound
      simp only [startupSingleEntryCoefficient, and_self, if_true, mul_one]
      rw [identity]
      exact mul_le_mul_of_nonneg_right bound (pow_nonneg (Grad.CellWeights.cellWeight_pos _).le _)
    · simp [startupSingleEntryCoefficient, same, Grad.RepresentedKernel.coefficientDerivative]
  rowBound := startupSingleEntryBound jet outputCell inputCell
  columnBound := startupSingleEntryBound jet outputCell inputCell
  rowNonnegative := fun index _ => by exact mul_nonneg (norm_nonneg (smoothOperatorDerivative jet index)) (pow_nonneg (Grad.CellWeights.cellWeight_pos _).le _)
  columnNonnegative := fun index _ => by exact mul_nonneg (norm_nonneg (smoothOperatorDerivative jet index)) (pow_nonneg (Grad.CellWeights.cellWeight_pos _).le _)
  rowsSummable := fun index moment output => by
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    by_cases same : output = outputCell
    · simp only [same, true_and]
      exact (hasSum_ite_eq inputCell (startupSingleEntryBound jet outputCell inputCell index moment)).summable
    · simp only [same, false_and, if_false]
      exact summable_zero
  columnsSummable := fun index moment input => by
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    by_cases same : input = inputCell
    · simp only [same, and_true]
      exact (hasSum_ite_eq outputCell (startupSingleEntryBound jet outputCell inputCell index moment)).summable
    · simp only [same, and_false, if_false]
      exact summable_zero
  rows := fun index moment output => by
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    by_cases same : output = outputCell
    · simp only [same, true_and, tsum_ite_eq]
      exact le_rfl
    · simp only [same, false_and, if_false, tsum_zero]
      exact mul_nonneg (norm_nonneg (smoothOperatorDerivative jet index)) (pow_nonneg (Grad.CellWeights.cellWeight_pos _).le _)
  columns := fun index moment input => by
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    by_cases same : input = inputCell
    · simp only [same, and_true, tsum_ite_eq]
      exact le_rfl
    · simp only [same, and_false, if_false, tsum_zero]
      exact mul_nonneg (norm_nonneg (smoothOperatorDerivative jet index)) (pow_nonneg (Grad.CellWeights.cellWeight_pos _).le _)

end Grad.CartesianStartup
