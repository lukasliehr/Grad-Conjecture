import AKAA16SingleEntryWeakKernel

noncomputable section

set_option maxHeartbeats 1400000

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ContDiff Topology

namespace Grad.CartesianStartup

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.RepresentedKernel

/-- A.e. coefficient equality identifies the actual integral operators;
 majorants are only bounds and do not change their action. -/
theorem startupEntry_congr {Parameter : Type*} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Grad.PDEBootstrap.Spatial}
    (first second : Grad.FullCellKernel.L2KernelData measure inputDimension outputDimension domain)
    (orthogonal : first.orthogonal = second.orthogonal) (output input : ℤ)
    (same : first.coefficient output input =ᵐ[measure.prod (volume.restrict domain)]
      second.coefficient output input) :
    Grad.FullCellKernel.entry first output input = Grad.FullCellKernel.entry second output input := by
  apply ContinuousLinearMap.ext
  intro field
  apply Lp.ext
  have sections := ae_ae_of_ae_prod
    ((measurePreserving_swap (μ := volume.restrict domain) (ν := measure)).quasiMeasurePreserving.ae same)
  filter_upwards [startup_entry_ae first output input field,
    startup_entry_ae second output input field, sections] with point left right identity
  rw [left, right]
  apply integral_congr_ae
  filter_upwards [identity] with parameter coefficient
  dsimp only [Prod.swap] at coefficient
  rw [coefficient, orthogonal]

theorem startupKernel_congr {Parameter : Type*} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Grad.PDEBootstrap.Spatial}
    (first second : Grad.FullCellKernel.L2KernelData measure inputDimension outputDimension domain)
    (orthogonal : first.orthogonal = second.orthogonal)
    (same : ∀ output input, first.coefficient output input =ᵐ[measure.prod (volume.restrict domain)]
      second.coefficient output input) :
    Grad.FullCellKernel.kernel first = Grad.FullCellKernel.kernel second := by
  apply ContinuousLinearMap.ext
  intro field
  apply (Grad.FullCellKernel.coordinateIsometry outputDimension domain).injective
  apply lp.ext
  funext output
  rw [Grad.FullCellKernel.coordinateIsometry_apply, Grad.FullCellKernel.coordinateIsometry_apply,
    Grad.FullCellKernel.kernel_coordinate, Grad.FullCellKernel.kernel_coordinate]
  apply tsum_congr
  intro input
  rw [startupEntry_congr first second orthogonal output input (same output input)]

theorem startupSingleEntry_derivative_ae {inputDimension outputDimension : ℕ}
    (jet : SmoothOperatorJet inputDimension outputDimension) (outputCell inputCell output input : ℤ)
    (index : ℕ × ℕ) :
    (l2Data (startupSingleEntryData jet outputCell inputCell) index 0).coefficient output input =ᵐ[
      (dirac (0 : ℝ)).prod (volume.restrict openUnitDisk)]
    (fun pair => if output = outputCell ∧ input = inputCell then
      closedDiskLift (smoothOperatorDerivative jet index) pair.2 else 0) := by
  by_cases same : output = outputCell ∧ input = inputCell
  · filter_upwards [startupJetDerivative_ae jet index] with pair identity
    change Grad.CellWeights.derivativeFactor 0 (output - input) •
      Grad.RepresentedKernel.coefficientDerivative index
        (startupSingleEntryCoefficient jet outputCell inputCell output input) pair = _
    simpa only [Grad.CellWeights.derivativeFactor, pow_zero, one_smul,
      startupSingleEntryCoefficient, if_pos same] using identity
  · filter_upwards [] with pair
    simp [l2Data, momentCoefficient, startupSingleEntryData, startupSingleEntryCoefficient,
      same, Grad.RepresentedKernel.coefficientDerivative]
    change Grad.CellWeights.derivativeFactor 0 (output - input) •
      (0 : OperatorValue inputDimension outputDimension) = 0
    rw [Grad.CellWeights.derivativeFactor, pow_zero]
    exact one_smul ℂ (0 : OperatorValue inputDimension outputDimension)

theorem startupSingleEntry_literal_entry {inputDimension outputDimension : ℕ}
    (jet : SmoothOperatorJet inputDimension outputDimension) (outputCell inputCell output input : ℤ)
    (index : ℕ × ℕ) :
    Grad.FullCellKernel.entry (l2Data (startupSingleEntryData jet outputCell inputCell) index 0) output input =
      if output = outputCell ∧ input = inputCell then closedOperatorL2 (smoothOperatorDerivative jet index) else 0 := by
  apply ContinuousLinearMap.ext
  intro field
  have identity := startupSingleEntry_derivative_ae jet outputCell inputCell output input index
  have sections := ae_ae_of_ae_prod
    ((measurePreserving_swap (μ := volume.restrict openUnitDisk) (ν := dirac (0 : ℝ))).quasiMeasurePreserving.ae identity)
  by_cases same : output = outputCell ∧ input = inputCell
  · simp only [if_pos same]
    apply Lp.ext
    filter_upwards [startup_entry_ae (l2Data (startupSingleEntryData jet outputCell inputCell) index 0) output input field,
      closedOperatorL2_ae (smoothOperatorDerivative jet index) field, sections] with point action literal equality
    rw [action, literal]
    have rewriteIntegral := integral_congr_ae (μ := dirac (0 : ℝ)) (show
      (fun parameter => (l2Data (startupSingleEntryData jet outputCell inputCell) index 0).coefficient output input
        (parameter, point) (field ((l2Data (startupSingleEntryData jet outputCell inputCell) index 0).orthogonal parameter point))) =ᵐ[dirac (0 : ℝ)]
      (fun _ => closedDiskLift (smoothOperatorDerivative jet index) point (field point)) from by
      filter_upwards [equality] with parameter coefficient
      dsimp only [Prod.swap] at coefficient
      rw [coefficient, if_pos same]
      rfl)
    rw [rewriteIntegral]
    simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  · simp only [if_neg same]
    change _ = (0 : Lp (PhysicalValue outputDimension) 2 (volume.restrict openUnitDisk))
    apply Lp.ext
    filter_upwards [startup_entry_ae (l2Data (startupSingleEntryData jet outputCell inputCell) index 0) output input field,
      sections, Lp.coeFn_zero (PhysicalValue outputDimension) 2 (volume.restrict openUnitDisk)] with point action equality zeroValue
    rw [action, zeroValue]
    have rewriteIntegral := integral_congr_ae (μ := dirac (0 : ℝ)) (show
      (fun parameter => (l2Data (startupSingleEntryData jet outputCell inputCell) index 0).coefficient output input
        (parameter, point) (field ((l2Data (startupSingleEntryData jet outputCell inputCell) index 0).orthogonal parameter point))) =ᵐ[dirac (0 : ℝ)]
      (fun _ => (0 : PhysicalValue outputDimension)) from by
      filter_upwards [equality] with parameter coefficient
      dsimp only [Prod.swap] at coefficient
      rw [coefficient, if_neg same]
      rfl)
    rw [rewriteIntegral]
    simp only [integral_zero]
    rfl

theorem startupSingleEntry_literal_operator {inputDimension outputDimension : ℕ}
    (jet : SmoothOperatorJet inputDimension outputDimension) (outputCell inputCell : ℤ)
    (index : ℕ × ℕ) (field : StartupL2 inputDimension) :
    operator (startupSingleEntryData jet outputCell inputCell) index 0 field =
      Grad.FullCellKernel.insertCell outputDimension openUnitDisk outputCell
        (closedOperatorL2 (smoothOperatorDerivative jet index)
          (fieldCellProjection inputDimension openUnitDisk inputCell field)) := by
  apply (Grad.FullCellKernel.coordinateIsometry outputDimension openUnitDisk).injective
  apply lp.ext
  funext output
  rw [Grad.FullCellKernel.coordinateIsometry_apply, Grad.FullCellKernel.coordinateIsometry_apply,
    operator_coordinate, Grad.FullCellKernel.projection_insertCell]
  simp_rw [startupSingleEntry_literal_entry]
  by_cases same : output = outputCell
  · subst output
    simp only [true_and, if_true]
    have equality : (fun input : ℤ =>
        (if input = inputCell then closedOperatorL2 (smoothOperatorDerivative jet index) else 0)
          (fieldCellProjection inputDimension openUnitDisk input field)) =
        (fun input : ℤ => if input = inputCell then
          closedOperatorL2 (smoothOperatorDerivative jet index)
            (fieldCellProjection inputDimension openUnitDisk input field) else 0) := by
      funext input
      split_ifs <;> rfl
    rw [equality, tsum_ite_eq]
  · simp [same]

end Grad.CartesianStartup
