import AKAA17SingleEntryLiteralAction

noncomputable section

set_option maxHeartbeats 1400000

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ContDiff Topology

namespace Grad.CartesianStartup

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.RepresentedKernel
open Grad.RepresentedKernel.WeakDerivatives Grad.RepresentedKernel.SpatialProduct

theorem startupEntry_smul {Parameter : Type*} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Grad.PDEBootstrap.Spatial}
    (first second : Grad.FullCellKernel.L2KernelData measure inputDimension outputDimension domain)
    (orthogonal : first.orthogonal = second.orthogonal) (scalar : ℂ) (output input : ℤ)
    (same : first.coefficient output input =ᵐ[measure.prod (volume.restrict domain)]
      (fun pair => scalar • second.coefficient output input pair)) :
    Grad.FullCellKernel.entry first output input = scalar • Grad.FullCellKernel.entry second output input := by
  apply ContinuousLinearMap.ext
  intro field
  change _ = scalar • (Grad.FullCellKernel.entry second output input field)
  apply Lp.ext
  have sections := ae_ae_of_ae_prod
    ((measurePreserving_swap (μ := volume.restrict domain) (ν := measure)).quasiMeasurePreserving.ae same)
  filter_upwards [startup_entry_ae first output input field,
    startup_entry_ae second output input field, sections,
    Lp.coeFn_smul scalar (Grad.FullCellKernel.entry second output input field)] with point left right identity scaled
  rw [left, scaled, Pi.smul_apply, right]
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [identity] with parameter coefficient
  dsimp only [Prod.swap] at coefficient
  rw [coefficient, orthogonal]
  rfl

theorem startupKernel_smul {Parameter : Type*} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Grad.PDEBootstrap.Spatial}
    (first second : Grad.FullCellKernel.L2KernelData measure inputDimension outputDimension domain)
    (orthogonal : first.orthogonal = second.orthogonal) (scalar : ℂ)
    (same : ∀ output input, first.coefficient output input =ᵐ[measure.prod (volume.restrict domain)]
      (fun pair => scalar • second.coefficient output input pair)) :
    Grad.FullCellKernel.kernel first = scalar • Grad.FullCellKernel.kernel second := by
  apply ContinuousLinearMap.ext
  intro field
  change _ = scalar • (Grad.FullCellKernel.kernel second field)
  apply (Grad.FullCellKernel.coordinateIsometry outputDimension domain).injective
  apply lp.ext
  funext output
  rw [Grad.FullCellKernel.coordinateIsometry_apply, Grad.FullCellKernel.coordinateIsometry_apply,
    map_smul, Grad.FullCellKernel.kernel_coordinate, Grad.FullCellKernel.kernel_coordinate]
  rw [← tsum_const_smul'' scalar]
  apply tsum_congr
  intro input
  rw [startupEntry_smul first second orthogonal scalar output input (same output input)]
  rfl

/-- For a constant orthogonal pullback, each accepted weak allocation is
 exactly a scalar multiple of the genuine coefficient-derivative kernel. -/
theorem startupAllocated_operator {Parameter : Type*} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Grad.PDEBootstrap.Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    (reference : Parameter) (constant : ∀ parameter, data.orthogonal parameter = data.orthogonal reference)
    {rank : ℕ} (word : Word rank) (selected : Finset (Fin rank)) (target : Word selectedᶜ.card) :
    operator (allocatedData data word selected target) (0, 0) 0 =
      (chainProduct data word selected target reference : ℂ) •
        operator data (selectedIndex word selected) 0 := by
  apply startupKernel_smul
    (l2Data (allocatedData data word selected target) (0, 0) 0)
    (l2Data data (selectedIndex word selected) 0) rfl
  intro output input
  filter_upwards [] with pair
  change (Grad.CellWeights.derivativeFactor 0 (output - input)) •
      allocatedCoefficient data word selected target output input pair =
    (chainProduct data word selected target reference : ℂ) •
      ((Grad.CellWeights.derivativeFactor 0 (output - input)) •
        Grad.RepresentedKernel.coefficientDerivative (selectedIndex word selected) (data.coefficient output input) pair)
  simp only [Grad.CellWeights.derivativeFactor, pow_zero, one_smul, allocatedCoefficient]
  congr 1
  unfold chainProduct
  rw [constant pair.1]

/-- The accepted weak product theorem for the SAME fixed entry, with no
 assumed derivative of its output. -/
theorem startupSingleEntry_weak {inputDimension outputDimension order rank weight : ℕ}
    (jet : SmoothOperatorJet inputDimension outputDimension) (outputCell inputCell : ℤ)
    (word : Word rank) (bound : rank ≤ order)
    (field : Grad.WeightedJets.GraphGrade inputDimension order weight openUnitDisk) :
    Grad.WeakTesting.Commutation.HasWeakOrderedDerivative outputDimension openUnitDisk rank word
      (operator (startupSingleEntryData jet outputCell inputCell) (0, 0) 0
        (Grad.WeightedJets.base inputDimension order openUnitDisk (fun _ => weight) field))
      (∑ selected : Finset (Fin rank), ∑ target : Word selectedᶜ.card,
        operator (allocatedData (startupSingleEntryData jet outputCell inputCell) word selected target) (0, 0) 0
          (inputDerivative inputDimension order rank weight openUnitDisk bound field selected target)) := by
  have consumer :
      ∀ (data : RawKernelData (dirac (0 : ℝ)) inputDimension outputDimension (Grad.SpatialDilation.disk 1))
        (word : Word rank) (bound : rank ≤ order)
        (family : AllocatedFamily (dirac (0 : ℝ)) inputDimension outputDimension (Grad.SpatialDilation.disk 1) rank),
        FamilySpecification data word family →
        ∀ field : Grad.WeightedJets.GraphGrade inputDimension order weight (Grad.SpatialDilation.disk 1),
        Grad.WeakTesting.Commutation.HasWeakOrderedDerivative outputDimension (Grad.SpatialDilation.disk 1) rank word
          (operator data (0, 0) 0 (Grad.WeightedJets.base inputDimension order (Grad.SpatialDilation.disk 1) (fun _ => weight) field))
          (∑ selected : Finset (Fin rank), ∑ target : Word selectedᶜ.card,
            operator (family selected target) (0, 0) 0
              (inputDerivative inputDimension order rank weight (Grad.SpatialDilation.disk 1) bound field selected target)) :=
    weakGraphConsumer ℝ (dirac (0 : ℝ)) inputDimension outputDimension order rank weight 1 (by norm_num)
  have domain : Grad.SpatialDilation.disk 1 = openUnitDisk := openUnitDisk_eq_ball.symm
  rw [domain] at consumer
  exact consumer (startupSingleEntryData jet outputCell inputCell) word bound
    (fun selected target => allocatedData (startupSingleEntryData jet outputCell inputCell) word selected target)
    (fun selected target => allocatedData_specification (startupSingleEntryData jet outputCell inputCell) word selected target) field

end Grad.CartesianStartup
