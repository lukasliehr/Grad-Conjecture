import RKWD1IBP
import KI1Analysis

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open Grad.RepresentedKernel.SpatialProduct
open scoped BigOperators ContDiff Topology

universe parameterUniverse

namespace Grad.RepresentedKernel.WeakDerivatives

theorem testedCoefficient_integrable
    {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    (output input : ℤ) (field : Lp (PhysicalValue inputDimension) 2 (volume.restrict domain))
    (test : Spatial → ℝ) (testMeasurable : Measurable test)
    (testLp : MemLp test 2 (volume.restrict domain))
    (vector : PhysicalValue outputDimension) :
    Integrable (fun pair : Parameter × Spatial =>
      test pair.2 • inner ℂ vector
        (data.coefficient output input pair (field (data.orthogonal pair.1 pair.2))))
      (measure.prod (volume.restrict domain)) := by
  let weight := data.majorant (0, 0) 0 output input
  have coefficientMeasurable : AEStronglyMeasurable (data.coefficient output input)
      (measure.prod (volume.restrict domain)) := by
    simpa only [coefficientDerivative_zero] using
      data.derivativeMeasurable (0, 0) output input
  have transportedMeasurable : AEStronglyMeasurable
      (fun pair : Parameter × Spatial => field (data.orthogonal pair.1 pair.2))
      (measure.prod (volume.restrict domain)) :=
    ((Lp.stronglyMeasurable field).comp_measurable data.actionMeasurable).aestronglyMeasurable
  have appliedMeasurable : AEStronglyMeasurable
      (fun pair : Parameter × Spatial =>
        data.coefficient output input pair (field (data.orthogonal pair.1 pair.2)))
      (measure.prod (volume.restrict domain)) :=
    (continuous_fst.clm_apply continuous_snd).comp_aestronglyMeasurable
      (coefficientMeasurable.prodMk transportedMeasurable)
  have integrandMeasurable : AEStronglyMeasurable (fun pair : Parameter × Spatial =>
      test pair.2 • inner ℂ vector
        (data.coefficient output input pair (field (data.orthogonal pair.1 pair.2))))
      (measure.prod (volume.restrict domain)) :=
    (testMeasurable.comp measurable_snd).aestronglyMeasurable.smul
      ((innerSL ℂ vector).continuous.comp_aestronglyMeasurable appliedMeasurable)
  have testEnergy : Integrable (fun pair : Parameter × Spatial =>
      weight pair.1 * ‖test pair.2‖ ^ 2) (measure.prod (volume.restrict domain)) :=
    (data.majorantIntegrable (0, 0) 0 output input).mul_prod testLp.norm.integrable_sq
  have fieldEnergy : Integrable (fun pair : Parameter × Spatial =>
      weight pair.1 * ‖field (data.orthogonal pair.1 pair.2)‖ ^ 2)
      (measure.prod (volume.restrict domain)) :=
    (Grad.SchurKernel.RealEnergy.field_energy measure domain data.domainOpen.measurableSet
      data.orthogonal data.invariant data.actionMeasurable weight
      (data.majorantMeasurable (0, 0) 0 output input)
      (data.majorantNonnegative (0, 0) 0 output input)
      (data.majorantIntegrable (0, 0) 0 output input) field).1
  have coefficientBound : ∀ᵐ pair ∂measure.prod (volume.restrict domain),
      ‖data.coefficient output input pair‖ ≤ weight pair.1 := by
    simpa only [coefficientDerivative_zero, pow_zero, mul_one] using
      derivative_domination data (0, 0) 0 output input
  refine ((testEnergy.add fieldEnergy).const_mul ‖vector‖).mono' integrandMeasurable ?_
  filter_upwards [coefficientBound] with pair coefficientEstimate
  have evaluationEstimate :
      ‖data.coefficient output input pair (field (data.orthogonal pair.1 pair.2))‖ ≤
        weight pair.1 * ‖field (data.orthogonal pair.1 pair.2)‖ :=
    ((data.coefficient output input pair).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right coefficientEstimate (norm_nonneg _))
  have young : 2 * (‖test pair.2‖ * ‖field (data.orthogonal pair.1 pair.2)‖) ≤
      ‖test pair.2‖ ^ 2 + ‖field (data.orthogonal pair.1 pair.2)‖ ^ 2 := by
    nlinarith [sq_nonneg (‖test pair.2‖ - ‖field (data.orthogonal pair.1 pair.2)‖)]
  have weightNonnegative : 0 ≤ weight pair.1 :=
    data.majorantNonnegative (0, 0) 0 output input pair.1
  have weightedYoung : weight pair.1 *
      (2 * (‖test pair.2‖ * ‖field (data.orthogonal pair.1 pair.2)‖)) ≤
      weight pair.1 *
        (‖test pair.2‖ ^ 2 + ‖field (data.orthogonal pair.1 pair.2)‖ ^ 2) :=
    mul_le_mul_of_nonneg_left young weightNonnegative
  have productNonnegative :
      0 ≤ weight pair.1 * ‖test pair.2‖ *
        ‖field (data.orthogonal pair.1 pair.2)‖ := by positivity
  calc
    ‖test pair.2 • inner ℂ vector
        (data.coefficient output input pair (field (data.orthogonal pair.1 pair.2)))‖
        = ‖test pair.2‖ * ‖inner ℂ vector
            (data.coefficient output input pair
              (field (data.orthogonal pair.1 pair.2)))‖ := norm_smul _ _
    _ ≤ ‖test pair.2‖ * (‖vector‖ *
          ‖data.coefficient output input pair
            (field (data.orthogonal pair.1 pair.2))‖) :=
      mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
    _ ≤ ‖test pair.2‖ * (‖vector‖ *
          (weight pair.1 * ‖field (data.orthogonal pair.1 pair.2)‖)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left evaluationEstimate (norm_nonneg _)) (norm_nonneg _)
    _ ≤ ‖vector‖ *
          (weight pair.1 * ‖test pair.2‖ ^ 2 +
            weight pair.1 * ‖field (data.orthogonal pair.1 pair.2)‖ ^ 2) := by
      nlinarith [weightedYoung, productNonnegative, norm_nonneg vector]

theorem coefficientCell_row_integrable
    {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    (output input : ℤ) (field : FieldL2 inputDimension domain) :
    ∀ᵐ point ∂volume.restrict domain, Integrable (fun parameter =>
      data.coefficient output input (parameter, point)
        (field (data.orthogonal parameter point) input)) measure := by
  let coordinate := fieldCellProjection inputDimension domain input field
  let weight := data.majorant (0, 0) 0 output input
  have coefficientMeasurable : AEStronglyMeasurable (data.coefficient output input)
      (measure.prod (volume.restrict domain)) := by
    simpa only [coefficientDerivative_zero] using
      data.derivativeMeasurable (0, 0) output input
  have coefficientBound : ∀ᵐ pair ∂measure.prod (volume.restrict domain),
      ‖data.coefficient output input pair‖ ≤ weight pair.1 := by
    simpa only [coefficientDerivative_zero, pow_zero, mul_one] using
      derivative_domination data (0, 0) 0 output input
  have projectedRows := Grad.KernelIntegral.row_integrable_and_sq_bound measure
    data.domainOpen.measurableSet data.orthogonal data.invariant data.actionMeasurable
    (data.coefficient output input) weight coefficientMeasurable
    (data.majorantMeasurable (0, 0) 0 output input)
    (data.majorantNonnegative (0, 0) 0 output input)
    (data.majorantIntegrable (0, 0) 0 output input) coefficientBound coordinate
  have coordinateEquality : coordinate =ᵐ[volume.restrict domain]
      fun point => field point input :=
    (fieldCellProjection_ae inputDimension domain field).mono fun _ equality => equality input
  have transported := Grad.KernelIntegral.transported_ae_eq_sections measure
    data.domainOpen.measurableSet data.orthogonal data.invariant data.actionMeasurable coordinateEquality
  filter_upwards [projectedRows, transported] with point projectedRow rowEquality
  exact projectedRow.1.congr (rowEquality.mono fun parameter equality => by
    change data.coefficient output input (parameter, point)
        (coordinate (data.orthogonal parameter point)) =
      data.coefficient output input (parameter, point)
        (field (data.orthogonal parameter point) input)
    exact congrArg _ equality)

theorem testedCell_integrable
    {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    (output input : ℤ) (field : FieldL2 inputDimension domain)
    (test : Spatial → ℝ) (testMeasurable : Measurable test)
    (testLp : MemLp test 2 (volume.restrict domain))
    (vector : PhysicalValue outputDimension) :
    Integrable (fun pair : Parameter × Spatial =>
      test pair.2 • inner ℂ vector
        (data.coefficient output input pair
          (field (data.orthogonal pair.1 pair.2) input)))
      (measure.prod (volume.restrict domain)) := by
  let coordinate := fieldCellProjection inputDimension domain input field
  have projected := testedCoefficient_integrable data output input coordinate test
    testMeasurable testLp vector
  have coordinateEquality : coordinate =ᵐ[volume.restrict domain]
      fun point => field point input :=
    (fieldCellProjection_ae inputDimension domain field).mono fun _ equality => equality input
  have transported := (Grad.KernelIntegral.joint_action_quasiMeasurePreserving measure
    data.domainOpen.measurableSet data.orthogonal data.invariant data.actionMeasurable).ae_eq
      coordinateEquality
  exact projected.congr (transported.mono fun pair equality => by
    have equalityAt : coordinate (data.orthogonal pair.1 pair.2) =
        field (data.orthogonal pair.1 pair.2) input := by
      simpa only [Function.comp_apply] using equality
    exact congrArg (fun value => test pair.2 • inner ℂ vector
      (data.coefficient output input pair value)) equalityAt)

theorem testedCell_representative_integrable
    {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    (output input : ℤ) (field : FieldL2 inputDimension domain)
    (representative : Spatial → CellValues inputDimension)
    (realized : field =ᵐ[volume.restrict domain] representative)
    (test : Spatial → ℝ) (testMeasurable : Measurable test)
    (testLp : MemLp test 2 (volume.restrict domain))
    (vector : PhysicalValue outputDimension) :
    Integrable (fun pair : Parameter × Spatial =>
      test pair.2 • inner ℂ vector
        (data.coefficient output input pair
          (representative (data.orthogonal pair.1 pair.2) input)))
      (measure.prod (volume.restrict domain)) := by
  have actual := testedCell_integrable data output input field test testMeasurable testLp vector
  have transported := (Grad.KernelIntegral.joint_action_quasiMeasurePreserving measure
    data.domainOpen.measurableSet data.orthogonal data.invariant data.actionMeasurable).ae_eq realized
  exact actual.congr (transported.mono fun pair equality =>
    congrArg (fun value : CellValues inputDimension => test pair.2 • inner ℂ vector
      (data.coefficient output input pair (value input))) equality)

theorem coefficientCell_pairing_fubini
    {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    (output input : ℤ) (field : FieldL2 inputDimension domain)
    (test : Spatial → ℝ) (testMeasurable : Measurable test)
    (testLp : MemLp test 2 (volume.restrict domain))
    (vector : PhysicalValue outputDimension) :
    (∫ point in domain, test point • inner ℂ vector
      (∫ parameter, data.coefficient output input (parameter, point)
        (field (data.orthogonal parameter point) input) ∂measure)) =
      ∫ parameter, (∫ point in domain, test point • inner ℂ vector
        (data.coefficient output input (parameter, point)
          (field (data.orthogonal parameter point) input))) ∂measure := by
  have productIntegrable := testedCell_integrable data output input field test
    testMeasurable testLp vector
  have vectorRows := coefficientCell_row_integrable data output input field
  have rowIdentity : ∀ᵐ point ∂volume.restrict domain,
      test point • inner ℂ vector
          (∫ parameter, data.coefficient output input (parameter, point)
            (field (data.orthogonal parameter point) input) ∂measure) =
        ∫ parameter, test point • inner ℂ vector
          (data.coefficient output input (parameter, point)
            (field (data.orthogonal parameter point) input)) ∂measure := by
    filter_upwards [vectorRows] with point rowIntegrable
    let functional : PhysicalValue outputDimension →L[ℝ] ℂ :=
      (test point) • (innerSL ℂ vector).restrictScalars ℝ
    change functional (∫ parameter, data.coefficient output input (parameter, point)
        (field (data.orthogonal parameter point) input) ∂measure) = _
    rw [(functional.integral_comp_comm rowIntegrable).symm]
    apply integral_congr_ae
    filter_upwards [] with parameter
    rfl
  calc
    _ = ∫ point in domain, ∫ parameter, test point • inner ℂ vector
          (data.coefficient output input (parameter, point)
            (field (data.orthogonal parameter point) input)) ∂measure :=
      integral_congr_ae rowIdentity
    _ = ∫ pair : Parameter × Spatial, test pair.2 • inner ℂ vector
          (data.coefficient output input pair
            (field (data.orthogonal pair.1 pair.2) input))
          ∂measure.prod (volume.restrict domain) :=
      (integral_prod_symm _ productIntegrable).symm
    _ = _ := integral_prod _ productIntegrable

theorem operator_pairing_fubini
    {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    (field : FieldL2 inputDimension domain) (cells : Finset ℤ)
    (support : ∀ input ∉ cells,
      fieldCellProjection inputDimension domain input field = 0)
    (output : ℤ) (vector : PhysicalValue outputDimension)
    (test : Spatial → ℝ) (testMeasurable : Measurable test)
    (testLp : MemLp test 2 (volume.restrict domain)) :
    (∫ point in domain, test point • inner ℂ vector
      (operator data (0, 0) 0 field point output)) =
      ∑ input ∈ cells, ∫ parameter,
        (∫ point in domain, test point • inner ℂ vector
          (data.coefficient output input (parameter, point)
            (field (data.orthogonal parameter point) input))) ∂measure := by
  have core := (operator_zero_core_ae data field cells support).mono
    fun _ equality => equality output
  calc
    (∫ point in domain, test point • inner ℂ vector
        (operator data (0, 0) 0 field point output)) =
        ∫ point in domain, test point • inner ℂ vector
          (∑ input ∈ cells, ∫ parameter,
            data.coefficient output input (parameter, point)
              (field (data.orthogonal parameter point) input) ∂measure) := by
      apply integral_congr_ae
      filter_upwards [core] with point equality
      rw [equality]
    _ = ∫ point in domain, ∑ input ∈ cells,
          test point • inner ℂ vector
            (∫ parameter, data.coefficient output input (parameter, point)
              (field (data.orthogonal parameter point) input) ∂measure) := by
      congr 1
      funext point
      let functional : PhysicalValue outputDimension →L[ℝ] ℂ :=
        (test point) • (innerSL ℂ vector).restrictScalars ℝ
      change functional (∑ input ∈ cells, ∫ parameter,
          data.coefficient output input (parameter, point)
            (field (data.orthogonal parameter point) input) ∂measure) =
        ∑ input ∈ cells, functional (∫ parameter,
          data.coefficient output input (parameter, point)
            (field (data.orthogonal parameter point) input) ∂measure)
      exact map_sum functional (fun input => ∫ parameter,
        data.coefficient output input (parameter, point)
          (field (data.orthogonal parameter point) input) ∂measure) cells
    _ = ∑ input ∈ cells, ∫ point in domain,
          test point • inner ℂ vector
            (∫ parameter, data.coefficient output input (parameter, point)
              (field (data.orthogonal parameter point) input) ∂measure) := by
      apply integral_finsetSum
      intro input _membership
      have productIntegrable := testedCell_integrable data output input field test
        testMeasurable testLp vector
      have scalarRows := productIntegrable.prod_left_ae
      have vectorRows := coefficientCell_row_integrable data output input field
      have rowIdentity : ∀ᵐ point ∂volume.restrict domain,
          test point • inner ℂ vector
              (∫ parameter, data.coefficient output input (parameter, point)
                (field (data.orthogonal parameter point) input) ∂measure) =
            ∫ parameter, test point • inner ℂ vector
              (data.coefficient output input (parameter, point)
                (field (data.orthogonal parameter point) input)) ∂measure := by
        filter_upwards [vectorRows] with point rowIntegrable
        let functional : PhysicalValue outputDimension →L[ℝ] ℂ :=
          (test point) • (innerSL ℂ vector).restrictScalars ℝ
        change functional (∫ parameter, data.coefficient output input (parameter, point)
            (field (data.orthogonal parameter point) input) ∂measure) = _
        rw [(functional.integral_comp_comm rowIntegrable).symm]
        apply integral_congr_ae
        filter_upwards [] with parameter
        rfl
      exact productIntegrable.integral_prod_right.congr
        (rowIdentity.mono fun _ equality => equality.symm)
    _ = ∑ input ∈ cells, ∫ parameter,
        (∫ point in domain, test point • inner ℂ vector
            (data.coefficient output input (parameter, point)
              (field (data.orthogonal parameter point) input))) ∂measure := by
      apply Finset.sum_congr rfl
      intro input _membership
      exact coefficientCell_pairing_fubini data output input field test testMeasurable testLp vector

theorem operator_pairing_representative
    {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    (field : FieldL2 inputDimension domain) (cells : Finset ℤ)
    (support : ∀ input ∉ cells,
      fieldCellProjection inputDimension domain input field = 0)
    (representative : Spatial → CellValues inputDimension)
    (realized : field =ᵐ[volume.restrict domain] representative)
    (output : ℤ) (vector : PhysicalValue outputDimension)
    (test : Spatial → ℝ) (testMeasurable : Measurable test)
    (testLp : MemLp test 2 (volume.restrict domain)) :
    (∫ point in domain, test point • inner ℂ vector
      (operator data (0, 0) 0 field point output)) =
      ∑ input ∈ cells, ∫ parameter,
        (∫ point in domain, test point • inner ℂ vector
          (data.coefficient output input (parameter, point)
            (representative (data.orthogonal parameter point) input))) ∂measure := by
  rw [operator_pairing_fubini data field cells support output vector test testMeasurable testLp]
  apply Finset.sum_congr rfl
  intro input _membership
  have actualIntegrable := testedCell_integrable data output input field test
    testMeasurable testLp vector
  have transported := (Grad.KernelIntegral.joint_action_quasiMeasurePreserving measure
    data.domainOpen.measurableSet data.orthogonal data.invariant data.actionMeasurable).ae_eq realized
  have integrandEquality : (fun pair : Parameter × Spatial =>
      test pair.2 • inner ℂ vector
        (data.coefficient output input pair
          (field (data.orthogonal pair.1 pair.2) input))) =ᵐ[
        measure.prod (volume.restrict domain)] fun pair =>
      test pair.2 • inner ℂ vector
        (data.coefficient output input pair
          (representative (data.orthogonal pair.1 pair.2) input)) :=
    transported.mono fun pair equality => congrArg (fun value : CellValues inputDimension =>
      test pair.2 • inner ℂ vector
        (data.coefficient output input pair (value input))) equality
  have representativeIntegrable : Integrable (fun pair : Parameter × Spatial =>
      test pair.2 • inner ℂ vector
        (data.coefficient output input pair
          (representative (data.orthogonal pair.1 pair.2) input)))
      (measure.prod (volume.restrict domain)) :=
    actualIntegrable.congr integrandEquality
  calc
    _ = ∫ pair : Parameter × Spatial, test pair.2 • inner ℂ vector
          (data.coefficient output input pair
            (field (data.orthogonal pair.1 pair.2) input))
          ∂measure.prod (volume.restrict domain) := (integral_prod _ actualIntegrable).symm
    _ = ∫ pair : Parameter × Spatial, test pair.2 • inner ℂ vector
          (data.coefficient output input pair
            (representative (data.orthogonal pair.1 pair.2) input))
          ∂measure.prod (volume.restrict domain) := integral_congr_ae integrandEquality
    _ = _ := integral_prod _ representativeIntegrable

theorem operator_pairing_product_representative
    {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    (field : FieldL2 inputDimension domain) (cells : Finset ℤ)
    (support : ∀ input ∉ cells,
      fieldCellProjection inputDimension domain input field = 0)
    (representative : Spatial → CellValues inputDimension)
    (realized : field =ᵐ[volume.restrict domain] representative)
    (output : ℤ) (vector : PhysicalValue outputDimension)
    (test : Spatial → ℝ) (testMeasurable : Measurable test)
    (testLp : MemLp test 2 (volume.restrict domain)) :
    (∫ point in domain, test point • inner ℂ vector
      (operator data (0, 0) 0 field point output)) =
      ∑ input ∈ cells, ∫ pair : Parameter × Spatial,
        test pair.2 • inner ℂ vector
          (data.coefficient output input pair
            (representative (data.orthogonal pair.1 pair.2) input))
        ∂measure.prod (volume.restrict domain) := by
  rw [operator_pairing_representative data field cells support representative realized output vector
    test testMeasurable testLp]
  apply Finset.sum_congr rfl
  intro input _membership
  exact (integral_prod _ (testedCell_representative_integrable data output input field
    representative realized test testMeasurable testLp vector)).symm

end Grad.RepresentedKernel.WeakDerivatives
