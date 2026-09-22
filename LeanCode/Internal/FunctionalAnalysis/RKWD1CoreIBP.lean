import RKWD1Fubini

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open Grad.RepresentedKernel.SpatialProduct
open Grad.SpatialDilation (disk)
open scoped BigOperators ContDiff Topology

universe parameterUniverse

namespace Grad.RepresentedKernel.WeakDerivatives

theorem allocated_operator_pairing
    {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension order rank weight : ℕ} {radius : ℝ}
    (data : RawKernelData measure inputDimension outputDimension (disk radius))
    (word : Word rank) (bound : rank ≤ order)
    (family : AllocatedFamily measure inputDimension outputDimension (disk radius) rank)
    (familySpec : FamilySpecification data word family)
    (jet : Grad.WeightedJets.GraphGrade inputDimension order weight (disk radius))
    (function : Spatial → CellValues inputDimension) (cells : Finset ℤ)
    (core : Grad.SmoothDensity.CoreLaws inputDimension function cells)
    (realized : Grad.SmoothDensity.Realizes inputDimension (disk radius)
      (.graph order weight) function jet)
    (selected : Finset (Fin rank)) (target : Word (selectedᶜ).card)
    (output : ℤ) (vector : PhysicalValue outputDimension)
    (test : Spatial → ℝ) (testSmooth : ContDiff ℝ ∞ test)
    (testCompact : HasCompactSupport test) :
    (∫ point in disk radius, test point • inner ℂ vector
      (operator (family selected target) (0, 0) 0
        (inputDerivative inputDimension order rank weight (disk radius) bound jet selected target)
        point output)) =
      ∑ input ∈ cells, ∫ pair : Parameter × Spatial,
        test pair.2 • inner ℂ vector
            (allocatedCoefficient data word selected target output input pair
              (Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function
              (data.orthogonal pair.1 pair.2) input))
        ∂measure.prod (volume.restrict (disk radius)) := by
  have support := inputDerivative_finite_support inputDimension order rank weight (disk radius)
    (family selected target).domainOpen bound jet function cells core realized selected target
  have derivativeRealized := inputDerivative_realized inputDimension order rank weight (disk radius)
    (family selected target).domainOpen bound jet function cells core realized selected target
  rw [operator_pairing_product_representative (family selected target)
    (inputDerivative inputDimension order rank weight (disk radius) bound jet selected target)
    cells support
    (Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function)
    derivativeRealized output vector test testSmooth.continuous.measurable
    (testSmooth.continuous.memLp_of_hasCompactSupport testCompact)]
  have orthogonalLaw := (familySpec selected target).1
  have coefficientLaw := (familySpec selected target).2.1
  apply Finset.sum_congr rfl
  intro input _membership
  apply integral_congr_ae
  filter_upwards [] with pair
  rw [coefficientLaw, orthogonalLaw]

theorem allocated_integrand_integrable
    {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension order rank weight : ℕ} {radius : ℝ}
    (data : RawKernelData measure inputDimension outputDimension (disk radius))
    (word : Word rank) (bound : rank ≤ order)
    (family : AllocatedFamily measure inputDimension outputDimension (disk radius) rank)
    (familySpec : FamilySpecification data word family)
    (jet : Grad.WeightedJets.GraphGrade inputDimension order weight (disk radius))
    (function : Spatial → CellValues inputDimension) (cells : Finset ℤ)
    (core : Grad.SmoothDensity.CoreLaws inputDimension function cells)
    (realized : Grad.SmoothDensity.Realizes inputDimension (disk radius)
      (.graph order weight) function jet)
    (selected : Finset (Fin rank)) (target : Word (selectedᶜ).card)
    (output input : ℤ) (vector : PhysicalValue outputDimension)
    (test : Spatial → ℝ) (testSmooth : ContDiff ℝ ∞ test)
    (testCompact : HasCompactSupport test) :
    Integrable (fun pair : Parameter × Spatial =>
      test pair.2 • inner ℂ vector
        (allocatedCoefficient data word selected target output input pair
          (Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function
            (data.orthogonal pair.1 pair.2) input)))
      (measure.prod (volume.restrict (disk radius))) := by
  have derivativeRealized := inputDerivative_realized inputDimension order rank weight (disk radius)
    (family selected target).domainOpen bound jet function cells core realized selected target
  have raw := testedCell_representative_integrable (family selected target) output input
    (inputDerivative inputDimension order rank weight (disk radius) bound jet selected target)
    (Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function)
    derivativeRealized test testSmooth.continuous.measurable
    (testSmooth.continuous.memLp_of_hasCompactSupport testCompact) vector
  have orthogonalLaw := (familySpec selected target).1
  have coefficientLaw := (familySpec selected target).2.1
  exact raw.congr (Filter.Eventually.of_forall fun pair => by
    rw [coefficientLaw, orthogonalLaw])

set_option maxHeartbeats 4000000 in
theorem derivativeCandidate_pairing_expansion
    {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension order rank weight : ℕ} {radius : ℝ}
    (data : RawKernelData measure inputDimension outputDimension (disk radius))
    (word : Word rank) (bound : rank ≤ order)
    (family : AllocatedFamily measure inputDimension outputDimension (disk radius) rank)
    (familySpec : FamilySpecification data word family)
    (jet : Grad.WeightedJets.GraphGrade inputDimension order weight (disk radius))
    (function : Spatial → CellValues inputDimension) (cells : Finset ℤ)
    (core : Grad.SmoothDensity.CoreLaws inputDimension function cells)
    (realized : Grad.SmoothDensity.Realizes inputDimension (disk radius)
      (.graph order weight) function jet)
    (output : ℤ) (vector : PhysicalValue outputDimension)
    (test : Spatial → ℝ) (testSmooth : ContDiff ℝ ∞ test)
    (testCompact : HasCompactSupport test) :
    (∫ point in disk radius, test point • inner ℂ vector
      (derivativeCandidate data word bound jet family point output)) =
      ∑ selected : Finset (Fin rank), ∑ target : Word (selectedᶜ).card,
        ∑ input ∈ cells, ∫ pair : Parameter × Spatial,
          test pair.2 • inner ℂ vector
            (allocatedCoefficient data word selected target output input pair
              (Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function
                (data.orthogonal pair.1 pair.2) input))
          ∂measure.prod (volume.restrict (disk radius)) := by
  rw [← Grad.WeakTesting.compactPairing_apply outputDimension (disk radius) output vector test
    testSmooth testCompact]
  change Grad.WeakTesting.compactPairing outputDimension (disk radius) output vector test
      testSmooth testCompact
      (∑ selected : Finset (Fin rank), ∑ target : Word (selectedᶜ).card,
        operator (family selected target) (0, 0) 0
          (inputDerivative inputDimension order rank weight (disk radius) bound jet selected target)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro selected _selectedMembership
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro target _targetMembership
  rw [Grad.WeakTesting.compactPairing_apply]
  exact allocated_operator_pairing data word bound family familySpec jet function cells core realized
    selected target output vector test testSmooth testCompact

theorem allocation_sum_pairing_pointwise
    {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter}
    {inputDimension outputDimension rank : ℕ} {domain : Set Spatial}
    (data : RawKernelData measure inputDimension outputDimension domain)
    (function : Spatial → CellValues inputDimension) (smooth : ContDiff ℝ ∞ function)
    (word : Word rank) (output input : ℤ) (vector : PhysicalValue outputDimension)
    (test : Spatial → ℝ) (pair : Parameter × Spatial) (inside : pair.2 ∈ domain) :
    (∑ selected : Finset (Fin rank), ∑ target : Word (selectedᶜ).card,
      test pair.2 • inner ℂ vector
        (allocatedCoefficient data word selected target output input pair
          (Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function
            (data.orthogonal pair.1 pair.2) input))) =
      test pair.2 • wordDerivative rank word (fun source => inner ℂ vector
        (data.coefficient output input (pair.1, source)
          (function (data.orthogonal pair.1 source) input))) pair.2 := by
  have expansion := productInnerDerivative_expansion data function smooth word output input
    pair.1 pair.2 inside vector
  rw [expansion]
  let functional : PhysicalValue outputDimension →L[ℝ] ℂ :=
    (test pair.2) • (innerSL ℂ vector).restrictScalars ℝ
  change (∑ selected : Finset (Fin rank), ∑ target : Word (selectedᶜ).card,
      functional (allocatedCoefficient data word selected target output input pair
        (Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function
          (data.orthogonal pair.1 pair.2) input))) =
    functional (∑ selected : Finset (Fin rank), ∑ target : Word (selectedᶜ).card,
      allocatedCoefficient data word selected target output input pair
        (Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function
          (data.orthogonal pair.1 pair.2) input))
  symm
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro selected _selectedMembership
  rw [map_sum]

set_option maxHeartbeats 4000000 in
theorem allocation_sum_pairing_integral
    {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension order rank weight : ℕ} {radius : ℝ}
    (data : RawKernelData measure inputDimension outputDimension (disk radius))
    (word : Word rank) (bound : rank ≤ order)
    (family : AllocatedFamily measure inputDimension outputDimension (disk radius) rank)
    (familySpec : FamilySpecification data word family)
    (jet : Grad.WeightedJets.GraphGrade inputDimension order weight (disk radius))
    (function : Spatial → CellValues inputDimension) (cells : Finset ℤ)
    (core : Grad.SmoothDensity.CoreLaws inputDimension function cells)
    (realized : Grad.SmoothDensity.Realizes inputDimension (disk radius)
      (.graph order weight) function jet)
    (output input : ℤ) (vector : PhysicalValue outputDimension)
    (test : Spatial → ℝ) (testSmooth : ContDiff ℝ ∞ test)
    (testCompact : HasCompactSupport test) :
    (∑ selected : Finset (Fin rank), ∑ target : Word (selectedᶜ).card,
      ∫ pair : Parameter × Spatial,
        test pair.2 • inner ℂ vector
          (allocatedCoefficient data word selected target output input pair
            (Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function
              (data.orthogonal pair.1 pair.2) input))
        ∂measure.prod (volume.restrict (disk radius))) =
      ∫ pair : Parameter × Spatial, test pair.2 •
        wordDerivative rank word (fun source => inner ℂ vector
          (data.coefficient output input (pair.1, source)
            (function (data.orthogonal pair.1 source) input))) pair.2
        ∂measure.prod (volume.restrict (disk radius)) := by
  calc
    _ = ∑ selected : Finset (Fin rank),
        ∫ pair : Parameter × Spatial, ∑ target : Word (selectedᶜ).card,
          test pair.2 • inner ℂ vector
            (allocatedCoefficient data word selected target output input pair
              (Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function
                (data.orthogonal pair.1 pair.2) input))
          ∂measure.prod (volume.restrict (disk radius)) := by
      apply Finset.sum_congr rfl
      intro selected _selectedMembership
      symm
      apply integral_finsetSum
      intro target _targetMembership
      exact allocated_integrand_integrable data word bound family familySpec jet function cells core
        realized selected target output input vector test testSmooth testCompact
    _ = ∫ pair : Parameter × Spatial,
        ∑ selected : Finset (Fin rank), ∑ target : Word (selectedᶜ).card,
          test pair.2 • inner ℂ vector
            (allocatedCoefficient data word selected target output input pair
              (Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function
                (data.orthogonal pair.1 pair.2) input))
          ∂measure.prod (volume.restrict (disk radius)) := by
      symm
      apply integral_finsetSum
      intro selected _selectedMembership
      exact integrable_finsetSum Finset.univ fun target _targetMembership =>
        allocated_integrand_integrable data word bound family familySpec jet function cells core
          realized selected target output input vector test testSmooth testCompact
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [Measure.quasiMeasurePreserving_snd.ae
        (ae_restrict_mem data.domainOpen.measurableSet)]
        with pair inside
      exact allocation_sum_pairing_pointwise data function core.1 word output input vector test pair inside

theorem kernelProductDerivative_integrable
    {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension order rank weight : ℕ} {radius : ℝ}
    (data : RawKernelData measure inputDimension outputDimension (disk radius))
    (word : Word rank) (bound : rank ≤ order)
    (family : AllocatedFamily measure inputDimension outputDimension (disk radius) rank)
    (familySpec : FamilySpecification data word family)
    (jet : Grad.WeightedJets.GraphGrade inputDimension order weight (disk radius))
    (function : Spatial → CellValues inputDimension) (cells : Finset ℤ)
    (core : Grad.SmoothDensity.CoreLaws inputDimension function cells)
    (realized : Grad.SmoothDensity.Realizes inputDimension (disk radius)
      (.graph order weight) function jet)
    (output input : ℤ) (vector : PhysicalValue outputDimension)
    (test : Spatial → ℝ) (testSmooth : ContDiff ℝ ∞ test)
    (testCompact : HasCompactSupport test) :
    Integrable (fun pair : Parameter × Spatial => test pair.2 •
      wordDerivative rank word (fun source => inner ℂ vector
        (data.coefficient output input (pair.1, source)
          (function (data.orthogonal pair.1 source) input))) pair.2)
      (measure.prod (volume.restrict (disk radius))) := by
  have allocationIntegrable : Integrable (fun pair : Parameter × Spatial =>
      ∑ selected : Finset (Fin rank), ∑ target : Word (selectedᶜ).card,
        test pair.2 • inner ℂ vector
          (allocatedCoefficient data word selected target output input pair
            (Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function
              (data.orthogonal pair.1 pair.2) input)))
      (measure.prod (volume.restrict (disk radius))) :=
    integrable_finsetSum Finset.univ fun selected _selectedMembership =>
      integrable_finsetSum Finset.univ fun target _targetMembership =>
        allocated_integrand_integrable data word bound family familySpec jet function cells core
          realized selected target output input vector test testSmooth testCompact
  exact allocationIntegrable.congr
    ((Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem data.domainOpen.measurableSet)).mono fun pair inside =>
        allocation_sum_pairing_pointwise data function core.1 word output input vector test pair inside)

theorem kernel_product_ibp_integral
    {Parameter : Type parameterUniverse} [MeasurableSpace Parameter]
    {measure : Measure Parameter} [SigmaFinite measure]
    {inputDimension outputDimension order rank weight : ℕ} {radius : ℝ}
    (data : RawKernelData measure inputDimension outputDimension (disk radius))
    (word : Word rank) (bound : rank ≤ order)
    (family : AllocatedFamily measure inputDimension outputDimension (disk radius) rank)
    (familySpec : FamilySpecification data word family)
    (jet : Grad.WeightedJets.GraphGrade inputDimension order weight (disk radius))
    (function : Spatial → CellValues inputDimension) (cells : Finset ℤ)
    (core : Grad.SmoothDensity.CoreLaws inputDimension function cells)
    (realized : Grad.SmoothDensity.Realizes inputDimension (disk radius)
      (.graph order weight) function jet)
    (output input : ℤ) (vector : PhysicalValue outputDimension)
    (test : Spatial → ℝ) (testSmooth : ContDiff ℝ ∞ test)
    (testCompact : HasCompactSupport test) (testSupported : tsupport test ⊆ disk radius) :
    (∫ pair : Parameter × Spatial, test pair.2 •
      wordDerivative rank word (fun source => inner ℂ vector
        (data.coefficient output input (pair.1, source)
          (function (data.orthogonal pair.1 source) input))) pair.2
      ∂measure.prod (volume.restrict (disk radius))) =
      (-1 : ℂ) ^ rank * ∫ pair : Parameter × Spatial,
        Grad.WeakTesting.orderedTestDerivative rank word test pair.2 • inner ℂ vector
          (data.coefficient output input pair
            (function (data.orthogonal pair.1 pair.2) input))
        ∂measure.prod (volume.restrict (disk radius)) := by
  have derivativeIntegrable := kernelProductDerivative_integrable data word bound family familySpec
    jet function cells core realized output input vector test testSmooth testCompact
  have derivativeTestContinuous :=
    Grad.WeakTesting.orderedTestDerivative_continuous rank word test testSmooth
  have derivativeTestLp :=
    Grad.WeakTesting.orderedTestDerivative_memLp (disk radius) rank word test testSmooth testCompact
  have baseIntegrable := testedCell_representative_integrable data output input
    (Grad.WeightedJets.base inputDimension order (disk radius) (fun _ => weight) jet)
    function realized.1 (Grad.WeakTesting.orderedTestDerivative rank word test)
    derivativeTestContinuous.measurable derivativeTestLp vector
  rw [integral_prod _ derivativeIntegrable, integral_prod _ baseIntegrable, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with parameter
  exact orderedScalar_ibp (disk radius) data.domainOpen rank word test testSmooth testCompact
    testSupported
    (fun source => inner ℂ vector (data.coefficient output input (parameter, source)
      (function (data.orthogonal parameter source) input)))
    (kernelProductInner_smooth data function core.1 output input parameter vector)

set_option maxHeartbeats 4000000 in
theorem coreIBP : CoreIBPGoal.{parameterUniverse} := by
  intro Parameter _ measure _ inputDimension outputDimension order rank weight radius _positiveRadius
    data word bound family familySpec jet function cells core realized output vector test testSmooth
    testCompact testSupported
  have expansion := derivativeCandidate_pairing_expansion data word bound family familySpec jet
    function cells core realized output vector test testSmooth testCompact
  have baseSupport := base_finite_support inputDimension order weight (disk radius) jet function cells
    core realized
  have derivativeTestContinuous :=
    Grad.WeakTesting.orderedTestDerivative_continuous rank word test testSmooth
  have derivativeTestLp :=
    Grad.WeakTesting.orderedTestDerivative_memLp (disk radius) rank word test testSmooth testCompact
  have basePairing := operator_pairing_product_representative data
    (Grad.WeightedJets.base inputDimension order (disk radius) (fun _ => weight) jet)
    cells baseSupport function realized.1 output vector
    (Grad.WeakTesting.orderedTestDerivative rank word test)
    derivativeTestContinuous.measurable derivativeTestLp
  calc
    (∫ point in disk radius, test point • inner ℂ vector
        (derivativeCandidate data word bound jet family point output)) =
        ∑ selected : Finset (Fin rank), ∑ target : Word (selectedᶜ).card,
          ∑ input ∈ cells, ∫ pair : Parameter × Spatial,
            test pair.2 • inner ℂ vector
              (allocatedCoefficient data word selected target output input pair
                (Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function
                  (data.orthogonal pair.1 pair.2) input))
            ∂measure.prod (volume.restrict (disk radius)) := expansion
    _ = ∑ selected : Finset (Fin rank), ∑ input ∈ cells,
          ∑ target : Word (selectedᶜ).card, ∫ pair : Parameter × Spatial,
            test pair.2 • inner ℂ vector
              (allocatedCoefficient data word selected target output input pair
                (Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function
                  (data.orthogonal pair.1 pair.2) input))
            ∂measure.prod (volume.restrict (disk radius)) := by
      apply Finset.sum_congr rfl
      intro selected _selectedMembership
      rw [Finset.sum_comm]
    _ = ∑ input ∈ cells, ∑ selected : Finset (Fin rank),
          ∑ target : Word (selectedᶜ).card, ∫ pair : Parameter × Spatial,
            test pair.2 • inner ℂ vector
              (allocatedCoefficient data word selected target output input pair
                (Grad.Mollifier.Pointwise.orderedDerivative (selectedᶜ).card target function
                  (data.orthogonal pair.1 pair.2) input))
            ∂measure.prod (volume.restrict (disk radius)) := by
      rw [Finset.sum_comm]
    _ = ∑ input ∈ cells, ∫ pair : Parameter × Spatial, test pair.2 •
          wordDerivative rank word (fun source => inner ℂ vector
            (data.coefficient output input (pair.1, source)
              (function (data.orthogonal pair.1 source) input))) pair.2
          ∂measure.prod (volume.restrict (disk radius)) := by
      apply Finset.sum_congr rfl
      intro input _inputMembership
      exact allocation_sum_pairing_integral data word bound family familySpec jet function cells core
        realized output input vector test testSmooth testCompact
    _ = ∑ input ∈ cells, (-1 : ℂ) ^ rank *
          ∫ pair : Parameter × Spatial,
            Grad.WeakTesting.orderedTestDerivative rank word test pair.2 • inner ℂ vector
              (data.coefficient output input pair
                (function (data.orthogonal pair.1 pair.2) input))
            ∂measure.prod (volume.restrict (disk radius)) := by
      apply Finset.sum_congr rfl
      intro input _inputMembership
      exact kernel_product_ibp_integral data word bound family familySpec jet function cells core
        realized output input vector test testSmooth testCompact testSupported
    _ = (-1 : ℂ) ^ rank * ∑ input ∈ cells,
          ∫ pair : Parameter × Spatial,
            Grad.WeakTesting.orderedTestDerivative rank word test pair.2 • inner ℂ vector
              (data.coefficient output input pair
                (function (data.orthogonal pair.1 pair.2) input))
            ∂measure.prod (volume.restrict (disk radius)) := by
      rw [Finset.mul_sum]
    _ = (-1 : ℂ) ^ rank * ∫ point in disk radius,
          Grad.WeakTesting.orderedTestDerivative rank word test point • inner ℂ vector
            (operator data (0, 0) 0
              (Grad.WeightedJets.base inputDimension order (disk radius) (fun _ => weight) jet)
              point output) := by
      rw [basePairing]

end Grad.RepresentedKernel.WeakDerivatives
