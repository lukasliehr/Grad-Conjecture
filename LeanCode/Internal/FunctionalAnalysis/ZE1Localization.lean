import ZE1Field

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue CellValues FieldL2 DomainL2)
open scoped ContDiff Topology

namespace Grad.WeightedJets.ZeroExtension

def SupportedField (Value : Type*) [NormedAddCommGroup Value] (domain support : Set Spatial)
    (field : DomainL2 Value domain) : Prop :=
  ∀ᵐ point ∂volume.restrict domain, point ∉ support → field point = 0

structure TestLocalizer (domain support : Set Spatial) where
  cutoff : TestFunction domain
  one_near : ∀ point ∈ support, cutoff.toFun =ᶠ[𝓝 point] fun _ => (1 : ℝ)

def localizeTest {domain support : Set Spatial} (localizer : TestLocalizer domain support)
    (test : TestFunction Set.univ) : TestFunction domain where
  toFun := fun point => localizer.cutoff.toFun point * test.toFun point
  smooth := localizer.cutoff.smooth.mul test.smooth
  compact := localizer.cutoff.compact.mul_right
  supported := tsupport_mul_subset_left.trans localizer.cutoff.supported

theorem localizeTest_germ {domain support : Set Spatial} (localizer : TestLocalizer domain support)
    (test : TestFunction Set.univ) (point : Spatial) (inside : point ∈ support) :
    (localizeTest localizer test).toFun =ᶠ[𝓝 point] test.toFun := by
  filter_upwards [localizer.one_near point inside] with source oneAt
  change localizer.cutoff.toFun source * test.toFun source = test.toFun source
  rw [oneAt, one_mul]

theorem localizeTest_derivative {domain support : Set Spatial}
    (localizer : TestLocalizer domain support) (test : TestFunction Set.univ)
    (rank : ℕ) (word : Fin rank → Fin 2) (point : Spatial) (inside : point ∈ support) :
    Grad.WeakTesting.orderedTestDerivative rank word (localizeTest localizer test).toFun point =
      Grad.WeakTesting.orderedTestDerivative rank word test.toFun point :=
  congrArg (fun multilinear => multilinear (fun position => spatialDirection (word position)))
    ((localizeTest_germ localizer test point inside).iteratedFDeriv ℝ rank).eq_of_nhds

theorem fieldExtension_inverse (dimension : ℕ) (domain : Set Spatial)
    (measurable : MeasurableSet domain) (power : ℕ) (field : FieldL2 dimension domain) :
    fieldExtension (CellValues dimension) domain measurable
        (Grad.CellWeights.inverseFieldCLM dimension domain power field) =
      Grad.CellWeights.inverseFieldCLM dimension Set.univ power
        (fieldExtension (CellValues dimension) domain measurable field) :=
  fieldExtension_naturality (CellValues dimension) domain measurable
    (Grad.CellWeights.inverseCellCLM (PhysicalValue dimension) power) field

theorem integral_extension (dimension : ℕ) (domain : Set Spatial)
    (measurable : MeasurableSet domain) (field : FieldL2 dimension domain)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : Spatial → ℝ) :
    (∫ point in (Set.univ : Set Spatial), test point • inner ℂ vector
      (fieldExtension (CellValues dimension) domain measurable field point cell)) =
      ∫ point in domain, test point • inner ℂ vector (field point cell) := by
  calc
    _ = ∫ point in (Set.univ : Set Spatial),
        domain.indicator (fun source => test source • inner ℂ vector (field source cell)) point := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae
        (fieldExtension_ae (CellValues dimension) domain measurable field)] with point represented
      rw [represented]
      by_cases inside : point ∈ domain
      · simp only [Set.indicator_of_mem inside]
      · simp only [Set.indicator_of_notMem inside, lp.coeFn_zero, Pi.zero_apply, inner_zero_right, smul_zero]
    _ = ∫ point : Spatial,
        domain.indicator (fun source => test source • inner ℂ vector (field source cell)) point := by
      rw [Measure.restrict_univ]
    _ = _ := integral_indicator measurable

theorem integral_supported_congr (dimension : ℕ) (domain support : Set Spatial)
    (field : FieldL2 dimension domain) (supported : SupportedField (CellValues dimension) domain support field)
    (cell : ℤ) (vector : PhysicalValue dimension) (first second : Spatial → ℝ)
    (same : Set.EqOn first second support) :
    (∫ point in domain, first point • inner ℂ vector (field point cell)) =
      ∫ point in domain, second point • inner ℂ vector (field point cell) := by
  apply integral_congr_ae
  filter_upwards [supported] with point zeroAt
  by_cases inside : point ∈ support
  · rw [same inside]
  · have zero : field point cell = 0 := by
      simpa only [lp.coeFn_zero, Pi.zero_apply] using
        congrArg (fun cells : CellValues dimension => cells cell) (zeroAt inside)
    rw [zero, inner_zero_right, smul_zero, smul_zero]

theorem testPairing_extension {domain support : Set Spatial} (dimension : ℕ)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (field : FieldL2 dimension domain) (supported : SupportedField (CellValues dimension) domain support field)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction Set.univ) :
    testPairing dimension Set.univ cell vector test
        (fieldExtension (CellValues dimension) domain measurable field) =
      testPairing dimension domain cell vector (localizeTest localizer test) field := by
  rw [testPairing_apply, testPairing_apply, integral_extension]
  apply integral_supported_congr dimension domain support field supported cell vector
  intro point inside
  exact (localizeTest_germ localizer test point inside).eq_of_nhds.symm

theorem derivativeTestPairing_extension {domain support : Set Spatial} (dimension order : ℕ)
    (measurable : MeasurableSet domain) (localizer : TestLocalizer domain support)
    (field : FieldL2 dimension domain) (supported : SupportedField (CellValues dimension) domain support field)
    (index : JetIndex order) (cell : ℤ) (vector : PhysicalValue dimension) (test : TestFunction Set.univ) :
    derivativeTestPairing dimension order Set.univ index cell vector test
        (fieldExtension (CellValues dimension) domain measurable field) =
      derivativeTestPairing dimension order domain index cell vector (localizeTest localizer test) field := by
  rw [derivativeTestPairing_apply, derivativeTestPairing_apply, integral_extension]
  apply integral_supported_congr dimension domain support field supported cell vector
  intro point inside
  exact (localizeTest_derivative localizer test (degree index) (derivativeWord index) point inside).symm

end Grad.WeightedJets.ZeroExtension
