import AKDL5ActualSampledLifts

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalAmbient
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalFamily.IntegerSampling
open Grad.PhysicalFamily.SampledSmoothFamily Grad.PhysicalFamily.SampledConfigurationRegularity
open Grad.PhysicalFamily.SampledFullGeometry Grad.PhysicalFamily.SampledGlobalEmbedding.Consumer
open Grad.MainAssembly.SampledAxisBasics

/-- The literal canonical sampled configuration has actual smooth ambient
magnetic and pressure extensions for every period above one threshold.
No ambient extension, inverse chart or geometric regularity premise remains. -/
theorem exists_sampledGlobalFieldsThreshold
    (cellLength : ℝ) (positive : 0 < cellLength) (family : CellSolutionFamily cellLength) :
    ∃ firstPeriod : ℕ, 1 ≤ firstPeriod ∧ ∀ period : ℕ, firstPeriod ≤ period →
      sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero ∧
      ∀ (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
        (potential : ℝ) (parameter : Icc family.lower family.upper),
        let configuration := sampledRepresentativeFamily cellLength family period epsilonIn potential parameter
        IsConfiguration .smooth configuration ∧
        ∃ magnetic : Vec → Vec, ∃ pressure : Vec → ℝ,
          ContDiff ℝ ∞ magnetic ∧ ContDiff ℝ ∞ pressure ∧
          SmoothNear (range configuration.position) magnetic ∧
          SmoothNear (range configuration.position) pressure ∧
          ∀ point : Reference,
            magnetic (configuration.position point) = configuration.magnetic point ∧
            pressure (configuration.position point) = configuration.pressure point := by
  obtain ⟨configurationPeriod, configurationPositive, configurationThreshold⟩ :=
    exists_sampledRepresentativeConfigurationThreshold cellLength positive family
  obtain ⟨derivativePeriod, _, derivativeThreshold⟩ :=
    exists_sampledPositionFullDerivativeThreshold cellLength positive family
  refine ⟨max configurationPeriod derivativePeriod,
    configurationPositive.trans (le_max_left _ _), ?_⟩
  intro period after
  have configurationResult := configurationThreshold period ((le_max_left _ _).trans after)
  have derivativeResult := derivativeThreshold period ((le_max_right _ _).trans after)
  refine ⟨configurationResult.1, ?_⟩
  intro epsilonIn potential parameter
  let configuration := sampledRepresentativeFamily cellLength family period epsilonIn potential parameter
  have configurationValid : IsConfiguration .smooth configuration := configurationResult.2 epsilonIn potential parameter
  have embedding := configurationValid.1.2.1
  have smooth := sampled_actual_lifts_smooth cellLength family period epsilonIn potential parameter
  have values := sampled_actual_lifts_values cellLength family period epsilonIn potential parameter
  have derivative (argument : ClosedDisk × ℝ) :
      Function.Injective (fderiv ℝ (sampledPositionCoordinateValue cellLength family period parameter.val)
        (referenceCoverPoint argument)) :=
    derivativeResult.2 parameter argument.1.val argument.1.property argument.2
  obtain ⟨magnetic, magneticSmooth, magneticSame⟩ := exists_ambient_smooth_field
    configuration.position configuration.magnetic embedding
    (sampledPositionCoordinateValue cellLength family period parameter.val)
    (sampledMagneticCoordinateValue cellLength family period parameter.val)
    (sampledAmbientCollar family) (sampledAmbientCollar_isOpen family) (sampledAmbientCollar_contains family)
    smooth.1 smooth.2.1 (fun argument => (values argument).1) (fun argument => (values argument).2.1) derivative
  obtain ⟨pressure, pressureSmooth, pressureSame⟩ := exists_ambient_smooth_field
    configuration.position configuration.pressure embedding
    (sampledPositionCoordinateValue cellLength family period parameter.val)
    (sampledPressureCoordinateValue potential)
    (sampledAmbientCollar family) (sampledAmbientCollar_isOpen family) (sampledAmbientCollar_contains family)
    smooth.1 smooth.2.2 (fun argument => (values argument).1) (fun argument => (values argument).2.2) derivative
  exact ⟨configurationValid, magnetic, pressure, magneticSmooth, pressureSmooth,
    ⟨univ, isOpen_univ, subset_univ _, magneticSmooth.contDiffOn⟩,
    ⟨univ, isOpen_univ, subset_univ _, pressureSmooth.contDiffOn⟩,
    fun point => ⟨magneticSame point, pressureSame point⟩⟩

/-- Exact ambient-field clauses of the unchanged main target. -/
theorem exists_sampledAmbientFieldsThreshold
    (cellLength : ℝ) (positive : 0 < cellLength) (family : CellSolutionFamily cellLength) :
    ∃ firstPeriod : ℕ, 1 ≤ firstPeriod ∧ ∀ period : ℕ, firstPeriod ≤ period →
      sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero ∧
      ∀ (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
        (potential : ℝ) (parameter : Icc family.lower family.upper),
        let configuration := sampledRepresentativeFamily cellLength family period epsilonIn potential parameter
        IsConfiguration .smooth configuration ∧
        ∃ magnetic : Vec → Vec, ∃ pressure : Vec → ℝ,
          SmoothNear (range configuration.position) magnetic ∧
          SmoothNear (range configuration.position) pressure ∧
          ∀ point : Reference,
            magnetic (configuration.position point) = configuration.magnetic point ∧
            pressure (configuration.position point) = configuration.pressure point := by
  obtain ⟨firstPeriod, firstPositive, threshold⟩ :=
    exists_sampledGlobalFieldsThreshold cellLength positive family
  refine ⟨firstPeriod, firstPositive, ?_⟩
  intro period after
  have result := threshold period after
  refine ⟨result.1, ?_⟩
  intro epsilonIn potential parameter
  obtain ⟨valid, magnetic, pressure, _, _, magneticNear, pressureNear, agrees⟩ :=
    result.2 epsilonIn potential parameter
  exact ⟨valid, magnetic, pressure, magneticNear, pressureNear, agrees⟩

end Grad.PhysicalAmbient
