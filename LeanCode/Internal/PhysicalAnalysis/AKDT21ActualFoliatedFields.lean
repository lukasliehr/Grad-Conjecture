import AKDT20ActualPressureFoliation

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient Grad.PhysicalEquilibrium
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledFullGeometry

/-- The literal family supplies SAME canonical smooth MHS fields, actual
boundary and axis geometry, every nonempty regular pressure torus, and the
full pressure foliation with its radius-one boundary leaf. -/
theorem exists_sampledFoliatedFieldsThreshold
    (length : ℝ) (positive : 0 < length) (family : CellSolutionFamily length) :
    ∃ firstPeriod : ℕ, 1 ≤ firstPeriod ∧ ∀ period : ℕ, firstPeriod ≤ period →
      sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero ∧
      ∀ (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
        (potential : ℝ) (parameter : Icc family.lower family.upper),
        let configuration := sampledRepresentativeFamily length family period epsilonIn potential parameter
        let body := range configuration.position
        let axis := roundAxis ((period : ℝ) * length)
        IsConfiguration .smooth configuration ∧
        ∃ magnetic : Vec → Vec, ∃ pressure : Vec → ℝ,
          ContDiff ℝ ∞ magnetic ∧ ContDiff ℝ ∞ pressure ∧
          SmoothNear body magnetic ∧ SmoothNear body pressure ∧
          (∀ point : Reference,
            magnetic (configuration.position point) = configuration.magnetic point ∧
            pressure (configuration.position point) = configuration.pressure point) ∧
          (∀ point ∈ body,
            cross (magnetic point) (curl magnetic point) + gradient pressure point = 0 ∧
              divergence magnetic point = 0) ∧
          (∀ point ∈ frontier body, TangentTo (frontier body) point (magnetic point)) ∧
          axis ⊆ interior body ∧
          {point | point ∈ body ∧ fderiv ℝ pressure point = 0} = axis ∧
          (∀ point ∈ body, magnetic point = 0 ↔ point ∈ axis) ∧
          (∀ value, (pressureLevel body pressure value).Nonempty → IsRegularLevel body pressure value →
            IsEmbeddedTorus (pressureLevel body pressure value)) ∧
          (∀ point ∈ body \ axis, IsRegularLevel body pressure (pressure point)) ∧
          IsPressureFoliation body axis pressure := by
  obtain ⟨fieldPeriod, fieldPositive, fieldThreshold⟩ := exists_sampledBoundaryFieldsThreshold length positive family
  obtain ⟨derivativePeriod, _, derivativeThreshold⟩ := exists_sampledPositionFullDerivativeThreshold length positive family
  refine ⟨max fieldPeriod derivativePeriod, fieldPositive.trans (le_max_left _ _), ?_⟩
  intro period after
  have fields := fieldThreshold period ((le_max_left _ _).trans after)
  have derivative := derivativeThreshold period ((le_max_right _ _).trans after)
  refine ⟨fields.1, ?_⟩
  intro epsilonIn potential parameter
  obtain ⟨valid, magnetic, pressure, magneticSmooth, pressureSmooth, magneticNear, pressureNear, same, equations, tangent, axisInterior, criticalSet, magneticZero⟩ :=
    fields.2 epsilonIn potential parameter
  have injective := derivative.2 parameter
  have regular := actual_regular_pressure_levels length family period epsilonIn potential parameter valid injective
    magnetic pressure magneticSmooth pressureSmooth same
  refine ⟨valid, magnetic, pressure, magneticSmooth, pressureSmooth, magneticNear, pressureNear, same, equations,
    tangent, axisInterior, criticalSet, magneticZero, ?_, regular.2.2,
    actual_pressure_foliation length family period epsilonIn potential parameter valid injective
      magnetic pressure magneticSmooth pressureSmooth same⟩
  intro value nonempty isRegular
  obtain ⟨radius, rfl⟩ := regular.2.1 value nonempty isRegular
  exact actual_pressure_embedded_torus length family period epsilonIn potential parameter valid injective
    pressure (fun argument => (same argument).2) radius

end Grad.PhysicalGeometry
