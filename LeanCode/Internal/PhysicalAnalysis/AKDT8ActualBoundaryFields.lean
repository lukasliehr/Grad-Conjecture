import AKDT7ActualFieldZeroSets

noncomputable section
open Set
open scoped ContDiff

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient Grad.PhysicalEquilibrium
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledFullGeometry

/-- The literal family supplies SAME canonical smooth fields with both MHS
equations, actual boundary tangency, and the exact axis and zero sets. -/
theorem exists_sampledBoundaryFieldsThreshold
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
          (∀ point ∈ body, magnetic point = 0 ↔ point ∈ axis) := by
  obtain ⟨fieldPeriod, fieldPositive, fieldThreshold⟩ := exists_sampledMHSFieldsThreshold length positive family
  obtain ⟨derivativePeriod, _, derivativeThreshold⟩ := exists_sampledPositionFullDerivativeThreshold length positive family
  refine ⟨max fieldPeriod derivativePeriod, fieldPositive.trans (le_max_left _ _), ?_⟩
  intro period after
  have fields := fieldThreshold period ((le_max_left _ _).trans after)
  have derivative := derivativeThreshold period ((le_max_right _ _).trans after)
  refine ⟨fields.1, ?_⟩
  intro epsilonIn potential parameter
  obtain ⟨valid, magnetic, pressure, magneticSmooth, pressureSmooth, magneticNear, pressureNear, same, equations⟩ :=
    fields.2 epsilonIn potential parameter
  have injective := derivative.2 parameter
  have zeroSets := actual_field_zero_sets length family period epsilonIn potential parameter valid injective
    magnetic pressure magneticSmooth pressureSmooth same
  exact ⟨valid, magnetic, pressure, magneticSmooth, pressureSmooth, magneticNear, pressureNear, same, equations,
    actual_boundary_tangent length family period epsilonIn potential parameter valid injective magnetic (fun argument => (same argument).1),
    actual_axis_subset_interior length family period epsilonIn potential parameter valid injective, zeroSets.1, zeroSets.2⟩

end Grad.PhysicalGeometry
