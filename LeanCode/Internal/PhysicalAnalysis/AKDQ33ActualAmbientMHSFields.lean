import AKDQ32ActualClosedCylinderDivergenceZero

noncomputable section
set_option maxHeartbeats 1200000
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily Grad.PhysicalAmbient
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledConfigurationRegularity Grad.PhysicalFamily.SampledFullGeometry
open Grad.MainAssembly.SampledAxisBasics Grad.MainAssembly.PhysicalNormalHessian

/-- The actual literal family gives globally smooth canonical ambient
fields satisfying BOTH literal MHS equations on the entire closed body. -/
theorem exists_sampledMHSFieldsThreshold
    (length : ℝ) (positive : 0 < length) (family : CellSolutionFamily length) :
    ∃ firstPeriod : ℕ, 1 ≤ firstPeriod ∧ ∀ period : ℕ, firstPeriod ≤ period →
      sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero ∧
      ∀ (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
        (potential : ℝ) (parameter : Icc family.lower family.upper),
        let configuration := sampledRepresentativeFamily length family period epsilonIn potential parameter
        IsConfiguration .smooth configuration ∧
        ∃ magnetic : Vec → Vec, ∃ pressure : Vec → ℝ,
          ContDiff ℝ ∞ magnetic ∧ ContDiff ℝ ∞ pressure ∧
          SmoothNear (range configuration.position) magnetic ∧
          SmoothNear (range configuration.position) pressure ∧
          (∀ point : Reference,
            magnetic (configuration.position point) = configuration.magnetic point ∧
            pressure (configuration.position point) = configuration.pressure point) ∧
          ∀ point ∈ range configuration.position,
            cross (magnetic point) (curl magnetic point) + gradient pressure point = 0 ∧
              divergence magnetic point = 0 := by
  obtain ⟨fieldPeriod, fieldPositive, fieldThreshold⟩ := exists_sampledForceFieldsThreshold length positive family
  obtain ⟨derivativePeriod, _, derivativeThreshold⟩ := exists_sampledPositionFullDerivativeThreshold length positive family
  refine ⟨max fieldPeriod derivativePeriod, fieldPositive.trans (le_max_left _ _), ?_⟩
  intro period after
  have fields := fieldThreshold period ((le_max_left _ _).trans after)
  have derivative := derivativeThreshold period ((le_max_right _ _).trans after)
  have periodPositive : 0 < period := lt_of_lt_of_le Nat.zero_lt_one
    (fieldPositive.trans ((le_max_left _ _).trans after))
  refine ⟨fields.1, ?_⟩
  intro epsilonIn potential parameter
  obtain ⟨valid, magnetic, pressure, magneticSmooth, pressureSmooth, magneticNear, pressureNear, same, force⟩ :=
    fields.2 epsilonIn potential parameter
  refine ⟨valid, magnetic, pressure, magneticSmooth, pressureSmooth, magneticNear, pressureNear, same, ?_⟩
  intro point pointIn
  refine ⟨force point pointIn, ?_⟩
  obtain ⟨reference, rfl⟩ := pointIn
  obtain ⟨cover, rfl⟩ := referenceCover_surjective reference
  have zero := actual_divergence_zero_closedCylinder length family period periodPositive epsilonIn potential parameter
    magnetic pressure magneticSmooth pressureSmooth same (derivative.2 parameter) cover.1.val cover.1.property cover.2
  have positionSame := (sampled_actual_lifts_values length family period epsilonIn potential parameter cover).1
  change divergence magnetic (sampledPositionCoordinateValue length family period parameter.val (referenceCoverPoint cover)) = 0 at zero
  rw [positionSame] at zero
  exact zero

end Grad.PhysicalEquilibrium
