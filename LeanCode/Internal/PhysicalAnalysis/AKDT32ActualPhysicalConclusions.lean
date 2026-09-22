import AKDT31ActualSignedStabilizer

noncomputable section
open Set

namespace Grad.PhysicalGeometry
open Grad.MainTarget Grad.PhysicalFamily
open Grad.PhysicalFamily.IntegerSampling Grad.PhysicalFamily.SampledSmoothFamily
open Grad.PhysicalFamily.SampledFullGeometry

/-- Every clause of the unchanged physical target holds for the SAME sampled
representatives of an actual cell solution family after one integer threshold. -/
theorem exists_sampledPhysicalConclusionsThreshold
    (length : ℝ) (positive : 0 < length) (family : CellSolutionFamily length) :
    ∃ firstPeriod : ℕ, 1 ≤ firstPeriod ∧ ∀ period : ℕ, firstPeriod ≤ period →
      sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero ∧
      ∀ (epsilonIn : sampledEpsilon period ∈ Ioo (-family.epsilonZero) family.epsilonZero)
        (potential : ℝ) (parameter : Icc family.lower family.upper),
        PhysicalConclusions (sampledRepresentativeFamily length family period epsilonIn potential parameter) length period := by
  obtain ⟨fieldPeriod, fieldPositive, fieldThreshold⟩ := exists_sampledFoliatedFieldsThreshold length positive family
  obtain ⟨derivativePeriod, _, derivativeThreshold⟩ := exists_sampledPositionFullDerivativeThreshold length positive family
  refine ⟨max fieldPeriod derivativePeriod, fieldPositive.trans (le_max_left _ _), ?_⟩
  intro period after
  have fields := fieldThreshold period ((le_max_left _ _).trans after)
  have derivative := derivativeThreshold period ((le_max_right _ _).trans after)
  have periodPositive : 0 < period := lt_of_lt_of_le Nat.zero_lt_one
    (fieldPositive.trans ((le_max_left _ _).trans after))
  refine ⟨fields.1, ?_⟩
  intro epsilonIn potential parameter
  obtain ⟨valid, magnetic, pressure, magneticSmooth, pressureSmooth, magneticNear, pressureNear, same,
    equations, tangent, axisInterior, criticalSet, magneticZero, tori, regular, foliation⟩ :=
    fields.2 epsilonIn potential parameter
  refine ⟨valid, magnetic, pressure, magneticNear, pressureNear, same,
    (fun point membership => equations point (interior_subset membership)), tangent, axisInterior,
    criticalSet, magneticZero, tori, regular, foliation, ?_⟩
  intro orthogonal translation
  exact actual_signed_stabilizer length positive family period periodPositive epsilonIn potential parameter
    valid (derivative.2 parameter) magnetic pressure magneticSmooth pressureSmooth pressureNear same orthogonal translation

end Grad.PhysicalGeometry
