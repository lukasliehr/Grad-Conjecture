import Q23MixedAffineGenuine
import QY36RootSeedGenuine
import QYP13PhysicalInnerFamily
import QYP22PhysicalTransferGenuine
import QY16MixedOuterIdentification

noncomputable section

set_option maxRecDepth 5000
set_option maxHeartbeats 4000000

open Set Filter
open scoped Topology

namespace Grad.PhysicalCoordinates

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.Constraints
open Grad.NonlinearQuotientBounds Grad.MixedQuotientComposition
open Grad.Constraints.Seed

/-- The coordinate-correct mixed Q23 inner family is its genuine
newest-last directional derivative tower on the full literal core domain. -/
theorem physicalMixedInnerFamily_genuine
    (parameters : PhaseParameters) (reference : Seed.Parameters)
    (insideR : reference ∈ Seed.parameterDomain) (order : ℕ)
    (base : Input parameters) (directions : Fin (order + 1) → Input parameters)
    (admissible : CoreAdmissible base) :
    IsStateDirectionalDerivative
      (fun point => physicalMixedInnerFamily parameters reference insideR order point
        (fun position => directions position.castSucc))
      base (directions (Fin.last order))
      (physicalMixedInnerFamily parameters reference insideR (order + 1)
        base directions) := by
  intro grade
  let oldDirections : Fin order → Input parameters :=
    fun position => directions position.castSucc
  let newest := directions (Fin.last order)
  let scalarCurve := fun t : ℝ =>
    referenceScalar order (base + t • newest).2
      (fun position => (oldDirections position).2)
  let scalarDerivative :=
    referenceScalar (order + 1) base.2 (fun position => (directions position).2)
  let rootCurve := fun t : ℝ =>
    q23MixedRootSeedField parameters order (base + t • newest) oldDirections
  let rootDerivative := q23MixedRootSeedField parameters (order + 1) base directions
  let tangentCurve := fun t : ℝ =>
    q23MixedTangentAffine parameters order (base + t • newest) oldDirections
  let tangentDerivative := q23MixedTangentAffine parameters (order + 1) base directions
  let transferCurve := fun t : ℝ =>
    toPhysicalCore parameters
      (q23MixedTransferredVector parameters reference insideR order
        (base + t • newest) oldDirections)
  let transferDerivative := toPhysicalCore parameters
    (q23MixedTransferredVector parameters reference insideR (order + 1) base directions)
  let fieldCurve := fun t : ℝ => rootCurve t + tangentCurve t + transferCurve t
  let fieldDerivative := rootDerivative + tangentDerivative + transferDerivative
  let seedScalarCurve := fun t : ℝ =>
    q23SeedScalarDirectionalCoreDerivative parameters order (base + t • newest).1
      (fun position => (oldDirections position).1)
  let seedScalarDerivative :=
    q23SeedScalarDirectionalCoreDerivative parameters (order + 1) base.1
      (fun position => (directions position).1)
  let potentialCurve := fun t : ℝ =>
    q23MixedPotentialAffine parameters order (base + t • newest) oldDirections
  let potentialDerivative :=
    q23MixedPotentialAffine parameters (order + 1) base directions
  let totalPotentialCurve := fun t : ℝ => seedScalarCurve t + potentialCurve t
  let totalPotentialDerivative := seedScalarDerivative + potentialDerivative
  have scalarGenuine : Tendsto (fun t : ℝ =>
      ‖(t : ℂ)⁻¹ * (scalarCurve t - scalarCurve 0) - scalarDerivative‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [scalarCurve, scalarDerivative, oldDirections, newest,
      zero_smul ℝ (directions (Fin.last order)), add_zero] using
      q23ReferenceScalar_genuine order base directions
  have rootGenuine : Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ • (rootCurve t - rootCurve 0)) - rootDerivative))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [rootCurve, rootDerivative, oldDirections, newest,
      zero_smul ℝ (directions (Fin.last order)), add_zero] using
      q23MixedRootSeedField_genuine parameters order base directions
        admissible.1 admissible.2 grade
  have tangentGenuine : Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ • (tangentCurve t - tangentCurve 0)) - tangentDerivative))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [tangentCurve, tangentDerivative, oldDirections, newest,
      zero_smul ℝ (directions (Fin.last order)), add_zero] using
      q23MixedTangentAffine_genuine parameters order grade base directions
  have transferGenuine : Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ • (transferCurve t - transferCurve 0)) - transferDerivative))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [transferCurve, transferDerivative, oldDirections, newest,
      zero_smul ℝ (directions (Fin.last order)), add_zero] using
      physicalMixedTransferredVector_genuine parameters reference insideR order
        base directions admissible.1 grade
  have rootTangentGenuine := q23OriginalGrade_add_genuine
    rootCurve tangentCurve rootDerivative tangentDerivative rootGenuine tangentGenuine
  have fieldGenuine : Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ • (fieldCurve t - fieldCurve 0)) - fieldDerivative))
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    exact q23OriginalGrade_add_genuine
      (fun t => rootCurve t + tangentCurve t) transferCurve
      (rootDerivative + tangentDerivative) transferDerivative
      rootTangentGenuine transferGenuine
  have seedScalarGenuine : Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ • (seedScalarCurve t - seedScalarCurve 0)) -
        seedScalarDerivative)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [seedScalarCurve, seedScalarDerivative, oldDirections, newest,
      zero_smul ℝ (directions (Fin.last order)), add_zero] using
      q23SeedScalarDirectionalCoreDerivative_genuine parameters order grade
        base directions admissible.1
  have potentialGenuine : Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ • (potentialCurve t - potentialCurve 0)) -
        potentialDerivative)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [potentialCurve, potentialDerivative, oldDirections, newest,
      zero_smul ℝ (directions (Fin.last order)), add_zero] using
      q23MixedPotentialAffine_genuine parameters order grade base directions
  have totalPotentialGenuine : Tendsto (fun t : ℝ => originalGradeNorm grade
      (((t : ℂ)⁻¹ • (totalPotentialCurve t - totalPotentialCurve 0)) -
        totalPotentialDerivative)) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    q23OriginalGrade_add_genuine seedScalarCurve potentialCurve
      seedScalarDerivative potentialDerivative seedScalarGenuine potentialGenuine
  have total := (scalarGenuine.add fieldGenuine).add totalPotentialGenuine
  have familyCurve : ∀ t : ℝ,
      physicalMixedInnerFamily parameters reference insideR order
          (base + t • newest) oldDirections =
        (scalarCurve t, fieldCurve t, totalPotentialCurve t) := by
    intro t
    rfl
  have familyBase :
      physicalMixedInnerFamily parameters reference insideR order base oldDirections =
        (scalarCurve 0, fieldCurve 0, totalPotentialCurve 0) := by
    rw [← familyCurve 0]
    simp only [zero_smul ℝ newest, add_zero]
  have familyDerivative :
      physicalMixedInnerFamily parameters reference insideR (order + 1) base directions =
        (scalarDerivative, fieldDerivative, totalPotentialDerivative) := by
    rfl
  have expression : ∀ t : ℝ,
      stateNorm grade
        (((t : ℂ)⁻¹ •
          (physicalMixedInnerFamily parameters reference insideR order
              (base + t • newest) oldDirections -
            physicalMixedInnerFamily parameters reference insideR order
              base oldDirections)) -
          physicalMixedInnerFamily parameters reference insideR (order + 1)
            base directions) =
        ‖(t : ℂ)⁻¹ * (scalarCurve t - scalarCurve 0) - scalarDerivative‖ +
          originalGradeNorm grade
            (((t : ℂ)⁻¹ • (fieldCurve t - fieldCurve 0)) - fieldDerivative) +
          originalGradeNorm grade
            (((t : ℂ)⁻¹ • (totalPotentialCurve t - totalPotentialCurve 0)) -
              totalPotentialDerivative) := by
    intro t
    rw [familyCurve t, familyBase, familyDerivative]
    change
      ‖(t : ℂ)⁻¹ * (scalarCurve t - scalarCurve 0) - scalarDerivative‖ +
          originalGradeNorm grade
            (((t : ℂ)⁻¹ • (fieldCurve t - fieldCurve 0)) - fieldDerivative) +
        originalGradeNorm grade
          (((t : ℂ)⁻¹ • (totalPotentialCurve t - totalPotentialCurve 0)) -
            totalPotentialDerivative) = _
    rfl
  have totalZero : Tendsto (fun t : ℝ =>
      (‖(t : ℂ)⁻¹ * (scalarCurve t - scalarCurve 0) - scalarDerivative‖ +
        originalGradeNorm grade
          (((t : ℂ)⁻¹ • (fieldCurve t - fieldCurve 0)) - fieldDerivative)) +
        originalGradeNorm grade
          (((t : ℂ)⁻¹ • (totalPotentialCurve t - totalPotentialCurve 0)) -
            totalPotentialDerivative)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [add_zero, zero_add] using total
  refine totalZero.congr' (Eventually.of_forall fun t => ?_)
  exact (expression t).symm

end Grad.PhysicalCoordinates
