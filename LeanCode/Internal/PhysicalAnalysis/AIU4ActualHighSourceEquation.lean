import AIU3SamePhysicalHighSuperposition

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentSolution Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse Grad.AnnularCurrentSource
open Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularCrossMaps Grad.AnnularUniformBoundary
open Grad.AnnularCurrentGreen Grad.AnnularOmegaGraph Grad.AnnularPhysicalSolution Grad.AnnularCurrentBoundary
open Grad.AnnularTiltedReference

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)

/-- The exact completed high source equation: actual incoming trace,
full complex physical form, and the actual recovered first-row flux value.
The flux derivative is already fixed by the original closed graph. -/
def HighSourceEquation (data : ActualHighGraphKnownData parameters lower 0 0)
    (field : CrossHighSpace lower L positive lengthPositive) : Prop :=
  annularEnergyTrace lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive 0
      (bEnergyDecode lower L positive field.ofLp.1) = data.innerValue ∧
  (∀ test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive,
    currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field.ofLp.1 test.val =
      actualHighGraphKnownFunctionalValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
        data.weighted data.auxiliary data.graphs data.datum test.val) ∧
  field.ofLp.2.val 0 = highPhysicalOutput lower 0
    (actualFullHighOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field.ofLp.1
      data.weighted data.auxiliary)

variable (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

theorem fullKnownHighResponse_equation (data : ActualHighGraphKnownData parameters lower 0 0) :
    HighSourceEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data
      (fullKnownHighResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) := by
  refine ⟨graphDataEnergySolution_physical_inner parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data, ?_, rfl⟩
  intro test
  exact actualHighGraphEnergySolution_complex parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    data.weighted data.auxiliary data.graphs data.datum data.innerValue test

theorem fullKnownHighResponse_unique (data : ActualHighGraphKnownData parameters lower 0 0)
    (field : CrossHighSpace lower L positive lengthPositive)
    (equation : HighSourceEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data field) :
    field = fullKnownHighResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data := by
  have energy := graphDataEnergySolution_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
    data field.ofLp.1 equation.1 equation.2.1
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).injective
  apply Prod.ext
  · exact energy
  · apply annularOmegaGraph_value_injective lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
    change field.ofLp.2.val 0 = highPhysicalOutput lower 0
      (graphDataPhysicalOutput parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data)
    rw [equation.2.2, energy]
    rfl

theorem highSourceEquation_iff_response (data : ActualHighGraphKnownData parameters lower 0 0)
    (field : CrossHighSpace lower L positive lengthPositive) :
    HighSourceEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data field ↔
      field = fullKnownHighResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data := by
  constructor
  · exact fullKnownHighResponse_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data field
  · intro same
    rw [same]
    exact fullKnownHighResponse_equation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data

end Grad.AnnularFullSource
