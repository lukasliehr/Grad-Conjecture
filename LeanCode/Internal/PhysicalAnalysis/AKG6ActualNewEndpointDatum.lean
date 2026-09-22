import AKG5SameInsertedGraphWitnesses

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
namespace Grad.AnnularRestriction
open Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.SourceCollarDivision Grad.AnnularSourceGraph Grad.AnnularCurrentSource
open Grad.AnnularForwardTraces Grad.AnnularStrongOrbit Grad.AnnularLowEnergy
open Grad.AnnularForwardDatum Grad.AnnularCrossMaps Grad.AnnularCoupledInverse Grad.AnnularReconstruction
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule

@[instance_reducible] private def genericSubmoduleNormed {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (carrier : Submodule ℝ E) : NormedSpace ℝ carrier := inferInstance
local instance restrictionStrongRealNormed (parameters : PhaseParameters) (lower : ℝ) :
    NormedSpace ℝ (OriginalStrongCarrier parameters lower 0 0) :=
  genericSubmoduleNormed (OriginalStrongCarrier parameters lower 0 0)
local instance restrictionStrongRealModule (parameters : PhaseParameters) (lower : ℝ) :
    Module ℝ (OriginalStrongCarrier parameters lower 0 0) :=
  (restrictionStrongRealNormed parameters lower).toModule

private theorem originalAmbient_mem_of_sourceMeans (parameters : PhaseParameters) (lower : ℝ)
    (field : OriginalStrongAmbient parameters lower 0 0)
    (first : ∀ mode : ℤ × ℤ, mode.1 = 0 → unweightedSourceF2Bulk parameters lower field.ofLp.1.ofLp.1.ofLp.2 mode = 0)
    (second : ∀ mode : ℤ × ℤ, mode.1 = 0 → field.ofLp.1.ofLp.2.ofLp.1 mode = 0)
    (third : ∀ mode : ℤ × ℤ, mode.1 = 0 → field.ofLp.1.ofLp.2.ofLp.2 mode = 0) :
    field ∈ OriginalStrongCarrier parameters lower 0 0 := by
  exact ⟨⟨sub_eq_zero.mpr ((meanFreeRow_fixed_iff lower _).mpr first),
    sub_eq_zero.mpr ((meanFreeRow_fixed_iff lower _).mpr second)⟩,
    sub_eq_zero.mpr ((meanFreeRow_fixed_iff lower _).mpr third)⟩

variable (parameters : PhaseParameters) (length compact lower upper : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperHalf : upper ≤ 1 / 2)
    (lengthPositive : 0 < length) (included : lower ≤ upper)
    (state : RetainedInverseState parameters length compact)

/-- Rebuild the actual datum at the new collar from all five restricted
original blocks. The incoming values are the actual traces at the NEW endpoint. -/
def originalEndpointDatum : ForwardFiveBlocks parameters lower length lowerPositive →L[ℝ]
    OriginalStrongCarrier parameters upper 0 0 :=
  (originalForwardDatum parameters length compact upper upperPositive upperHalf lengthPositive state).comp
    (originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive
      (upperHalf.trans_lt (by norm_num)) lengthPositive included)

theorem originalEndpointDatum_apply (field : ForwardFiveBlocks parameters lower length lowerPositive) :
    originalEndpointDatum parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state field =
      originalForwardDatum parameters length compact upper upperPositive upperHalf lengthPositive state
        (originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive
          (upperHalf.trans_lt (by norm_num)) lengthPositive included field) := rfl

theorem originalEndpointDatum_continuous :
    Continuous (originalEndpointDatum parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state) :=
  (originalEndpointDatum parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state).continuous

/-- All four copied original source/residual blocks survive EXACTLY for
any original datum and arbitrary retained candidate. Only the boundary is rebuilt. -/
theorem originalEndpointDatum_sources (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower length lowerPositive) :
    (originalEndpointDatum parameters length compact lower upper lowerPositive upperPositive upperHalf lengthPositive included state
      (originalFiveBlockObservation parameters lower length lowerPositive data candidate)).val.ofLp.1 =
      originalFullSourceRestriction parameters lower upper included data.val.ofLp.1 := by
  let observed := originalFiveBlockObservation parameters lower length lowerPositive data candidate
  let restricted := originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive
    (upperHalf.trans_lt (by norm_num)) lengthPositive included observed
  let ambient := originalForwardAmbient parameters length compact upper upperPositive upperHalf lengthPositive state restricted
  have means := OriginalStrongCarrier.mean_free parameters lower 0 0 data
  have restrictedMeans := originalFullSourceRestriction_meanFree parameters lower upper included data.val.ofLp.1
    means.1 means.2.1 means.2.2
  have mem : ambient ∈ OriginalStrongCarrier parameters upper 0 0 :=
    originalAmbient_mem_of_sourceMeans parameters upper ambient restrictedMeans.1 restrictedMeans.2.1 restrictedMeans.2.2
  let rebuilt : OriginalStrongCarrier parameters upper 0 0 := ⟨ambient,mem⟩
  have same := originalMeanFreeRetraction_fixed parameters upper upperPositive (upperHalf.trans (by norm_num)) rebuilt
  exact congrArg (fun value : OriginalStrongCarrier parameters upper 0 0 => value.val.ofLp.1) same

end Grad.AnnularRestriction
