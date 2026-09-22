import AKAE7SameGlobalCartesianCells

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.ActualSmoothPhysicalField
open Grad.CartesianState Grad.AnnularFullGraph Grad.AnnularForwardDatum Grad.AnnularStrongOrbit
open Grad.AnnularForwardTraces Grad.AnnularStrongSolution Grad.AnnularStrongData
open Grad.AnnularReconstruction Grad.AnnularCoupledInverse Grad.AnnularRestriction
open Grad.AnnularExhaustionEstimate Grad.AnnularWeakExhaustion Grad.AnnularFullSource
open Grad.AnnularHighGenerators Grad.AnnularCrossOrbit Grad.ActualAnnularExhaustion
open Grad.QuotientProjection Grad.FlatSourceProjection Grad.SourceCollarFullSource Grad.ExhaustionSourceAllocation
open Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  traceCoupledRealNormed traceCoupledRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule
  sourceRadialRealInner sourceGraphRealInner sourceKnownGraphRealInner
  weakRetainedRealInner weakSourcesRealInner weakFiveRealInner

attribute [local instance] weakWeightedRetainedRealInner
attribute [local instance] Grad.AnnularStrongOrbit.knownAmbientNormed Grad.AnnularStrongOrbit.knownAmbientSeminormed Grad.AnnularStrongOrbit.knownAmbientRealNormed Grad.AnnularStrongOrbit.knownAmbientRealModule
  Grad.AnnularStrongOrbit.strongCarrierNormed Grad.AnnularStrongOrbit.strongCarrierSeminormed Grad.AnnularStrongOrbit.strongCarrierRealNormed Grad.AnnularStrongOrbit.strongCarrierRealModule
  Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace
  Grad.AnnularCrossOrbit.coupledNormed Grad.AnnularCrossOrbit.coupledSeminormed
  Grad.AnnularCrossOrbit.coupledComplexNormed Grad.AnnularCrossOrbit.coupledComplexModule
  Grad.AnnularCrossOrbit.coupledRealNormed Grad.AnnularCrossOrbit.coupledRealModule
  Grad.AnnularCrossOrbit.coupledOperatorRealNormed Grad.AnnularCrossOrbit.coupledOperatorRealModule





open Grad.AnnularKernelContinuity
open Grad.AnnularPhysicalReconstruction Grad.AnnularKernelL2 Grad.SourceCollarDivision


open Grad.ActualPuncturedReconstruction Grad.AnnularCurrentEnergy

open Grad.ActualPuncturedFamily Grad.ActualPhysicalField

variable (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (fields : ∀ index, OriginalFiveBlockAmbient parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index))


variable
    (member : ∀ index, fields index ∈ OriginalObservedEquationGraph parameters length compact
      (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index)
      (originalExhaustionRadius_half length lengthPositive index) lengthPositive widthHalf widthLength state)
    (sameSources : ∀ index, (fields index).ofLp.2 =
      (cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0).val.ofLp.1)
    (allGrades : ∀ index grade : ℕ, ∃ weighted : CoupledSpace (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index) lengthPositive,
      CoupledInsertedGrade (originalExhaustionRadius length index) length
        (originalExhaustionRadius_positive length lengthPositive index) lengthPositive grade
        (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length
          (originalExhaustionRadius_positive length lengthPositive index)
          ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index)) weighted)

/-- Exact corrected physical curves for the original compatible source family. -/
def cartesianCorrectedVectorCurves (index : ℕ) :
    SmoothLowPhysicalRow parameters (originalExhaustionRadius length index)
      (originalExhaustionRadius_positive length lengthPositive index)
      (cartesianCorrectedVectorFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index) :=
  actualObservedPhysicalUCurves parameters length compact (originalExhaustionRadius length index)
    (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index)
    lengthPositive widthHalf widthLength state
    (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    source flat (fields index) (member index) (sameSources index) (allGrades index)

/-- Exact corrected physical curves for the original compatible source family. -/
def cartesianCorrectedScalarOverRadiusCurves (index : ℕ) :
    SmoothLowPhysicalRow parameters (originalExhaustionRadius length index)
      (originalExhaustionRadius_positive length lengthPositive index)
      (cartesianCorrectedScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index) :=
  actualObservedSOverRadiusCurves parameters length compact (originalExhaustionRadius length index)
    (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index)
    lengthPositive widthHalf widthLength state
    (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    source flat (fields index) (member index) (sameSources index) (allGrades index)

variable (compatible : ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)
include compatible in
/-- Both corrected rows preserve the same original collar restrictions. -/
theorem cartesianCorrectedFamilies_compatible (first second : ℕ) (ordered : first ≤ second) :
    originalBulkRestriction 3 (originalExhaustionRadius length second) (originalExhaustionRadius length first)
      (originalExhaustionRadius_antitone length lengthPositive ordered)
      (cartesianCorrectedVectorFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields second) = cartesianCorrectedVectorFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields first ∧
    originalBulkRestriction 1 (originalExhaustionRadius length second) (originalExhaustionRadius length first)
      (originalExhaustionRadius_antitone length lengthPositive ordered)
      (cartesianCorrectedScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields second) = cartesianCorrectedScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields first := by
  have sourceCompatible := fun first second included =>
    (cartesianExhaustionDatum_restrict parameters length compact lengthPositive widthHalf widthLength state small source flat first second 0 included).symm
  have polarCompatible := originalCovariantFamilies_compatible parameters length compact (originalExhaustionRadius length)
    (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_half length lengthPositive) lengthPositive state
    (fun index => cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0) fields
    (originalExhaustionRadius_antitone length lengthPositive) sourceCompatible compatible
  have scalarCompatible := originalScalarOverRadiusFamily_compatible parameters length (originalExhaustionRadius length)
    (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_half length lengthPositive) lengthPositive
    (fun index => cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0) fields
    (originalExhaustionRadius_antitone length lengthPositive) sourceCompatible compatible
  constructor
  · exact correctedPhysicalVectorFamily_compatible parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
      (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
      (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
      (fun index => (originalExhaustionRadius_half length lengthPositive index).trans (by norm_num))
      _ (originalExhaustionRadius_antitone length lengthPositive) (fun first second ordered => (polarCompatible first second ordered).1) first second ordered
  · exact correctedPhysicalScalarOverRadiusFamily_compatible (originalExhaustionRadius length) _ _
      (originalExhaustionRadius_antitone length lengthPositive)
      (fun first second ordered => (polarCompatible first second ordered).1) scalarCompatible first second ordered

end Grad.ActualSmoothPhysicalField
