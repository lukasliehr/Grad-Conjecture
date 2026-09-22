import AKAC27CorrectedCompatiblePhysicalEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 450000
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

def cartesianPolarCovariantFamily : ∀ index, DivisionRow 3 (originalExhaustionRadius length index) :=
  originalCovariantFamily parameters length compact (originalExhaustionRadius length)
    (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_half length lengthPositive) lengthPositive
    state (fun index => cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0) fields

def cartesianCorrectedVectorFamily : ∀ index, DivisionRow 3 (originalExhaustionRadius length index) :=
  correctedPhysicalVectorFamily parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans (by norm_num))
    (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields)

def cartesianCorrectedScalarOverRadiusFamily : ∀ index, DivisionRow 1 (originalExhaustionRadius length index) :=
  correctedPhysicalScalarOverRadiusFamily (originalExhaustionRadius length)
    (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields)
    (cartesianOriginalScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields)

variable (M : ℝ) (Mnonnegative : 0 ≤ M)
    (stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ M)
    (vanishing : SourceHigherVanishing source)
    (nativeBound : ∀ index, originalWeightedRetainedNorm parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index).ofLp.1 ≤
        2 * independentCoupledDataConstant parameters length compact *
          (originalSourceAllocationConstant parameters length 0 * (1 + M) * ‖quotientEta parameters 8 source‖))
    (compatible : ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)
include Mnonnegative stateBound vanishing nativeBound compatible

/-- The actual source family has finite corrected U and S/r energy. The
polar rotation and scalar correction are both performed before this estimate. -/
theorem cartesianCorrectedPhysicalFamilies_globalBound :
    globalPhysicalBulkEnergy 3 (originalExhaustionRadius length)
      (cartesianCorrectedVectorFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) ≤
      ENNReal.ofReal ((5 * physicalUActionConstant parameters length 0 *
        (1 + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 5) *
        (cartesianPhysicalBulkConstant parameters length compact M * ‖quotientEta parameters 8 source‖)) ^ 2) ∧
    globalPhysicalBulkEnergy 1 (originalExhaustionRadius length)
      (cartesianCorrectedScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) ≤
      ENNReal.ofReal (((cartesianScalarBulkConstant parameters length compact M +
        cartesianPhysicalBulkConstant parameters length compact M) * ‖quotientEta parameters 8 source‖) ^ 2) := by
  have sourceCompatible := fun first second included =>
    (cartesianExhaustionDatum_restrict parameters length compact lengthPositive widthHalf widthLength state small source flat first second 0 included).symm
  have covariantCompatible := originalCovariantFamilies_compatible parameters length compact (originalExhaustionRadius length)
    (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_half length lengthPositive) lengthPositive state
    (fun index => cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0) fields
    (originalExhaustionRadius_antitone length lengthPositive) sourceCompatible compatible
  have scalarCompatible := originalScalarOverRadiusFamily_compatible parameters length (originalExhaustionRadius length)
    (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_half length lengthPositive) lengthPositive
    (fun index => cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0) fields
    (originalExhaustionRadius_antitone length lengthPositive) sourceCompatible compatible
  have covariantBound (index : ℕ) :
      ‖cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index‖ ≤
        cartesianPhysicalBulkConstant parameters length compact M * ‖quotientEta parameters 8 source‖ :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans
      (cartesianOriginalCovariants_bound parameters length compact lengthPositive widthHalf widthLength state small
        M Mnonnegative stateBound source flat vanishing index (fields index) (nativeBound index))
  have scalarBound (index : ℕ) :
      ‖cartesianOriginalScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index‖ ≤
        cartesianScalarBulkConstant parameters length compact M * ‖quotientEta parameters 8 source‖ :=
    cartesianOriginalScalarOverRadius_bound parameters length compact lengthPositive widthHalf widthLength state small
      M stateBound source flat vanishing index (fields index) (nativeBound index)
  constructor
  · exact correctedPhysicalVectorFamily_globalBound parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
      (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
      (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
      (fun index => (originalExhaustionRadius_half length lengthPositive index).trans (by norm_num))
      _ (originalExhaustionRadius_antitone length lengthPositive) (fun first second ordered => (covariantCompatible first second ordered).1)
      (originalExhaustionRadius_tendsto length) _ covariantBound
  · have estimate := correctedPhysicalScalarOverRadiusFamily_globalBound (originalExhaustionRadius length)
      (originalExhaustionRadius_positive length lengthPositive) _ _ (originalExhaustionRadius_antitone length lengthPositive)
      (fun first second ordered => (covariantCompatible first second ordered).1) scalarCompatible
      (originalExhaustionRadius_tendsto length) _ _ covariantBound scalarBound
    simpa only [cartesianCorrectedScalarOverRadiusFamily,cartesianPolarCovariantFamily,cartesianOriginalScalarOverRadiusFamily,← add_mul] using estimate

end Grad.ActualSmoothPhysicalField
