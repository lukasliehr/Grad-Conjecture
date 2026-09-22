import AKZ11ActualSourceScalarEnergyBudget

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology
namespace Grad.ActualPhysicalField
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

open Grad.ActualPuncturedFamily

variable (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (fields : ∀ index, OriginalFiveBlockAmbient parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index))

def cartesianOriginalPhysicalVectorFamily : ∀ index, DivisionRow 3 (originalExhaustionRadius length index) :=
  actualPhysicalVectorFamily parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans (by norm_num))
    (originalCovariantFamily parameters length compact (originalExhaustionRadius length)
      (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_half length lengthPositive) lengthPositive
      state (fun index => cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0) fields)

def cartesianOriginalScalarOverRadiusFamily : ∀ index, DivisionRow 1 (originalExhaustionRadius length index) :=
  originalScalarOverRadiusFamily parameters length (originalExhaustionRadius length)
    (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_half length lengthPositive) lengthPositive
    (fun index => cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0) fields

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

theorem cartesianOriginalPhysicalVectorFamily_globalBound :
    globalPhysicalBulkEnergy 3 (originalExhaustionRadius length)
      (cartesianOriginalPhysicalVectorFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) ≤
      ENNReal.ofReal ((physicalUActionConstant parameters length 0 * (1 + M) *
        (cartesianPhysicalBulkConstant parameters length compact M * ‖quotientEta parameters 8 source‖)) ^ 2) := by
  have sourceCompatible := fun first second included =>
    (cartesianExhaustionDatum_restrict parameters length compact lengthPositive widthHalf widthLength state small source flat first second 0 included).symm
  have covariantCompatible := originalCovariantFamilies_compatible parameters length compact (originalExhaustionRadius length)
    (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_half length lengthPositive) lengthPositive state
    (fun index => cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0) fields
    (originalExhaustionRadius_antitone length lengthPositive) sourceCompatible compatible
  apply actualPhysicalVectorFamily_globalBound parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans (by norm_num))
    _ (originalExhaustionRadius_antitone length lengthPositive) (fun first second ordered => (covariantCompatible first second ordered).1)
    (originalExhaustionRadius_tendsto length) M (cartesianPhysicalBulkConstant parameters length compact M * ‖quotientEta parameters 8 source‖)
    ((physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon (by norm_num : 5 ≤ 14)).trans stateBound)
  intro index
  exact (le_add_of_nonneg_right (norm_nonneg _)).trans
    (cartesianOriginalCovariants_bound parameters length compact lengthPositive widthHalf widthLength state small
      M Mnonnegative stateBound source flat vanishing index (fields index) (nativeBound index))

omit Mnonnegative in
theorem cartesianOriginalScalarOverRadiusFamily_globalBound :
    globalPhysicalBulkEnergy 1 (originalExhaustionRadius length)
      (cartesianOriginalScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) ≤
      ENNReal.ofReal ((cartesianScalarBulkConstant parameters length compact M * ‖quotientEta parameters 8 source‖) ^ 2) := by
  apply originalScalarOverRadiusFamily_globalBound parameters length (originalExhaustionRadius length)
    (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_half length lengthPositive) lengthPositive
    (fun index => cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0) fields
    (originalExhaustionRadius_antitone length lengthPositive)
    (fun first second included => (cartesianExhaustionDatum_restrict parameters length compact lengthPositive widthHalf widthLength state small
      source flat first second 0 included).symm) compatible (originalExhaustionRadius_tendsto length)
    (cartesianScalarBulkConstant parameters length compact M * ‖quotientEta parameters 8 source‖)
  intro index
  exact cartesianOriginalScalarOverRadius_bound parameters length compact lengthPositive widthHalf widthLength state small
    M stateBound source flat vanishing index (fields index) (nativeBound index)

end Grad.ActualPhysicalField
