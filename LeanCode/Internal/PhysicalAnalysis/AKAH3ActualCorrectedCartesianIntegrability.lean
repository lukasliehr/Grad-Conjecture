import AKAH2SamePhysicalCellEnergyIntegrability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff
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


open Grad.ActualCartesianDescent Grad.ClosedJets Grad.DiskExtension.Operator Grad.BoundaryTrace Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
variable (M : ℝ) (Mnonnegative : 0 ≤ M)
    (stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ M)
    (vanishing : SourceHigherVanishing source)
    (nativeBound : ∀ index, originalWeightedRetainedNorm parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index).ofLp.1 ≤
        2 * independentCoupledDataConstant parameters length compact *
          (originalSourceAllocationConstant parameters length 0 * (1 + M) * ‖quotientEta parameters 8 source‖))

variable (compatible : ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)

open Grad.ActualCartesianIntegrability
include Mnonnegative stateBound vanishing nativeBound compatible

/-- Actual corrected U, with the exact original source and uniform energy,
is integrable together with its inverse-radius norm on the full Cartesian disk. -/
theorem actualCartesianVectorCell_integrable_pair (cell : ℤ) :
    IntegrableOn (actualCartesianVectorCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖actualCartesianVectorCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point‖) openUnitDisk := by
  have polarBound (index : ℕ) : ‖cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index‖ ≤
      cartesianPhysicalBulkConstant parameters length compact M * ‖quotientEta parameters 8 source‖ :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans
      (cartesianOriginalCovariants_bound parameters length compact lengthPositive widthHalf widthLength state small
        M Mnonnegative stateBound source flat vanishing index (fields index) (nativeBound index))
  have estimate (index : ℕ) : ‖cartesianCorrectedVectorFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index‖ ≤ 5 * physicalUActionConstant parameters length 0 * (1 + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 5) * (cartesianPhysicalBulkConstant parameters length compact M * ‖quotientEta parameters 8 source‖) := by
    apply (physicalUFromPolar_bound parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
      (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
      (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num))
      (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index)).trans
    exact mul_le_mul_of_nonneg_left (polarBound index) (mul_nonneg
      (mul_nonneg (by norm_num) (physicalUActionConstant_nonnegative parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
        (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small) 0))
      (by linarith [physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon 5]))
  exact sameOriginalPhysicalCell_integrable_pair parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive)
    (cartesianCorrectedVectorFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (cartesianCorrectedVectorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades)
    (fun first second ordered => (cartesianCorrectedFamilies_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).1)
    _ estimate cell

/-- The genuine corrected S/r, including its original angular projection,
has the same two Cartesian integrability bounds. -/
theorem actualCartesianScalarOverRadiusCell_integrable_pair (cell : ℤ) :
    IntegrableOn (actualCartesianScalarOverRadiusCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖actualCartesianScalarOverRadiusCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point‖) openUnitDisk := by
  have polarBound (index : ℕ) : ‖cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index‖ ≤
      cartesianPhysicalBulkConstant parameters length compact M * ‖quotientEta parameters 8 source‖ :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans
      (cartesianOriginalCovariants_bound parameters length compact lengthPositive widthHalf widthLength state small
        M Mnonnegative stateBound source flat vanishing index (fields index) (nativeBound index))
  have scalarBound (index : ℕ) :
      ‖cartesianOriginalScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index‖ ≤
      cartesianScalarBulkConstant parameters length compact M * ‖quotientEta parameters 8 source‖ :=
    cartesianOriginalScalarOverRadius_bound parameters length compact lengthPositive widthHalf widthLength state small
      M stateBound source flat vanishing index (fields index) (nativeBound index)
  have estimate (index : ℕ) : ‖cartesianCorrectedScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index‖ ≤ (cartesianScalarBulkConstant parameters length compact M + cartesianPhysicalBulkConstant parameters length compact M) * ‖quotientEta parameters 8 source‖ := by
    have bound := (polarScalarOverRadiusRow_bound (originalExhaustionRadius length index)
      (cartesianOriginalScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index) (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index)).trans
      (add_le_add (scalarBound index) (polarBound index))
    simpa only [cartesianCorrectedScalarOverRadiusFamily,correctedPhysicalScalarOverRadiusFamily,← add_mul] using bound
  exact sameOriginalPhysicalCell_integrable_pair parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive)
    (cartesianCorrectedScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (cartesianCorrectedScalarOverRadiusCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades)
    (fun first second ordered => (cartesianCorrectedFamilies_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).2)
    _ estimate cell

end Grad.ActualSmoothPhysicalField
