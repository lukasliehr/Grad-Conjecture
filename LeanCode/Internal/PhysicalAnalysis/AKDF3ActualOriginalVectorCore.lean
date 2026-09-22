import AKDF2SameNativeInverseTranspose
import AKBV20OriginalWidthPhysicalCoreConsumer
import AKCA15SameRecoveredVectorPolar
import AKCF6ActualNativePuncturedGraphs
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace Grad.ActualScaledNativeCoefficients
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
open Grad.ActualSmoothPhysicalField Grad.PuncturedRetainedEnergy
variable (compatible : ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)


open Grad.ActualCartesianFlux Grad.ActualNativeCellMoments Grad.CartesianStartup Grad.WeightedJets
open Grad.PDEBootstrap Grad.GenericCarriers Grad.SourceCollarFullSource


open Grad.OriginalCoreRealization Grad.AnalyticWeights.Calculus Grad.SpatialDilation
open Grad.ActualCartesianWeakEquations Grad.Constraints

open Grad.OriginalVectorCoreRecovery Grad.CartesianCoreRecovery

include compatible in
/-- The actual native U belongs to the original analytic core as soon as
the SAME full covariant has been recovered in that core. No new graph,
regularity, phase, or derivative hypothesis is required. -/
theorem actualNativeVector_of_covariantCore (covariant : ACore parameters 3)
    (same : ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters covariant).value (point,(axial : CellCircle)) =
        actualCartesianCovariantFamilyField parameters length compact lengthPositive widthHalf widthLength state small source flat
          fields member sameSources allGrades (point.val,axial)) :
    ∃ vector : ACore parameters 3,
      ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
        (originalPhysicalClosedJet parameters vector).value (point,(axial : CellCircle)) =
          actualCartesianVectorField parameters length compact lengthPositive widthHalf widthLength state small source flat
            fields member sameSources allGrades (point.val,axial) := by
  let coefficient := originalInverseTransposeFamily parameters length state.val.val.epsilon state.val.val.field
  have coherent := originalInverseTransposeFamily_coherent parameters length state.val.val.rho state.val.val.epsilon
    state.val.val.field (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho
      state.val.val.epsilon state.val.val.field small)
  let raw := actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small source flat
    fields member sameSources allGrades 1
  have regular := actualScaledCovariantRaw_regular parameters length compact lengthPositive widthHalf widthLength
    state small source flat fields member sameSources allGrades compatible 1 zero_lt_one le_rfl
  have inputSame : ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters covariant).value (point,(axial : CellCircle)) = raw (axial,point.val) := by
    simpa only [raw,actualScaledCovariantRaw,one_smul] using same
  obtain ⟨weighted,graphs,represented⟩ := originalCore_matrix_allGraphs parameters covariant coefficient coherent raw regular inputSame
  have uSame : StartupWeightedRep parameters.sigma0 parameters.gamma 1 weighted
      (fun pair => actualCartesianVectorField parameters length compact lengthPositive widthHalf widthLength state small
        source flat fields member sameSources allGrades (pair.2,pair.1)) := by
    apply represented.congr_raw
    filter_upwards [startupDisk_ae_nonzero,ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point nonzero inside
    intro axial
    exact actualNative_inverseTranspose_raw parameters length compact lengthPositive widthHalf widthLength state small
      source flat fields member sameSources allGrades compatible ⟨point,openDiskMembershipClosed point inside⟩
      (norm_pos_iff.mpr nonzero) axial
  obtain ⟨vector,_,physical⟩ := originalWidthLocalizedAllOrder_physicalCore parameters (originalExhaustionRadius length)
    (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive)
    (cartesianCorrectedVectorFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields)
    (cartesianCorrectedVectorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades)
    (fun first second ordered => (cartesianCorrectedFamilies_compatible parameters length compact lengthPositive widthHalf widthLength
      state small source flat fields compatible first second ordered).1)
    (⟨1,by norm_num⟩ : Scale) 1 zero_lt_one le_rfl weighted (fun grade => (graphs grade).choose)
    (fun grade => (graphs grade).choose_spec) (fun _ => 1) (fun _ _ => rfl) (by
      filter_upwards [uSame,startupDisk_ae_nonzero,ae_restrict_mem openUnitDisk_isOpen.measurableSet]
        with point actual nonzero inside
      intro cell
      simp only [one_smul]
      rw [actual cell]
      congr 1
      exact (nativeFamilyCell_actual parameters (originalExhaustionRadius length)
        (originalExhaustionRadius_positive length lengthPositive)
        (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
        (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive)
        (cartesianCorrectedVectorFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields)
        (cartesianCorrectedVectorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades)
        (fun first second ordered => (cartesianCorrectedFamilies_compatible parameters length compact lengthPositive widthHalf widthLength
          state small source flat fields compatible first second ordered).1) cell point nonzero inside).symm)
  exact ⟨vector,physical⟩

end Grad.ActualScaledNativeCoefficients
