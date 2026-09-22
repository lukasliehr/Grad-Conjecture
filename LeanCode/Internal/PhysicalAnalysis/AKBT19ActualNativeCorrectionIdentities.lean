import AKBT18ScaledNativeFixedKernels

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


include compatible
open Grad.CartesianStartup Grad.ActualForceMoments Grad.ActualScalarWeakEquations
open Grad.Constraints.Gauges Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Ledger Grad.GenericCarriers Grad.PDEBootstrap


/-- Same physical force correction, now as an equality in the rough joint-cell carrier. -/
theorem actualNative_forceCorrectionKernel (force correction : StartupL2 3)
    (forceSame : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      force point cell = actualCartesianForceMatrixCell parameters length compact lengthPositive widthHalf widthLength state small
        source flat fields member sameSources allGrades cell point)
    (correctionSame : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      correction point cell = actualCartesianForceCorrectionCell parameters length compact lengthPositive widthHalf widthLength state small
        source flat fields member sameSources allGrades cell point) :
    originalValueKernel planarPartMap correction = (2 : ℂ) • originalValueKernel planarPartMap force := by
  apply Lp.ext
  filter_upwards [forceSame,correctionSame,
    startupPointKernel_field_ae planarPartMap (LinearIsometryEquiv.refl ℝ _) force,
    startupPointKernel_field_ae planarPartMap (LinearIsometryEquiv.refl ℝ _) correction,
    Lp.coeFn_smul (2 : ℂ) (originalValueKernel planarPartMap force)]
    with point actual corrected forceAt correctionAt scaled
  apply lp.ext
  funext cell
  change ∀ cell, originalValueKernel planarPartMap force point cell = planarPartMap (force point cell) at forceAt
  change ∀ cell, originalValueKernel planarPartMap correction point cell = planarPartMap (correction point cell) at correctionAt
  rw [scaled,Pi.smul_apply,lp.coeFn_smul,Pi.smul_apply,forceAt cell,correctionAt cell,actual cell,corrected cell]
  change planarPartMap (forceCorrectionMap length _) = _
  rw [forceCorrectionMap_apply]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> rfl

/-- The native projected third correction has its exact negative-length
normalization in L2; this is the positive correction in the normalized third equation. -/
theorem actualNative_projectedThirdKernel_eq (force : StartupL2 3) (correction : StartupL2 1)
    (forceSame : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      force point cell = actualCartesianForceMatrixCell parameters length compact lengthPositive widthHalf widthLength state small
        source flat fields member sameSources allGrades cell point)
    (correctionSame : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      correction point cell = actualCartesianProjectedThirdForceCell parameters length compact lengthPositive widthHalf widthLength state small
        source flat fields member sameSources allGrades cell point) :
    correction = (-2 * (length : ℂ)) • originalScalarMeanFreeKernel (originalValueKernel toroidalPartMap force) := by
  have actual := actualNative_projectedThirdForceKernel parameters length compact lengthPositive widthHalf widthLength state small
    source flat fields member sameSources allGrades compatible force forceSame
  rw [nativeThirdValueMap] at actual
  apply Lp.ext
  filter_upwards [actual,correctionSame] with point actualAt correctionAt
  apply lp.ext
  funext cell
  exact (correctionAt cell).trans (actualAt cell).symm

end Grad.ActualScaledNativeCoefficients
