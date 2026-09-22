import AKDB10SameActualPsiPhase
import AKCX31ActualKnownAllSpatialGraphs
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000
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


open Grad.ActualCartesianFlux
open Grad.ActualCartesianDescent Grad.ClosedJets Grad.DiskExtension.Operator Grad.BoundaryTrace Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularGeneralSourceRegularity Grad.ActualSmoothPhysicalField Grad.PuncturedRetainedEnergy
variable (compatible : ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)

open Grad.PhysicalFamily Grad.PDEBootstrap Grad.Constraints
open Grad.ActualScalarWeakEquations Grad.ActualForceMoments Grad.ActualCartesianEquations Grad.Constraints.Gauges

open Grad.ActualCurrentPrimitives

include compatible

variable (M : ℝ) (Mnonnegative : 0 ≤ M)
    (stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ M)
    (vanishing : SourceHigherVanishing source)
    (nativeBound : ∀ index, originalWeightedRetainedNorm parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index).ofLp.1 ≤
        2 * independentCoupledDataConstant parameters length compact *
          (originalSourceAllocationConstant parameters length 0 * (1 + M) * ‖quotientEta parameters 8 source‖))

open Grad.PhysicalAxisEquation
include Mnonnegative stateBound vanishing nativeBound

open Grad.CartesianStartup Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ActualNativeCellMoments Grad.ActualOriginalSourceMoments
variable (graded : ∀ index (_grade : ℕ), CoupledSpace (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index) lengthPositive)
    (sameGrade : ∀ index grade, CoupledInsertedGrade (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index) lengthPositive grade
      (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length
        (originalExhaustionRadius_positive length lengthPositive index)
        ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index)) (graded index grade))
    (constants : ℕ → ℝ) (estimate : ∀ index grade, ‖graded index grade‖ ≤ constants grade)
include sameGrade estimate



open Grad.SpatialDilation


open Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets Grad.ActualOriginalSourceFirst Grad.AnalyticWeights.Calculus
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.Ledger
local notation "fixedScale" => originalStartupScale length lengthPositive

/-- Genuine full covariant and retained scalar regularity of the SAME native
family. The only analytic input is the proved all-order circle induction;
actual coefficients, weak force, sources and scalar phase are supplied here. -/
theorem actualNative_covariantPsi_allSpatialGraphs
    (admissible : Admissible length parameters.sigma0 parameters.gamma (fixedScale).val)
    (ledger : ActualLedger parameters admissible state.val.val.rho state.val.val.alpha state.val.val.delta
      state.val.val.parameter state.val.val.epsilon state.val.val.field)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.val.gaugeDeviation))
    (gaugeConstants : ℕ → ℝ) (gaugeNonnegative : ∀ grade, 0 ≤ gaugeConstants grade)
    (low : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 6 ≤ 1)
    (gaugeBound : ∀ grade, ‖ledger.val.gaugeDeviation grade‖ ≤ gaugeConstants grade *
      physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade+4))
    (determinantSmall : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 6 ≤ determinantLowRadius gaugeConstants)
    (allNative : OriginalNativeAllMoments parameters
      (actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades)
      (actualCartesianXiOverRadiusCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades))
    (regular : ∀ order, ((StartupSignedFamily.ofNatural (allNative.scaledCovariant fixedScale) length (fixedScale).val).circle).HasSpatialGrade order) :
    (∀ order, (StartupSignedFamily.ofNatural (allNative.scaledCovariant fixedScale) length (fixedScale).val).HasSpatialGrade order) ∧
    (∀ order weight, ∃ graph : GraphGrade 1 order weight openUnitDisk,
      base 1 order openUnitDisk (fun _ => weight) graph=(allNative.scaledPsi fixedScale).field) := by
  obtain ⟨covariant,force,cofactor,xi,covariantSame,forceSame,cofactorSame,xiSame,weak⟩ :=
    actualNative_scaledERRows parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible
      M Mnonnegative stateBound vanishing nativeBound graded sameGrade constants estimate fixedScale
  obtain ⟨weighted,weightedForce,weightedCofactor,weightedSame,weightedForceSame,weightedCofactorSame,
    covariantRep,forceRep,cofactorRep,orbit,forceContinuous,cofactorContinuous⟩ :=
    actualNative_scaledMatrixRepresentatives parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible
      vanishing graded sameGrade constants estimate fixedScale
  let knownForce := (originalSourceMoments parameters (cartesianSourceVector source)).dilate fixedScale
  let knownThird := ((originalSourceMoments parameters (source 3)).dilate fixedScale).smul (length : ℂ)⁻¹
  let determinant := ((originalSourceMoments parameters (source 2)).dilate fixedScale).smul (((fixedScale).val : ℂ)/(length : ℂ))
  let rawKnownForce := (originalSourceRawMoments parameters (cartesianSourceVector source)).dilate fixedScale
  let rawKnownThird := ((originalSourceRawMoments parameters (source 3)).dilate fixedScale).smul (length : ℂ)⁻¹
  let rawDeterminant := ((originalSourceRawMoments parameters (source 2)).dilate fixedScale).smul (((fixedScale).val : ℂ)/(length : ℂ))
  let rows := nativeERRows weighted weightedForce weightedCofactor knownForce knownThird determinant
  let rawRows := nativeERRows (covariant.dilate fixedScale) (force.dilate fixedScale) (cofactor.dilate fixedScale)
    rawKnownForce rawKnownThird rawDeterminant
  have phase : StartupNativeERRowsRelated (physicalWeight parameters.sigma0 parameters.gamma (fixedScale).val) rows rawRows := by
    apply nativeERRows_phase
    · intro cell first second same
      simp only [physicalWeight,same]
    · exact sameScaledNative_phase parameters fixedScale _ _ _ weightedSame covariantSame
    · exact sameScaledNative_phase parameters fixedScale _ _ _ weightedForceSame forceSame
    · exact sameScaledNative_phase parameters fixedScale _ _ _ weightedCofactorSame cofactorSame
    · exact originalKnownSource_scaledPhase parameters (cartesianSourceVector source) fixedScale
    · exact (originalKnownSource_scaledPhase parameters (source 3) fixedScale).smul (length : ℂ)⁻¹
    · exact (originalKnownSource_scaledPhase parameters (source 2) fixedScale).smul (((fixedScale).val : ℂ)/(length : ℂ))
  have recovered := actualNative_current_recovers parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible
    admissible ledger inverseCoherent gaugeConstants gaugeNonnegative low gaugeBound determinantSmall weighted.field covariantRep
  have coefficientLow := originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small
  have forces := actualWeighted_forceLedger_actions admissible ledger coefficientLow covariantRep orbit forceRep forceContinuous
  have coefficientFlux := actualWeighted_fluxLedger_action admissible ledger coefficientLow covariantRep orbit cofactorRep cofactorContinuous
  have operators := nativeERRows_actualOperators admissible ledger.val ledger.property.1 inverseCoherent weighted weightedForce weightedCofactor
    knownForce knownThird determinant recovered forces.1 forces.2 coefficientFlux

  let signed := StartupSignedFamily.ofNatural (allNative.scaledCovariant fixedScale) length (fixedScale).val
  have allSameBase : signed.field=weighted.field := by
    apply Lp.ext
    filter_upwards [allNative.scaledCovariant_same fixedScale,weightedSame] with point one two
    apply lp.ext
    funext cell
    exact (one cell).trans (two cell).symm
  have fullRecovery : originalCurrentKernel admissible ledger.val.gaugeDeviation ledger.property.1.2.2.2.1 inverseCoherent
      (originalCircleKernel signed.field)=signed.field := by
    rw [allSameBase,recovered]
  have fullRegular (order : ℕ) : signed.HasSpatialGrade order :=
    signed.current_allSpatialGrade admissible ledger.val ledger.property.1 inverseCoherent lengthPositive.ne' (fixedScale).property.1.ne'
      order (regular order) fullRecovery
  let signedForce := StartupSignedFirstFamily.knownForce parameters source length lengthPositive
  let actualForce := (StartupSignedAction.force admissible ledger.val ledger.property.1 inverseCoherent).action signed.circle
  let gradient := (signed.circle.value planarPartMap).recoveredGradient (signedForce.toStartupSignedFamily.sub actualForce)
  have forceBase : signedForce.field=rows.knownForce.field := by
    change startupGenuineQradKernel (base 2 1 openUnitDisk (fun _ => 0)
      (scaledOriginalSourceFirst parameters (cartesianSourceVector source) fixedScale)) = _
    rw [scaledOriginalSourceFirst_base]
    rfl
  have gradientSame : gradient.field=rows.gradient.field := by
    change startupRecoveredGradient (originalValueKernel planarPartMap (originalCircleKernel signed.field))
      (signedForce.field-((StartupSignedAction.force admissible ledger.val ledger.property.1 inverseCoherent).action signed.circle).field)=_
    rw [StartupSignedAction.sameField,StartupSignedAction.force_coarse]
    change startupRecoveredGradient (originalValueKernel planarPartMap (originalCircleKernel signed.field))
      (signedForce.field-startupGenuineForceKernel admissible ledger.val ledger.property.1 inverseCoherent (originalCircleKernel signed.field))=_
    rw [allSameBase,forceBase]
    change startupRecoveredGradient rows.vector.field
      (rows.knownForce.field-startupGenuineForceKernel admissible ledger.val ledger.property.1 inverseCoherent rows.circle.field)=rows.gradient.field
    rw [operators.1]
    rfl
  have gradientRegular (order : ℕ) : gradient.HasSpatialGrade order :=
    ((regular order).value planarPartMap).recoveredGradient
      ((StartupSignedFirstFamily.knownForce_allSpatialGrade parameters source length lengthPositive order).sub
        (StartupSignedAction.actualForce_allSpatialGrade admissible ledger.val ledger.property.1 inverseCoherent
          lengthPositive.ne' (fixedScale).property.1.ne' order signed.circle (regular order)))
  have scalarPhase := actualNativePsi_scaledPhase parameters length compact lengthPositive widthHalf widthLength state small source flat
    fields member sameSources allGrades allNative fixedScale xi.field xiSame
  refine ⟨fullRegular,?_⟩
  exact weak.weighted_scalar_allSpatialGraphs phase
    (fun cell first second equal => by simp only [physicalWeight,equal]) scalarPhase gradient gradientSame gradientRegular

end Grad.ActualScaledNativeCoefficients
