import AKDS7SameActualXiCorePhase
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

open Grad.OriginalVectorCoreRecovery Grad.NonlinearProduct Grad.OriginalCoreRealization

omit compatible Mnonnegative stateBound vanishing nativeBound sameGrade estimate in
/-- The original unit-scale field dilation is literally the same L2 field. -/
theorem actualRecovery_dilation_one {dimension : ℕ} (field : StartupL2 dimension) :
    startupMomentDilation oneScale field = field := by
  apply Lp.ext
  filter_upwards [startupMomentDilation_ae oneScale field] with point same
  simpa only [oneScale,one_smul] using same

/-- The actual weak rows at original scale one determine the SAME original
Xi norm. Only the two recovered core identities are left for coefficient
composition; no weak-equation, phase or scalar-regularity premise remains. -/
theorem actualNativeXi_core_recovery_bound
    (scalar : ACore parameters 1)
    (scalarSame : ∀ (point : ClosedDisk),0<‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters scalar).value (point,(axial : CellCircle))=
        actualCartesianXiFamilyField parameters length compact lengthPositive widthHalf widthLength state small
          source flat fields member sameSources allGrades (point.val,axial)) :
    ∃ weighted force : StartupMoments 3,
      StartupWeightedRep parameters.sigma0 parameters.gamma 1 weighted.field
        (actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small
          source flat fields member sameSources allGrades 1) ∧
      StartupWeightedRep parameters.sigma0 parameters.gamma 1 force.field
        (nativeScaledMatrixRaw 1 (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field)
          (actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small
            source flat fields member sameSources allGrades 1)) ∧
      ∀ (vector right : ACore parameters 2),
        originalSourceFieldLinear parameters vector =
          originalValueKernel planarPartMap (originalCircleKernel weighted.field) →
        originalSourceFieldLinear parameters right =
          startupGenuineQradKernel (originalSourceFieldLinear parameters (cartesianSourceVector source)) -
            (2:ℂ) • startupGenuineQradKernel (originalValueKernel planarPartMap force.field) →
        ∀ grade, originalGradeNorm grade scalar ≤ tangentialBoundaryConstant grade *
          (originalRecoveredGradientConstant grade * originalGradeNorm grade vector +
            originalCovariantPrimitiveConstant grade * originalGradeNorm grade right) := by
  obtain ⟨rawCovariant,rawForce,rawCofactor,xi,rawCovariantSame,rawForceSame,rawCofactorSame,xiSame,weak⟩ :=
    actualNative_scaledERRows parameters length compact lengthPositive widthHalf widthLength state small source flat
      fields member sameSources allGrades compatible M Mnonnegative stateBound vanishing nativeBound
      graded sameGrade constants estimate oneScale
  obtain ⟨weighted,force,cofactor,weightedSame,forceSame,cofactorSame,
    covariantRep,forceRep,cofactorRep,orbit,forceContinuous,cofactorContinuous⟩ :=
    actualNative_scaledMatrixRepresentatives parameters length compact lengthPositive widthHalf widthLength state small
      source flat fields member sameSources allGrades compatible vanishing graded sameGrade constants estimate oneScale
  let knownForce := (originalSourceMoments parameters (cartesianSourceVector source)).dilate oneScale
  let knownThird := ((originalSourceMoments parameters (source 3)).dilate oneScale).smul (length : ℂ)⁻¹
  let determinant := ((originalSourceMoments parameters (source 2)).dilate oneScale).smul ((1:ℂ)/(length:ℂ))
  let rawKnownForce := (originalSourceRawMoments parameters (cartesianSourceVector source)).dilate oneScale
  let rawKnownThird := ((originalSourceRawMoments parameters (source 3)).dilate oneScale).smul (length:ℂ)⁻¹
  let rawDeterminant := ((originalSourceRawMoments parameters (source 2)).dilate oneScale).smul ((1:ℂ)/(length:ℂ))
  let rows := nativeERRows weighted force cofactor knownForce knownThird determinant
  let rawRows := nativeERRows (rawCovariant.dilate oneScale) (rawForce.dilate oneScale) (rawCofactor.dilate oneScale)
    rawKnownForce rawKnownThird rawDeterminant
  have phase : StartupNativeERRowsRelated (physicalWeight parameters.sigma0 parameters.gamma 1) rows rawRows := by
    apply nativeERRows_phase
    · intro cell first second same
      simp only [physicalWeight,same]
    · exact sameScaledNative_phase parameters oneScale _ _ _ weightedSame rawCovariantSame
    · exact sameScaledNative_phase parameters oneScale _ _ _ forceSame rawForceSame
    · exact sameScaledNative_phase parameters oneScale _ _ _ cofactorSame rawCofactorSame
    · exact originalKnownSource_scaledPhase parameters (cartesianSourceVector source) oneScale
    · exact (originalKnownSource_scaledPhase parameters (source 3) oneScale).smul (length:ℂ)⁻¹
    · exact (originalKnownSource_scaledPhase parameters (source 2) oneScale).smul ((1:ℂ)/(length:ℂ))
  have scalarPhase := actualNativeXi_core_phase parameters length compact lengthPositive widthHalf widthLength
    state small source flat fields member sameSources allGrades compatible scalar scalarSame xi.field xiSame
  have psiSame : ((oneScale.val:ℂ)⁻¹ • startupMomentDilation oneScale xi.field) = xi.field := by
    rw [actualRecovery_dilation_one]
    simp only [oneScale,Complex.ofReal_one,inv_one,one_smul]
  rw [psiSame] at weak
  refine ⟨weighted,force,covariantRep,forceRep,?_⟩
  intro vector right vectorSame rightSame grade
  apply actualRetainedScalarCore_bound parameters weak phase
    (fun cell first second equal => by simp only [physicalWeight,equal]) scalar vector right scalarPhase
  · exact vectorSame
  · change originalSourceFieldLinear parameters right =
      startupGenuineQradKernel (startupMomentDilation oneScale (originalSourceMoments parameters (cartesianSourceVector source)).field) -
        (2:ℂ) • startupGenuineQradKernel (originalValueKernel planarPartMap force.field)
    rw [actualRecovery_dilation_one]
    exact rightSame

end Grad.ActualScaledNativeCoefficients
