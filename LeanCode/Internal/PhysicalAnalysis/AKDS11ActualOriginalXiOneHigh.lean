import AKDS9ActualOriginalForceCoreTame
import AKDS10OriginalXiRecoveryInputs
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators

namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.CartesianStartup Grad.NonlinearProduct Grad.SourceBoundaryTrace
open Grad.Constraints.Gauges Grad.GaugeCoefficients.Physical.RadialLedger Grad.ActualPhysicalField

def actualOriginalXiNormConstant (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) : ℝ :=
  tangentialBoundaryConstant grade *
    (originalRecoveredGradientConstant grade *
        (‖planarPartMap‖*(startupOriginalCircle_core_bound parameters grade).choose) +
      originalCovariantPrimitiveConstant grade * (startupOriginalQrad_core_bound parameters grade).choose *
        (1+2*‖planarPartMap‖*(actualOriginalForce_core_tame parameters length).choose grade))

end Grad.OriginalCoreRealization

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
open Grad.ActualCartesianWeakEquations


/-- Full actual original Xi recovery. All scalar weak equations and phase
identities are supplied from the SAME native solution; only its covariant
norm remains on the right, with a true one-high coefficient payment. -/
theorem actualNativeXi_ofCovariant_oneHigh
    (covariant : ACore parameters 3) (scalar : ACore parameters 1)
    (covariantSame : ∀ (point : ClosedDisk),0<‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters covariant).value (point,(axial : CellCircle))=
        actualCartesianCovariantFamilyField parameters length compact lengthPositive widthHalf widthLength state small
          source flat fields member sameSources allGrades (point.val,axial))
    (scalarSame : ∀ (point : ClosedDisk),0<‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters scalar).value (point,(axial : CellCircle))=
        actualCartesianXiFamilyField parameters length compact lengthPositive widthHalf widthLength state small
          source flat fields member sameSources allGrades (point.val,axial)) :
    ∀ grade,originalGradeNorm grade scalar ≤ actualOriginalXiNormConstant parameters length grade *
      (originalGradeNorm grade covariant + originalGradeNorm grade (cartesianSourceVector source) +
        (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (5+grade))*
          originalGradeNorm 0 covariant) := by
  have low := originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho
    state.val.val.epsilon state.val.val.field small
  let forceResult := (actualOriginalForce_core_tame parameters length).choose_spec.2 state.val.val.field
    state.val.val.rho state.val.val.epsilon low covariant
  let forceCore := forceResult.choose
  have forceCoreSame := forceResult.choose_spec.1
  have forceCoreBound := forceResult.choose_spec.2
  obtain ⟨weighted,force,covariantRep,forceRep,recovery⟩ :=
    actualNativeXi_core_recovery_bound parameters length compact lengthPositive widthHalf widthLength state small
      source flat fields member sameSources allGrades compatible M Mnonnegative stateBound vanishing nativeBound
      graded sameGrade constants estimate scalar scalarSame
  let raw := actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small
    source flat fields member sameSources allGrades 1
  have coreRep : StartupWeightedRep parameters.sigma0 parameters.gamma 1
      (originalSourceFieldLinear parameters covariant) raw := by
    apply originalCore_sameWeightedRep parameters covariant raw
    intro point positive axial
    simpa only [raw,actualScaledCovariantRaw,one_smul] using covariantSame point positive axial
  have weightedSame : originalSourceFieldLinear parameters covariant = weighted.field := coreRep.ext covariantRep
  have regular := actualScaledCovariantRaw_regular parameters length compact lengthPositive widthHalf widthLength
    state small source flat fields member sameSources allGrades compatible 1 zero_lt_one le_rfl
  have matrixRep := coreRep.matrix (unitDiskAdmissible parameters)
    (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field)
    (forceMatrixFamily_coherent parameters length state.val.val.rho state.val.val.epsilon state.val.val.field low) regular
  have forceSame : originalSourceFieldLinear parameters forceCore = force.field := by
    change (originalSourceMoments parameters forceCore).field = _
    rw [forceCoreSame]
    apply matrixRep.ext
    have sameRaw : nativeScaledMatrixRaw 1
        (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field) raw =
        startupRawMatrix (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field) raw := by
      funext pair
      simp only [nativeScaledMatrixRaw,startupRawMatrix,one_smul]
    change StartupWeightedRep parameters.sigma0 parameters.gamma 1 force.field
      (nativeScaledMatrixRaw 1 (forceMatrixFamily parameters length state.val.val.epsilon state.val.val.field) raw) at forceRep
    rwa [sameRaw] at forceRep
  obtain ⟨vector,right,vectorSame,rightSame,inputs⟩ :=
    originalXiRecoveryInputs parameters covariant forceCore (cartesianSourceVector source)
  rw [weightedSame] at vectorSame
  rw [forceSame] at rightSame
  have bound := recovery vector right vectorSame rightSame
  intro grade
  let payment := originalGradeNorm grade covariant + originalGradeNorm grade (cartesianSourceVector source) +
    (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (5+grade))*originalGradeNorm 0 covariant
  have extraNonnegative := mul_nonneg
    (add_nonneg zero_le_one (physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon (5+grade)))
    (originalGradeNorm_nonnegative 0 covariant)
  have covLe : originalGradeNorm grade covariant ≤ payment := by
    dsimp [payment]; linarith [originalGradeNorm_nonnegative grade (cartesianSourceVector source)]
  have knownLe : originalGradeNorm grade (cartesianSourceVector source) ≤ payment := by
    dsimp [payment]; linarith [originalGradeNorm_nonnegative grade covariant]
  have forcePayment : originalGradeNorm grade covariant +
      (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (5+grade))*originalGradeNorm 0 covariant ≤ payment := by
    dsimp [payment]; linarith [originalGradeNorm_nonnegative grade (cartesianSourceVector source)]
  have forcePaid := (forceCoreBound grade).trans (mul_le_mul_of_nonneg_left forcePayment
    ((actualOriginalForce_core_tame parameters length).choose_spec.1 grade))
  have vectorPaid := (inputs grade).1.trans (mul_le_mul_of_nonneg_left covLe
    (mul_nonneg (norm_nonneg _) (startupOriginalCircle_core_bound parameters grade).choose_spec.1))
  have rightPaid := (inputs grade).2.trans (mul_le_mul_of_nonneg_left
    (add_le_add knownLe (mul_le_mul_of_nonneg_left forcePaid (mul_nonneg (by norm_num) (norm_nonneg _))))
    (startupOriginalQrad_core_bound parameters grade).choose_spec.1)
  have paid := (bound grade).trans (mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left vectorPaid (originalRecoveredGradientConstant_nonnegative grade))
      (mul_le_mul_of_nonneg_left rightPaid (originalCovariantPrimitiveConstant_nonnegative grade)))
    (tangentialBoundaryConstant_nonnegative grade))
  exact paid.trans_eq (by unfold actualOriginalXiNormConstant; dsimp only [payment]; ring)

end Grad.ActualScaledNativeCoefficients
