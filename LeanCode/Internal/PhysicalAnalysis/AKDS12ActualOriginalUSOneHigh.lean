import AKDS11ActualOriginalXiOneHigh
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option maxRecDepth 3000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators

namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.ActualPhysicalField

def actualOriginalUSNormConstant (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) : ℝ :=
  ((actualOriginalInverseTranspose_sameCore_bound parameters length).choose grade +
    1+scalarRecoveryConstant grade)*(1+actualOriginalXiNormConstant parameters length grade)

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



/-- Complete physical U/S recovery from the SAME original covariant core.
The actual scalar equation, all projections and matrix actions are now
estimated. The only unknown high norm remaining is the covariant norm. -/
theorem actualNative_US_ofCovariant_oneHigh
    (covariant : ACore parameters 3) (xi : ACore parameters 1)
    (covariantSame : ∀ (point : ClosedDisk),0<‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters covariant).value (point,(axial : CellCircle))=
        actualCartesianCovariantFamilyField parameters length compact lengthPositive widthHalf widthLength state small
          source flat fields member sameSources allGrades (point.val,axial))
    (xiSame : ∀ (point : ClosedDisk),0<‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters xi).value (point,(axial : CellCircle))=
        actualCartesianXiFamilyField parameters length compact lengthPositive widthHalf widthLength state small
          source flat fields member sameSources allGrades (point.val,axial)) :
    ∃ vector scalar,
      (∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
        (originalPhysicalClosedJet parameters vector).value (point,(axial : CellCircle))=
          actualCartesianVectorField parameters length compact lengthPositive widthHalf widthLength state small
            source flat fields member sameSources allGrades (point.val,axial)) ∧
      (∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
        (originalPhysicalClosedJet parameters scalar).value (point,(axial : CellCircle))=
          actualNativeScalarField parameters length compact lengthPositive widthHalf widthLength state small
            source flat fields member sameSources allGrades (point.val,axial)) ∧
      ∀ grade, originalGradeNorm grade vector + originalGradeNorm grade scalar ≤
        actualOriginalUSNormConstant parameters length grade *
          (originalGradeNorm grade covariant + originalGradeNorm grade (cartesianSourceVector source) +
            (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (5+grade))*
              originalGradeNorm 0 covariant) := by
  obtain ⟨vector,scalar,vectorSame,scalarSame,recovery⟩ := actualNative_recovery_oneHigh parameters length compact
    lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible
    covariant xi covariantSame xiSame
  have xiBound := actualNativeXi_ofCovariant_oneHigh parameters length compact lengthPositive widthHalf widthLength
    state small source flat fields member sameSources allGrades compatible M Mnonnegative stateBound vanishing
    nativeBound graded sameGrade constants estimate covariant xi covariantSame xiSame
  refine ⟨vector,scalar,vectorSame,scalarSame,?_⟩
  intro grade
  let payment := originalGradeNorm grade covariant + originalGradeNorm grade (cartesianSourceVector source) +
    (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (5+grade))*
      originalGradeNorm 0 covariant
  have extra := mul_le_mul_of_nonneg_right
    (add_le_add_left (physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon
      (by omega : 4+grade≤5+grade)) 1) (originalGradeNorm_nonnegative 0 covariant)
  have covPaid : originalGradeNorm grade covariant +
      (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (4+grade))*
        originalGradeNorm 0 covariant ≤ payment := by
    dsimp [payment]; linarith [originalGradeNorm_nonnegative grade (cartesianSourceVector source)]
  have fullPaid : originalGradeNorm grade covariant + originalGradeNorm grade xi +
      (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (4+grade))*
        originalGradeNorm 0 covariant ≤ (1+actualOriginalXiNormConstant parameters length grade)*payment := by
    have xiPaid := xiBound grade
    change originalGradeNorm grade xi ≤ actualOriginalXiNormConstant parameters length grade*payment at xiPaid
    nlinarith only [covPaid,xiPaid]
  have factorNonnegative : 0≤(actualOriginalInverseTranspose_sameCore_bound parameters length).choose grade+
      1+scalarRecoveryConstant grade :=
    add_nonneg (add_nonneg ((actualOriginalInverseTranspose_sameCore_bound parameters length).choose_spec.1 grade)
      zero_le_one) (scalarRecoveryConstant_nonnegative grade)
  exact (recovery grade).trans ((mul_le_mul_of_nonneg_left fullPaid factorNonnegative).trans_eq
    (by unfold actualOriginalUSNormConstant; dsimp only [payment]; ring))

end Grad.ActualScaledNativeCoefficients
