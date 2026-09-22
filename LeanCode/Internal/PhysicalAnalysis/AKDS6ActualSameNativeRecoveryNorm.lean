import AKDS5ActualSameNativeVectorTame
import AKDB12ActualNativeScalarOriginalCore
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

open Grad.NonlinearProduct
open Grad.ActualScalarWeakEquations

include compatible in
/-- Full actual original U/S recovery, with a single coefficient-high
factor multiplying only the independent covariant base norm. -/
theorem actualNative_recovery_oneHigh
    (covariant : ACore parameters 3) (xi : ACore parameters 1)
    (covariantSame : ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters covariant).value (point,(axial : CellCircle))=
        actualCartesianCovariantFamilyField parameters length compact lengthPositive widthHalf widthLength state small
          source flat fields member sameSources allGrades (point.val,axial))
    (xiSame : ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
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
        ((actualOriginalInverseTranspose_sameCore_bound parameters length).choose grade +
          1+scalarRecoveryConstant grade) *
        (originalGradeNorm grade covariant + originalGradeNorm grade xi +
          (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (4+grade))*
            originalGradeNorm 0 covariant) := by
  let vectorResult := actualNativeVector_of_covariantCore_tame parameters length compact lengthPositive widthHalf widthLength
    state small source flat fields member sameSources allGrades compatible covariant covariantSame
  let vector := vectorResult.choose
  let scalar := recoveredScalarOriginalCore parameters covariant xi
  refine ⟨vector,scalar,vectorResult.choose_spec.1,?_,?_⟩
  · exact actualNativeScalar_fromCovariantXi_originalCore parameters length compact lengthPositive widthHalf widthLength
      state small source flat fields member sameSources allGrades compatible covariant xi covariantSame xiSame
  intro grade
  let payment := originalGradeNorm grade covariant + originalGradeNorm grade xi +
    (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (4+grade))*
      originalGradeNorm 0 covariant
  have covNonnegative := originalGradeNorm_nonnegative grade covariant
  have xiNonnegative := originalGradeNorm_nonnegative grade xi
  have baseNonnegative := mul_nonneg
    (add_nonneg zero_le_one (physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon (4+grade)))
    (originalGradeNorm_nonnegative 0 covariant)
  have covLe : originalGradeNorm grade covariant ≤ payment := by dsimp [payment]; linarith
  have xiLe : originalGradeNorm grade xi ≤ payment := by dsimp [payment]; linarith
  have vectorPayment : originalGradeNorm grade covariant +
      (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (4+grade))*
        originalGradeNorm 0 covariant ≤ payment := by dsimp [payment]; linarith
  have vectorBound := (vectorResult.choose_spec.2 grade).trans
    (mul_le_mul_of_nonneg_left vectorPayment
      ((actualOriginalInverseTranspose_sameCore_bound parameters length).choose_spec.1 grade))
  have scalarBound := (recoveredScalarOriginalCore_bound parameters grade covariant xi).trans
    (add_le_add xiLe (mul_le_mul_of_nonneg_left covLe (scalarRecoveryConstant_nonnegative grade)))
  exact (add_le_add vectorBound scalarBound).trans_eq (by ring)

end Grad.ActualScaledNativeCoefficients
