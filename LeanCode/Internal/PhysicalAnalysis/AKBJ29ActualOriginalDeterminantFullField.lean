import AKBJ25ActualNativeCofactorCurves
import AKBJ26CompletedCofactorCartesianFidelity
import AKBE10ActualObservedCartesianDeterminant
import AKBJ12ThirdCellLinearAlgebra

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace Grad.ActualScalarWeakEquations
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
open Grad.AnnularGeneralSourceRegularity Grad.ActualSmoothPhysicalField Grad.PuncturedRetainedEnergy
variable (compatible : ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)

open Grad.ActualCartesianWeakEquations Grad.ActualCartesianEquations Grad.PhysicalFamily

open Grad.ActualDeterminantEquations

private theorem sourceCofactorCartesian_sameCompleted (index : ℕ) :
    (cartesianSourceCofactorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).cartesianField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) = (sameCompletedCofactorCurves parameters length compact (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index) ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) state (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small) (actualCartesianSevenCurves parameters length compact (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index) lengthPositive widthHalf widthLength state (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small) (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small) source flat (fields index) (member index) (sameSources index) (allGrades index))).cartesianField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) := by
  rfl

/-- The actual original determinant equation for the native full cofactor convolution used by integrability. No radial PDE premise is supplied. -/
theorem actualOriginalDeterminant_full (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Ioo (originalExhaustionRadius length index) 1) (angles : ℝ × ℝ) :
    removePolarMean (fun query => cartesianDeterminantDivergence length
      ((cartesianSourceCofactorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).cartesianField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))) (polarPlane (radius,query.1),query.2)) angles =
      corePolarValue parameters (source 2) radius ((originalExhaustionRadius_positive length lengthPositive index).le.trans inside.1.le) inside.2.le angles 0 := by
  have sameField : (fun query : ℝ × ℝ => cartesianDeterminantDivergence length
      ((cartesianSourceCofactorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).cartesianField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))) (polarPlane (radius,query.1),query.2)) =
      fun query => cartesianDeterminantDivergence length
        ((samePolarCofactorVector parameters length compact (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index) ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) state (actualCartesianSevenCurves parameters length compact (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index) lengthPositive widthHalf widthLength state (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small) (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small) source flat (fields index) (member index) (sameSources index) (allGrades index))).cartesianCovariant.cartesianField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))) (polarPlane (radius,query.1),query.2) := by
    funext query
    have normInside : ‖polarPlane (radius,query.1)‖ ∈ Ioo (originalExhaustionRadius length index) 1 := by
      simpa only [polarPlane_norm,abs_of_pos ((originalExhaustionRadius_positive length lengthPositive index).trans inside.1)] using inside
    have nativeSame := congrArg (fun field : SpatialPlane × ℝ → ComplexEuclidean 3 =>
      fderiv ℝ field (polarPlane (radius,query.1),query.2))
      (sourceCofactorCartesian_sameCompleted parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index)
    have jetSame := sameCompletedCofactor_fderiv parameters length compact (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index) ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) state (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small) (actualCartesianSevenCurves parameters length compact (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index) lengthPositive widthHalf widthLength state (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small) (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small) source flat (fields index) (member index) (sameSources index) (allGrades index)) (polarPlane (radius,query.1),query.2) normInside
    exact congrArg (fun derivative : SpatialPlane × ℝ →L[ℝ] ComplexEuclidean 3 =>
      (length : ℂ) * (derivative (spatialBasis 0,0) 0 + derivative (spatialBasis 1,0) 1) + derivative (0,1) 2)
      (nativeSame.trans jetSame)
  rw [sameField]
  exact actualObserved_originalDeterminant parameters length compact (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index) lengthPositive widthHalf widthLength state (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small) (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    source flat (fields index) (member index) (sameSources index) (allGrades index) (actualCartesianSevenCurves parameters length compact (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index) lengthPositive widthHalf widthLength state (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small) (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small) source flat (fields index) (member index) (sameSources index) (allGrades index)) radius inside angles

end Grad.ActualScalarWeakEquations
