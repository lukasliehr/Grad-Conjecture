import AKBJ27SameCofactorCellDerivatives
import AKBJ28DeterminantFourierAlgebra
import AKBJ26CompletedCofactorCartesianFidelity
import AKBK2SameLocalCellDerivatives

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
open Grad.ActualSmoothPhysicalField Grad.PuncturedRetainedEnergy
variable (compatible : ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)

open Grad.ActualCartesianFlux

open Grad.ActualNativeCellMoments Grad.ActualCurrentPrimitives

open Grad.ActualForceMoments Grad.CartesianStartup Grad.BoundaryLift Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger

open Grad.ActualDeterminantEquations Grad.ActualCartesianWeakEquations Grad.PDEBootstrap Grad.PhysicalFamily
include compatible

/-- Axial differentiation is the signed integer symbol on the SAME full cofactor output. -/
theorem actualCofactorCell_axial_local (cell : ℤ) (index : ℕ) (point : SpatialPlane)
    (inside : ‖point‖ ∈ Ioo (originalExhaustionRadius length index) 1) :
    angularCoefficient (fun axial => fderiv ℝ ((cartesianSourceCofactorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).cartesianField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))) (point,axial) (0,1)) cell =
      (Complex.I * (cell : ℂ)) • (actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) point := by
  let domain : Set SpatialPlane := {query | ‖query‖ ∈ Ioo (originalExhaustionRadius length index) 1}
  have regular : ContDiffOn ℝ ∞ ((cartesianSourceCofactorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).cartesianField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))) (domain ×ˢ (univ : Set ℝ)) := by
    intro query collarMembership
    exact ((cartesianSourceCofactorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).cartesianField_smoothAt ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) query collarMembership.1).contDiffWithinAt
  have given := originalCell_axialDerivative (isOpen_Ioo.preimage continuous_norm)
    ((cartesianSourceCofactorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).cartesianField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))) regular point inside
    (nativeLocalField_axialPeriodic (cartesianSourceCofactorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index) ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) point) cell
  rw [← actualCofactorCell_local parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell index point inside] at given
  exact given

/-- The literal L,L,1 determinant divergence is projected to its actual integer cell after the coefficient convolution. -/
theorem actualDeterminantDivergence_axialCell (cell : ℤ) (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Ioo (originalExhaustionRadius length index) 1) (polar : ℝ) :
    angularCoefficient (fun axial => cartesianDeterminantDivergence length
      ((cartesianSourceCofactorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).cartesianField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))) (polarPlane (radius,polar),axial)) cell =
      determinantRowValue length
        (fderiv ℝ (actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) (polarPlane (radius,polar)) (spatialBasis 0))
        (fderiv ℝ (actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) (polarPlane (radius,polar)) (spatialBasis 1))
        ((Complex.I * (cell : ℂ)) • (actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) (polarPlane (radius,polar))) := by
  have joint := nativeLocalField_fderiv_circle_continuous (cartesianSourceCofactorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index) ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) radius inside
  have firstContinuous := originalDerivative_axialContinuous _ radius joint polar (spatialBasis 0,0)
  have secondContinuous := originalDerivative_axialContinuous _ radius joint polar (spatialBasis 1,0)
  have thirdContinuous := originalDerivative_axialContinuous _ radius joint polar (0,1)
  have given := determinantRowValue_axialCell length _ _ _ firstContinuous secondContinuous thirdContinuous cell
  have normInside : ‖polarPlane (radius,polar)‖ ∈ Ioo (originalExhaustionRadius length index) 1 := by
    simpa only [polarPlane_norm,abs_of_pos ((originalExhaustionRadius_positive length lengthPositive index).trans inside.1)] using inside
  have firstSame := actualCofactorCell_fderiv_local parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell index (polarPlane (radius,polar)) normInside (spatialBasis 0)
  have secondSame := actualCofactorCell_fderiv_local parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell index (polarPlane (radius,polar)) normInside (spatialBasis 1)
  have thirdSame := actualCofactorCell_axial_local parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell index (polarPlane (radius,polar)) normInside
  rw [← firstSame,← secondSame,thirdSame] at given
  exact given

end Grad.ActualScalarWeakEquations
