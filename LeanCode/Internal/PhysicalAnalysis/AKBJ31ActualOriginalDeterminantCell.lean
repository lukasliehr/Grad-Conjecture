import AKBJ29ActualOriginalDeterminantFullField
import AKBJ30ActualDeterminantCellDerivative
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
private theorem determinantDivergence_circle_continuous (L radius : ℝ) (field : SpatialPlane × ℝ → ComplexEuclidean 3)
    (continuousDerivative : Continuous (fun angles : ℝ × ℝ => fderiv ℝ field (polarPlane (radius,angles.1),angles.2))) :
    Continuous (fun angles : ℝ × ℝ => cartesianDeterminantDivergence L field (polarPlane (radius,angles.1),angles.2)) := by
  have first := continuousDerivative.clm_apply (show Continuous (fun _ : ℝ × ℝ => (spatialBasis 0,(0 : ℝ))) from continuous_const)
  have second := continuousDerivative.clm_apply (show Continuous (fun _ : ℝ × ℝ => (spatialBasis 1,(0 : ℝ))) from continuous_const)
  have third := continuousDerivative.clm_apply (show Continuous (fun _ : ℝ × ℝ => ((0 : SpatialPlane),(1 : ℝ))) from continuous_const)
  have firstScalar := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => ℂ) 0).continuous.comp first
  have secondScalar := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => ℂ) 1).continuous.comp second
  have thirdScalar := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 3 => ℂ) 2).continuous.comp third
  exact ((firstScalar.add secondScalar).const_mul (L : ℂ)).add thirdScalar

def sameCellDeterminantDivergence (length : ℝ) (cell : ℤ) (field : SpatialPlane → ComplexEuclidean 3) (point : SpatialPlane) : ℂ :=
  determinantRowValue length (fderiv ℝ field point (spatialBasis 0)) (fderiv ℝ field point (spatialBasis 1))
    ((Complex.I * (cell : ℂ)) • field point)

include compatible in
/-- The genuine original determinant row in every axial cell, with P0 preserved on the full signed cofactor divergence. -/
theorem actualOriginalDeterminant_cell_polar (cell : ℤ) (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Ioo (originalExhaustionRadius length index) 1) (polar : ℝ) :
    sameCellDeterminantDivergence length cell (actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) (polarPlane (radius,polar)) -
      angularCoefficient (fun angle => sameCellDeterminantDivergence length cell (actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) (polarPlane (radius,angle))) 0 =
      originalCoreCell parameters (source 2) cell (polarPlane (radius,polar)) 0 := by
  let full := fun angles : ℝ × ℝ => cartesianDeterminantDivergence length ((cartesianSourceCofactorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).cartesianField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))) (polarPlane (radius,angles.1),angles.2)
  have fullContinuous : Continuous full := determinantDivergence_circle_continuous length radius _
    (nativeLocalField_fderiv_circle_continuous (cartesianSourceCofactorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index) ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) radius inside)
  have fullEquation : (fun axial => removePolarMean full (polar,axial)) =
      fun axial => corePolarValue parameters (source 2) radius ((originalExhaustionRadius_positive length lengthPositive index).le.trans inside.1.le) inside.2.le (polar,axial) 0 := by
    funext axial
    exact actualOriginalDeterminant_full parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index radius inside (polar,axial)
  have fourier := congrArg (fun field : ℝ → ℂ => angularCoefficient field cell) fullEquation
  rw [scalarProjection_axialCell full fullContinuous cell polar] at fourier
  have cellSame (angle : ℝ) : angularCoefficient (fun axial => full (angle,axial)) cell =
      sameCellDeterminantDivergence length cell (actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) (polarPlane (radius,angle)) :=
    actualDeterminantDivergence_axialCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell index radius inside angle
  simp_rw [cellSame] at fourier
  have sourceContinuous := (corePolarValue_continuous parameters (source 2) radius ((originalExhaustionRadius_positive length lengthPositive index).le.trans inside.1.le) inside.2.le).comp
    (show Continuous (fun axial : ℝ => (polar,axial)) from continuous_const.prodMk continuous_id)
  have sourceComponent := (angularCoefficient_component
    (fun axial => corePolarValue parameters (source 2) radius ((originalExhaustionRadius_positive length lengthPositive index).le.trans inside.1.le) inside.2.le (polar,axial))
    sourceContinuous 0 cell).symm
  have sourceSame := congrArg (fun value : ComplexEuclidean 1 => value 0)
    (originalCoreCell_polarCoefficient parameters (source 2) cell radius ((originalExhaustionRadius_positive length lengthPositive index).le.trans inside.1.le) inside.2.le polar)
  exact fourier.trans (sourceComponent.trans sourceSame)

end Grad.ActualScalarWeakEquations
