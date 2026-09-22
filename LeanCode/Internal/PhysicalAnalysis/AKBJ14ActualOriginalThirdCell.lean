import AKBJ13ActualOriginalThirdFullValue
import AKBJ19NativeDerivativeSections
import AKBK9SameXiDerivativeAngularContinuity

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
include compatible

/-- The actual original third equation in every signed integer Fourier cell, with the original reconstructed covariant and Xi. -/
theorem actualOriginalThird_cell_polar (cell : ℤ) (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Ioo (originalExhaustionRadius length index) 1) (polar : ℝ) :
    thirdRowValue length
      (fderiv ℝ (actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) (polarPlane (radius,polar))
        (radius • planeQuarterTurn (radialDirection polar)))
      ((Complex.I * (cell : ℂ)) • actualCartesianXiCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell (polarPlane (radius,polar)))
      (actualCartesianProjectedThirdForceCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell (polarPlane (radius,polar))) =
      originalCoreCell parameters (source 3) cell (polarPlane (radius,polar)) := by
  let rotation := fun axial => fderiv ℝ ((cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).cartesianCovariant.cartesianField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))) (polarPlane (radius,polar),axial) (radius • planeQuarterTurn (radialDirection polar),0)
  let xiAxial := fun axial => fderiv ℝ (cartesianPhysicalField (originalPhysicalComponentField parameters (originalExhaustionRadius length index) length (originalExhaustionRadius_positive length lengthPositive index) ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) lengthPositive (originalWeightedRetainedObservation parameters (originalExhaustionRadius length index) length (originalExhaustionRadius_positive length lengthPositive index) ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index)) 1)) (polarPlane (radius,polar),axial) (0,1)
  let correction := fun axial => (-2 * (length : ℂ)) • (((cartesianSourceForceMatrixCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).bulkUnit (0 : Fin 1) 2).meanFree).fullField ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (radius,polar,axial)
  have rotationJoint := nativeLocalField_fderiv_circle_continuous (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).cartesianCovariant
    ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) radius inside
  have rotationContinuous : Continuous rotation :=
    originalDerivative_axialContinuous _ radius rotationJoint polar (radius • planeQuarterTurn (radialDirection polar),0)
  have xiJoint := actualCartesianXiOriginal_fderiv_circle_continuous parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible index radius inside
  have xiContinuous : Continuous xiAxial := originalDerivative_axialContinuous _ radius xiJoint polar (0,1)
  have correctionContinuous : Continuous correction :=
    ((((cartesianSourceForceMatrixCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).bulkUnit (0 : Fin 1) 2).meanFree).fullField_continuous_angles ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) radius ⟨inside.1.le,inside.2.le⟩).comp
      (continuous_const.prodMk continuous_id) |>.const_smul (-2 * (length : ℂ))
  have full : (fun axial => thirdRowValue length (rotation axial) (xiAxial axial) (correction axial)) = (fun axial => corePolarValue parameters (source 3) radius ((originalExhaustionRadius_positive length lengthPositive index).le.trans inside.1.le) inside.2.le (polar,axial)) := by
    funext axial
    exact actualOriginalThird_fullValue parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index radius inside (polar,axial)
  have fourier := congrArg (fun field : ℝ → ComplexEuclidean 1 => angularCoefficient field cell) full
  rw [thirdRowValue_axialCell length rotation xiAxial correction rotationContinuous xiContinuous correctionContinuous cell] at fourier
  have normInside : ‖polarPlane (radius,polar)‖ ∈ Ioo (originalExhaustionRadius length index) 1 := by
    simpa only [polarPlane_norm,abs_of_pos ((originalExhaustionRadius_positive length lengthPositive index).trans inside.1)] using inside
  have rotationSame := actualCartesianCovariantCell_fderiv_local parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell index (polarPlane (radius,polar)) normInside
    (radius • planeQuarterTurn (radialDirection polar))
  have xiSame := actualCartesianXiCell_axial_original parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell index (polarPlane (radius,polar)) normInside
  have correctionSame := actualProjectedThirdForceCell_full parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades compatible cell index radius ⟨inside.1.le,inside.2.le⟩ polar
  have sourceSame := originalCoreCell_polarCoefficient parameters (source 3) cell radius ((originalExhaustionRadius_positive length lengthPositive index).le.trans inside.1.le) inside.2.le polar
  change thirdRowValue length (angularCoefficient rotation cell) (angularCoefficient xiAxial cell) (angularCoefficient correction cell) = _ at fourier
  rw [← rotationSame,xiSame,← correctionSame,sourceSame] at fourier
  exact fourier

end Grad.ActualScalarWeakEquations
