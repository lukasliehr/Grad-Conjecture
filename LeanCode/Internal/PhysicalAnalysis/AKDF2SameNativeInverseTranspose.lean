import AKDF1OriginalCoreMatrixGraphs
import AKCA15SameRecoveredVectorPolar
import AKCF6ActualNativePuncturedGraphs
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

include compatible in
/-- The actual glued Cartesian U is the literal inverse-transpose product
of the SAME full native covariant, including the original outer boundary. -/
theorem actualNative_inverseTranspose_raw (point : ClosedDisk) (positive : 0 < ‖point.val‖) (axial : ℝ) :
    startupRawMatrix (originalInverseTransposeFamily parameters length state.val.val.epsilon state.val.val.field)
      (actualScaledCovariantRaw parameters length compact lengthPositive widthHalf widthLength state small source flat
        fields member sameSources allGrades 1) (axial,point.val) =
      actualCartesianVectorField parameters length compact lengthPositive widthHalf widthLength state small source flat
        fields member sameSources allGrades (point.val,axial) := by
  obtain ⟨angle,polar⟩ := closedPoint_has_polar_angle point
  have represented : spatialPlaneOfPair (polarCoord.symm (‖point.val‖,angle)) = point.val := by
    rw [polarPlane_originalParametrization]
    have coordinates := congrArg Subtype.val polar
    rw [Grad.Constraints.polarClosedPoint_coordinates] at coordinates
    simpa [polarPlane,collarPlane] using coordinates
  let index := selectedInnerCollar (originalExhaustionRadius length) (originalExhaustionRadius_tendsto length) ‖point.val‖ positive
  have inside : ‖point.val‖ ∈ Icc (originalExhaustionRadius length index) 1 :=
    ⟨(selectedInnerCollar_lt (originalExhaustionRadius length) (originalExhaustionRadius_tendsto length) ‖point.val‖ positive).le,point.property⟩
  have coefficientLow := originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho
    state.val.val.epsilon state.val.val.field small
  have covariant := actualScaledCovariantRaw_polar parameters length compact lengthPositive widthHalf widthLength
    state small source flat fields member sameSources allGrades compatible 1 ‖point.val‖
    (by simpa only [one_mul] using positive) positive.le (by rw [abs_of_nonneg positive.le]; exact point.property)
    index (by simpa only [one_mul] using inside) angle axial
  rw [polar] at covariant
  simp only [one_mul] at covariant
  rw [startupRawMatrix_value, covariant,
    actualCartesianVectorField_same parameters length compact lengthPositive widthHalf widthLength state small source flat
      fields member sameSources allGrades compatible index (point.val,axial) inside]
  have uPolar := (cartesianCorrectedVectorCurves parameters length compact lengthPositive widthHalf widthLength
    state small source flat fields member sameSources allGrades index).cartesianField_polar
    ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) ‖point.val‖ positive angle axial
  rw [represented] at uPolar
  rw [uPolar]
  have recovered := (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength
    state small source flat fields member sameSources allGrades index).fullField_physicalUFromPolar
    parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientLow
    (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index)
    ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) ‖point.val‖ inside (angle,axial)
  change _ = ((cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength
    state small source flat fields member sameSources allGrades index).physicalUFromPolar
    parameters length state.val.val.rho state.val.val.epsilon state.val.val.field coefficientLow
    (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index)
    ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))).fullField
    ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (‖point.val‖,angle,axial)
  rw [recovered]
  have diskSame : Grad.SourceCollarDivision.polarClosedPoint ‖point.val‖ angle
      ((originalExhaustionRadius_positive length lengthPositive index).le.trans inside.1) inside.2 = point := by
    apply Subtype.ext
    simpa only [Grad.SourceCollarDivision.polarClosedPoint,polarPlane_originalParametrization] using represented
  rw [diskSame]
  exact operatorMatrix_action _ _

end Grad.ActualScaledNativeCoefficients
