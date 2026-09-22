import AKCA17SameCorrectedScalarMean

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
open scoped Topology ContDiff ENNReal BigOperators
namespace Grad.OriginalCoreRealization
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

include compatible
open Grad.ActualCartesianFlux Grad.NonlinearRange Grad.SourceCollar

/-- SAME original scalar S, with the corrected S/r field retained literally. -/
def actualNativeScalarField (point : SpatialPlane×ℝ) : ComplexEuclidean 1 :=
  ‖point.1‖ • actualCartesianScalarOverRadiusField parameters length compact lengthPositive widthHalf widthLength state small
    source flat fields member sameSources allGrades point

 theorem actualNativeScalarField_polar (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc (originalExhaustionRadius length index) 1) (polar axial : ℝ) :
    actualNativeScalarField parameters length compact lengthPositive widthHalf widthLength state small source flat
      fields member sameSources allGrades (polarPlane (radius,polar),axial)=
      radius • (cartesianCorrectedScalarOverRadiusCurves parameters length compact lengthPositive widthHalf widthLength state small source flat
        fields member sameSources allGrades index).fullField
        ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (radius,polar,axial) := by
  have positive : 0 < radius := (originalExhaustionRadius_positive length lengthPositive index).trans_le inside.1
  have pointNorm : ‖polarPlane (radius,polar)‖=radius := (polarPlane_norm radius polar).trans (abs_of_pos positive)
  rw [actualNativeScalarField,pointNorm,
    actualCartesianScalarOverRadiusField_same parameters length compact lengthPositive widthHalf widthLength state small source flat fields
      member sameSources allGrades compatible index _ (by change ‖polarPlane (radius,polar)‖∈_; rw [pointNorm]; exact inside)]
  congr 1
  simpa only [polarPlane_originalParametrization] using
    (cartesianCorrectedScalarOverRadiusCurves parameters length compact lengthPositive widthHalf widthLength state small source flat
      fields member sameSources allGrades index).cartesianField_polar
      ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) radius positive polar axial

 theorem actualNativeScalarField_mean (radius : ℝ) (radiusPositive : 0 < radius) (radiusBounded : radius≤1) (axial : ℝ) :
    angularCoefficient (fun polar => actualNativeScalarField parameters length compact lengthPositive widthHalf widthLength state small source flat
      fields member sameSources allGrades (polarPlane (radius,polar),axial)) 0=0 := by
  let index := selectedInnerCollar (originalExhaustionRadius length) (originalExhaustionRadius_tendsto length) radius radiusPositive
  have inside : radius ∈ Icc (originalExhaustionRadius length index) 1 :=
    ⟨(selectedInnerCollar_lt (originalExhaustionRadius length) (originalExhaustionRadius_tendsto length) radius radiusPositive).le,radiusBounded⟩
  simp_rw [actualNativeScalarField_polar parameters length compact lengthPositive widthHalf widthLength state small source flat
    fields member sameSources allGrades compatible index radius inside]
  apply correctedScalar_mean (cartesianSourceXiOverRadiusCurves parameters length compact lengthPositive widthHalf widthLength state small source flat
    fields member sameSources allGrades index) (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat
    fields member sameSources allGrades index) _ _ radius inside axial
  intro cell
  exact originalScalarOverRadius_zeroAngular parameters length (originalExhaustionRadius length index)
    (originalExhaustionRadius_positive length lengthPositive index)
    ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) lengthPositive
    (actualOriginalSourceDatum parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
      (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
      (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) 0 source flat)
    (fields index) cell

 theorem actualRecoveredScalar_mean (scalar : ACore parameters 1)
    (same : ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters scalar).value (point,(axial : CellCircle)) =
        actualNativeScalarField parameters length compact lengthPositive widthHalf widthLength state small
          source flat fields member sameSources allGrades (point.val,axial)) :
    Grad.Constraints.angularCore parameters 0 scalar=0 := by
  apply angularCore_zero_of_physicalMeans
  intro radius positive bounded axial
  have samePolar (polar : ℝ) : coreValue scalar (Grad.Constraints.polarClosedPoint radius bounded polar) axial=
      actualNativeScalarField parameters length compact lengthPositive widthHalf widthLength state small source flat
        fields member sameSources allGrades (polarPlane (radius,polar),axial) := by
    rw [coreValue_originalPhysical,same]
    · rw [← divisionPolarPoint_eq_original radius polar positive.le ((le_abs_self radius).trans bounded)]
      rfl
    · rw [Grad.CartesianStartup.startupPolarClosedPoint_norm,abs_of_pos positive]
      exact positive
  have period : Function.Periodic (fun polar => coreValue scalar (Grad.Constraints.polarClosedPoint radius bounded polar) axial 0) (2*Real.pi) := by
    intro polar
    dsimp only
    rw [Grad.Constraints.polarClosedPoint_periodic]
  rw [sourceAngularAverage_eq_coefficient _ period,
    ← angularCoefficient_component (fun polar => coreValue scalar (Grad.Constraints.polarClosedPoint radius bounded polar) axial)
      (sourceCoreValue_polar_continuous scalar radius bounded axial) 0 0]
  simp_rw [samePolar]
  exact congrArg (fun value : ComplexEuclidean 1 => value 0)
    (actualNativeScalarField_mean parameters length compact lengthPositive widthHalf widthLength state small source flat
      fields member sameSources allGrades compatible radius positive ((le_abs_self radius).trans bounded) axial)

end Grad.OriginalCoreRealization
