import AKDB11ActualNativeScalarAllOrder
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
open Grad.ActualCartesianWeakEquations


open Grad.ActualScalarWeakEquations


open Grad.NonlinearRange Grad.OriginalKernelHomogeneousGraph Grad.OriginalKernelCovariantRecovery
open Grad.DiskExtension.Operator Grad.SourceCollar Grad.Constraints

include compatible in
/-- Genuine S recovery from the SAME original covariant and retained Xi.
Its polynomial formula supplies one original core, including the axis and
outer boundary, without multiplying an arbitrary smooth field by radius. -/
theorem actualNativeScalar_fromCovariantXi_originalCore
    (covariant : ACore parameters 3) (xi : ACore parameters 1)
    (covariantSame : ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters covariant).value (point,(axial : CellCircle))=
        actualCartesianCovariantFamilyField parameters length compact lengthPositive widthHalf widthLength state small
          source flat fields member sameSources allGrades (point.val,axial))
    (xiSame : ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters xi).value (point,(axial : CellCircle))=
        actualCartesianXiFamilyField parameters length compact lengthPositive widthHalf widthLength state small
          source flat fields member sameSources allGrades (point.val,axial)) :
    ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters (recoveredScalarOriginalCore parameters covariant xi)).value (point,(axial : CellCircle))=
        actualNativeScalarField parameters length compact lengthPositive widthHalf widthLength state small
          source flat fields member sameSources allGrades (point.val,axial) := by
  have polar (radius : ℝ) (positive : 0<radius) (bounded : radius≤1) (angle axial : ℝ) :
      coreValue (recoveredScalarOriginalCore parameters covariant xi) (polarClosedPoint radius angle positive.le bounded) axial=
        actualNativeScalarField parameters length compact lengthPositive widthHalf widthLength state small
          source flat fields member sameSources allGrades (polarPlane (radius,angle),axial) := by
    let radialPoint : Icc (radius/2) (1:ℝ) := ⟨radius,⟨by linarith,bounded⟩⟩
    have radiusPositive : 0<radius/2 := by positivity
    have radiusBounded : radius/2<1 := by linarith
    have representation := recoveredScalarOriginalCore_polar parameters covariant xi (radius/2) radiusPositive radiusBounded radialPoint (angle,axial)
    change coreValue (recoveredScalarOriginalCore parameters covariant xi) (polarClosedPoint radius angle positive.le bounded) axial=
      coreValue xi (polarClosedPoint radius angle positive.le bounded) axial+
        removePolarMean (fun query => scalarTangentialPolynomial (polarPlane (radius,query.1))
          (coreValue covariant (polarClosedPoint radius query.1 positive.le bounded) query.2)) (angle,axial) at representation
    rw [representation,actualNativeScalarField_cartesianPolynomial parameters length compact lengthPositive widthHalf widthLength state small
      source flat fields member sameSources allGrades compatible radius positive bounded angle axial]
    have normPositive (angle : ℝ) : 0<‖(polarClosedPoint radius angle positive.le bounded).val‖ := by
      change 0<‖polarPlane (radius,angle)‖
      rw [polarPlane_norm,abs_of_pos positive]
      exact positive
    rw [coreValue_originalPhysical,xiSame _ (normPositive angle)]
    congr 1
    congr 1
    funext query
    rw [coreValue_originalPhysical,covariantSame _ (normPositive query.1)]
    rfl
  intro point positive axial
  have actual := polar ‖point.val‖ positive point.property (Complex.arg (signedComplexCoordinate 1 point.val)) axial
  have samePoint : polarClosedPoint ‖point.val‖ (Complex.arg (signedComplexCoordinate 1 point.val)) positive.le point.property=point :=
    Subtype.ext (originalPolarPlane_norm_argument point.val)
  rw [samePoint,originalPolarPlane_norm_argument,coreValue_originalPhysical] at actual
  exact actual

end Grad.ActualScaledNativeCoefficients
