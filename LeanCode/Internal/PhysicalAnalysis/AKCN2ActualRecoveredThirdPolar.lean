import AKCN1OriginalThirdForceValue
import AKCJ9SameCoreCartesianFields
import AKBE7ActualObservedCartesianEquations

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
open Grad.ActualCartesianWeakEquations Grad.ActualScalarWeakEquations
open Grad.OriginalKernelCovariantRecovery Grad.AxisSplit Grad.FinitePhysicalJetLift

variable (core : ACore parameters 3)
    (same : ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters core).value (point,(axial : CellCircle)) =
        actualCartesianVectorField parameters length compact lengthPositive widthHalf widthLength state small
          source flat fields member sameSources allGrades (point.val,axial))

variable (scalar : ACore parameters 1)
    (sameScalar : ∀ (point : ClosedDisk), 0 < ‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters scalar).value (point,(axial : CellCircle)) =
        actualNativeScalarField parameters length compact lengthPositive widthHalf widthLength state small
          source flat fields member sameSources allGrades (point.val,axial))

open Grad.Constraints Grad.NonlinearQuotientBounds Grad.ActualCartesianEquations
open Grad.ActualForceMatrixFidelity Grad.ActualPolarEquations Grad.PhysicalFamily
open Grad.AnnularGeneralSourceRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularPhysicalFourier Grad.AnnularClosedJointRegularity
variable (physicalState : QuotientState parameters)
    (sameBase : physicalState.2.1=planarReferenceCore parameters+state.val.val.field)
    (sameEpsilon : physicalState.1=(state.val.val.epsilon : ℂ))

include same sameScalar sameBase sameEpsilon in
/-- The literal original fourth derivative row equals the SAME actual source
on every strict collar. All derivatives and frame products are genuine. -/
theorem actualRecoveredScalar_third_polar (index : ℕ) (radius : ℝ)
    (inside : radius∈Ioo (originalExhaustionRadius length index) 1) (angles : ℝ×ℝ) :
    coreValue (quotientRowsDerivative parameters length 1 physicalState ![(0,core,scalar)] 3)
      (Grad.SourceCollarDivision.polarClosedPoint radius angles.1
        ((originalExhaustionRadius_positive length lengthPositive index).le.trans inside.1.le) inside.2.le) angles.2 0=
      corePolarValue parameters (source 3) radius
        ((originalExhaustionRadius_positive length lengthPositive index).le.trans inside.1.le) inside.2.le angles 0 := by
  let lower := originalExhaustionRadius length index
  let positive := originalExhaustionRadius_positive length lengthPositive index
  let bounded := (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num : (1:ℝ)/2<1)
  let coefficientSmall := originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small
  let inverseSmall := originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small
  let seven := actualCartesianSevenCurves parameters length compact lower positive
    (originalExhaustionRadius_half length lengthPositive index) lengthPositive widthHalf widthLength state inverseSmall
    coefficientSmall source flat (fields index) (member index) (sameSources index) (allGrades index)
  let a := seven.covariant parameters length compact lower positive bounded state.val
  let covCore := originalCovariantCore parameters length state.val.val.epsilon state.val.val.field core false
  let xiCore := Grad.OriginalKernelRetainedDecay.originalKernelXi (planarReferenceCore parameters+state.val.val.field) core scalar
  let xiField := cartesianPhysicalField (originalPhysicalComponentField parameters lower length positive bounded lengthPositive
    (originalWeightedRetainedObservation parameters lower length positive
      ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index)) 1)
  have sameCov : ∀ (r : ℝ) (included : r∈Icc lower 1) (query : ℝ×ℝ),
      coreValue covCore (Grad.SourceCollarDivision.polarClosedPoint r query.1 (positive.le.trans included.1) included.2) query.2=
        a.cartesianCovariant.fullField bounded (r,query) := by
    intro r included query
    exact nativeCovariant_sameOriginalCore parameters length state.val.val.rho state.val.val.epsilon lengthPositive.ne'
      state.val.val.field coefficientSmall lower positive bounded a core r included query
      (actualRecoveredVector_polar parameters length compact lengthPositive widthHalf widthLength state small source flat
        fields member sameSources allGrades compatible core same index r included query.1 query.2).symm
  have sameXi : ∀ (r : ℝ) (included : r∈Icc lower 1) (query : ℝ×ℝ),
      coreValue xiCore (Grad.SourceCollarDivision.polarClosedPoint r query.1 (positive.le.trans included.1) included.2) query.2=
        xiField (polarPlane (r,query.1),query.2) := by
    intro r included query
    have normInside : ‖polarPlane (r,query.1)‖∈Icc lower 1 := by
      simpa only [polarPlane_norm,abs_of_pos (positive.trans_le included.1)] using included
    exact (actualRecoveredXi_polar parameters length compact lengthPositive widthHalf widthLength state small source flat
      fields member sameSources allGrades compatible core same scalar sameScalar index r included query).trans
      (actualCartesianXiFamilyField_same parameters length compact lengthPositive widthHalf widthLength state small source flat
        fields member sameSources allGrades compatible index (polarPlane (r,query.1)) normInside query.2)
  have normInside : ‖polarPlane (radius,angles.1)‖∈Ioo lower 1 := by
    simpa only [polarPlane_norm,abs_of_pos (positive.trans inside.1)] using inside
  have covDerivative := originalCore_same_nativeDerivative parameters lower positive bounded a.cartesianCovariant covCore sameCov
    (polarPlane (radius,angles.1),angles.2) normInside
  have xiDerivative := originalCore_fderiv_of_polar parameters xiCore lower positive xiField sameXi
    (polarPlane (radius,angles.1),angles.2) normInside
  have force (query : ℝ×ℝ) :
      (-2 : ℂ)*coreValue (originalCovariantCore parameters length state.val.val.epsilon state.val.val.field core true)
        (Grad.SourceCollarDivision.polarClosedPoint radius query.1 (positive.le.trans inside.1.le) inside.2.le) query.2 2=
      matrixPairing ((-2 : ℂ) • physicalToroidalVector)
        (rotatedPhysicalFrameMatrix parameters 1 1 state.val.val.epsilon state.val.val.field query.2
          (Grad.SourceCollarDivision.polarClosedPoint radius query.1 (positive.le.trans inside.1.le) inside.2.le) *
          Matrix.diagonal ![1,1,(length : ℂ)⁻¹]).transpose
        ((a.physicalUFromPolar parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
          state.val.val.low lower positive bounded).fullField bounded (radius,query)) := by
    rw [originalThirdForce_value parameters length state.val.val.epsilon lengthPositive.ne' state.val.val.field core _ query.2 query.1,
      actualRecoveredVector_polar parameters length compact lengthPositive widthHalf widthLength state small source flat
        fields member sameSources allGrades compatible core same index radius ⟨inside.1.le,inside.2.le⟩ query.1 query.2]
    rfl
  have quarter : planeQuarterTurn (polarPlane (radius,angles.1))=radius • planeQuarterTurn (radialDirection angles.1) := by
    ext coordinate
    fin_cases coordinate <;> simp [polarPlane,collarPlane,radialDirection,planeQuarterTurn]
  have raw := originalThirdRow_cartesianValue parameters length state.val.val.epsilon lower lengthPositive.ne' positive bounded
    state.val.val.field core scalar physicalState sameBase sameEpsilon radius inside angles
  rw [sameBase] at raw
  change coreValue (quotientRowsDerivative parameters length 1 physicalState ![(0,core,scalar)] 3)
      (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 (positive.le.trans inside.1.le) inside.2.le) angles.2 0=
      (length : ℂ)*fderiv ℝ (originalCoreProductLift parameters covCore) (polarPlane (radius,angles.1),angles.2)
        (planeQuarterTurn (polarPlane (radius,angles.1)),0) 2-
      fderiv ℝ (originalCoreProductLift parameters xiCore) (polarPlane (radius,angles.1),angles.2) (0,1) 0+_ at raw
  rw [covDerivative,xiDerivative,quarter] at raw
  simp_rw [force] at raw
  exact raw.trans (actualObserved_originalForceAndThird parameters length compact lower positive
    (originalExhaustionRadius_half length lengthPositive index) lengthPositive widthHalf widthLength state inverseSmall coefficientSmall source flat
    (fields index) (member index) (sameSources index) (allGrades index) seven radius inside angles).2

end Grad.OriginalCoreRealization
