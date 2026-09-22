import AKDS15ActualResidualReferenceNorm

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4000
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


open Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.ActualCartesianDescent Grad.BoundaryTrace Grad.SourceBoundaryTrace
open Grad.FinitePhysicalJetLift Grad.OriginalKernelRetainedDecay Grad.OriginalKernelCovariantRecovery
open Grad.PhysicalCoordinates Grad.SourceCollar Grad.Constraints Grad.Cor18 Grad.NonlinearRange
open Grad.ActualCartesianFlux

open Grad.NonlinearQuotientBounds Grad.RealFixedRanges Grad.Q24Realization Grad.OriginalCurrentInverseUniqueness

variable (parameters : PhaseParameters) (compact : ℝ)
    (lengthPositive : 0<parameters.length) (widthHalf : parameters.gamma≤1/2)
    (widthLength : parameters.gamma≤Real.sqrt 5/(6*parameters.length))
    (reference : Seed.Parameters) (insideR : reference∈Seed.parameterDomain)
    (seed : Seed.Parameters) (insideS : seed∈Seed.parameterDomain)
    (base : RealJointCore parameters reference insideR)
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val))
    (small : physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
      (seed 0) base.1 8≤actualJetExhaustionRadius parameters parameters.length compact)
    (compactNonnegative : 0≤compact) (alphaSmall : |seed 1|≤compact)
    (deltaSmall : |seed 2|≤compact) (parameterSmall : |seed 3|≤compact)
    (source : OriginalFlatSource parameters parameters.length)

local notation "currentLow" => actualJetExhaustion_cubicSmall parameters parameters.length compact reference insideR seed insideS base small
local notation "nativeState" => actualJetExhaustionState parameters parameters.length compact reference insideR seed insideS base small
  compactNonnegative alphaSmall deltaSmall parameterSmall
local notation "nativeSmall" => actualNativeState_small parameters compact reference insideR seed insideS base small
  compactNonnegative alphaSmall deltaSmall parameterSmall
local notation "residual" => actualFiniteSourceResidual parameters parameters.length (seed 0) reference insideR seed insideS base currentLow source
local notation "residualFlat" => actualFiniteSourceResidual_isFlat parameters parameters.length (seed 0) lengthPositive reference insideR seed insideS base currentLow axis source


variable (seedPatch : Set Seed.Parameters) (compactPatch : IsCompact seedPatch)
    (insidePatch : seedPatch ⊆ Seed.parameterDomain) (seedIn : seed ∈ seedPatch)
open Grad.NonlinearProduct
include seedIn

/-- The literal finite-jet lift and SAME native residual correction now
solve the original flat source with their actual reference norm payments. -/
theorem actualNativeFlatSource_reference_norm
    (family : NativeCartesianFamily parameters parameters.length compact lengthPositive widthHalf widthLength nativeState nativeSmall residual residualFlat)
    (constants : ℕ→ℝ) (estimate : ∀ index grade, ‖family.graded index grade‖≤constants grade)
    (vector : ACore parameters 3)
    (sameVector : ∀ (point : ClosedDisk), 0<‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters vector).value (point,(axial : CellCircle))=
        actualCartesianVectorField parameters parameters.length compact lengthPositive widthHalf widthLength nativeState nativeSmall residual residualFlat
          family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
          (fun index grade => Exists.intro (family.graded index grade) (family.inserted index grade)) (point.val,axial))
    (scalar : ACore parameters 1)
    (sameScalar : ∀ (point : ClosedDisk), 0<‖point.val‖ → ∀ axial : ℝ,
      (originalPhysicalClosedJet parameters scalar).value (point,(axial : CellCircle))=
        actualNativeScalarField parameters parameters.length compact lengthPositive widthHalf widthLength nativeState nativeSmall residual residualFlat
          family.limit (fun index => (family.equations index).1) (fun index => (family.equations index).2.1)
          (fun index grade => Exists.intro (family.graded index grade) (family.inserted index grade)) (point.val,axial))
 :
    ∃ reconstructed : stateSmoothRange parameters reference insideR,
      literalPhysicalSmoothForward parameters parameters.length reference insideR seed insideS base axis reconstructed=source.val ∧
      ∀ grade, ‖Grad.SmoothingFamily.stateToGrade parameters grade reconstructed.val‖ ≤
        ((Grad.FinitePhysicalJetLift.originalRealFiniteLift_reference_bound_on_patch parameters parameters.length grade
            reference insideR seedPatch compactPatch insidePatch).choose+
          (actualReferencePair_bound_on_patch parameters grade reference insideR seedPatch compactPatch insidePatch).choose) *
        (‖quotientEta parameters (grade+6) source.val.val‖+
          physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
            (seed 0) base.1 (grade+6)*‖quotientEta parameters 6 source.val.val‖+
          originalGradeNorm grade vector+originalGradeNorm grade scalar) := by
  obtain ⟨correction,correctionLaw,correctionBound⟩ := actualNativeResidual_referenceSolution_quantitative parameters
    compact lengthPositive widthHalf widthLength reference insideR seed insideS base axis small compactNonnegative
    alphaSmall deltaSmall parameterSmall source seedPatch compactPatch insidePatch seedIn family constants estimate
    vector sameVector scalar sameScalar
  let lift := actualFiniteReferenceLift parameters parameters.length (seed 0) lengthPositive reference insideR seed insideS
    base currentLow source
  have solved := actualFiniteJet_sameResidual_uniqueSolution parameters compact lengthPositive widthHalf widthLength
    reference insideR seed insideS base axis small compactNonnegative alphaSmall deltaSmall parameterSmall source correction correctionLaw
  refine ⟨lift+correction,solved.1,?_⟩
  intro grade
  have liftBound := (originalRealFiniteLift_reference_bound_on_patch parameters parameters.length grade reference insideR
    seedPatch compactPatch insidePatch).choose_spec.2 seed seedIn insideS (seed 0) base.1
    (actualFiniteCurrentField parameters reference insideR seed insideS base)
    (actualFiniteCurrentField_axis_zero parameters reference insideR seed insideS base) currentLow source.val.val
    ((source_isFlat_iff_kernel parameters.length lengthPositive source.val).mpr source.property)
  change ‖Grad.SmoothingFamily.stateToGrade parameters grade lift.val‖ ≤ _ at liftBound
  let liftPayment := ‖quotientEta parameters (grade+6) source.val.val‖+
    physicalBudget parameters (actualFiniteCurrentField parameters reference insideR seed insideS base)
      (seed 0) base.1 (grade+6)*‖quotientEta parameters 6 source.val.val‖
  let pairPayment := originalGradeNorm grade vector+originalGradeNorm grade scalar
  have liftNonnegative : 0≤liftPayment := add_nonneg (norm_nonneg _)
    (mul_nonneg (physicalBudget_nonnegative _ _ _ _ _) (norm_nonneg _))
  have pairNonnegative : 0≤pairPayment := add_nonneg (originalGradeNorm_nonnegative grade vector)
    (originalGradeNorm_nonnegative grade scalar)
  have first := liftBound.trans (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_right pairNonnegative : liftPayment≤liftPayment+pairPayment)
    (originalRealFiniteLift_reference_bound_on_patch parameters parameters.length grade reference insideR
      seedPatch compactPatch insidePatch).choose_spec.1)
  have second := (correctionBound grade).trans (mul_le_mul_of_nonneg_left
    (le_add_of_nonneg_left liftNonnegative : pairPayment≤liftPayment+pairPayment)
    (actualReferencePair_bound_on_patch parameters grade reference insideR seedPatch compactPatch insidePatch).choose_spec.1)
  change ‖Grad.SmoothingFamily.stateToGrade parameters grade (lift.val+correction.val)‖ ≤ _
  rw [map_add]
  exact (norm_add_le _ _).trans ((add_le_add first second).trans_eq
    (by dsimp only [liftPayment,pairPayment]; ring))

end Grad.OriginalCoreRealization
