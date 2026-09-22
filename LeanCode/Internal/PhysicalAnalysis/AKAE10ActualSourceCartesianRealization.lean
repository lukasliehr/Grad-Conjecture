import AKAE9ActualGlobalCorrectedFields

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 300000
open Set Filter
open scoped Topology ContDiff
namespace Grad.ActualSmoothPhysicalField
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

open Grad.ActualCartesianDescent Grad.ClosedJets Grad.DiskExtension.Operator Grad.BoundaryTrace Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients

/-- The actual original Cartesian source supplies the same corrected global fields,
with no radial smoothness or compatible-family premise. -/
theorem actualCartesianSource_correctedCartesianRealization
    (parameters : PhaseParameters) (length compact : ℝ) (lengthPositive : 0 < length)
    (M : ℝ) (Mnonnegative : 0 ≤ M)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      originalExhaustionPrimitiveRadius parameters length compact)
    (stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ M)
    (source : SmoothQuotient parameters) (flat : IsFlat source) (vanishing : SourceHigherVanishing source) :
    ∃ (fields : ∀ index, OriginalFiveBlockAmbient parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index)),
    ∃ (member : ∀ index, fields index ∈ OriginalObservedEquationGraph parameters length compact
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
          ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index)) weighted),
      (∀ index, originalWeightedRetainedNorm parameters (originalExhaustionRadius length index) length
        (originalExhaustionRadius_positive length lengthPositive index)
        ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index).ofLp.1 ≤
          2 * independentCoupledDataConstant parameters length compact *
            (originalSourceAllocationConstant parameters length 0 * (1+M) * ‖quotientEta parameters 8 source‖)) ∧
      ( ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second) ∧
      (∀ point : SpatialPlane × ℝ, point.1 ≠ 0 → ‖point.1‖ < 1 →
        ContDiffAt ℝ ∞ (actualCartesianVectorField parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) point ∧
        ContDiffAt ℝ ∞ (actualCartesianScalarOverRadiusField parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) point) ∧
      (∀ cell : ℤ, ∀ point : SpatialPlane, point ≠ 0 → ‖point‖ < 1 →
        ContDiffAt ℝ ∞ (actualCartesianVectorCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) point ∧
        ContDiffAt ℝ ∞ (actualCartesianScalarOverRadiusCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) point) ∧
      (∀ cell index radius, radius ∈ Icc (originalExhaustionRadius length index) 1 → ∀ angular : ℤ,
        angularCoefficient (fun polar => actualCartesianVectorCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell
          (spatialPlaneOfPair (polarCoord.symm (radius,polar)))) angular =
            actualCartesianVectorCurve parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades radius (angular,cell) ∧
        angularCoefficient (fun polar => actualCartesianScalarOverRadiusCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell
          (spatialPlaneOfPair (polarCoord.symm (radius,polar)))) angular =
            actualCartesianScalarOverRadiusCurve parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades radius (angular,cell)) := by
  have certificate := actualCartesianSource_compatibleSolution parameters length compact lengthPositive M Mnonnegative
  obtain ⟨fields,graded,laws⟩ := certificate.choose_spec.2 widthHalf widthLength state small stateBound source flat vanishing
  let member := fun index => (laws.1 index).1
  let sameSources := fun index => (laws.1 index).2.1
  let allGrades := fun index grade => Exists.intro (graded index grade) (laws.2.2 index grade).1
  refine ⟨fields,member,sameSources,allGrades,(fun index => (laws.1 index).2.2.2),laws.2.1,?_,?_,?_⟩
  · intro point nonzero inside
    exact ⟨actualCartesianVectorField_smoothAt parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades laws.2.1 point nonzero inside,
      actualCartesianScalarOverRadiusField_smoothAt parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades laws.2.1 point nonzero inside⟩
  · intro cell point nonzero inside
    exact ⟨actualCartesianVectorCell_smoothAt parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades laws.2.1 cell point nonzero inside,
      actualCartesianScalarOverRadiusCell_smoothAt parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades laws.2.1 cell point nonzero inside⟩
  · intro cell index radius inside angular
    exact ⟨actualCartesianVectorCell_coefficient parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades laws.2.1 cell index radius inside angular,
      actualCartesianScalarOverRadiusCell_coefficient parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades laws.2.1 cell index radius inside angular⟩

end Grad.ActualSmoothPhysicalField
