import AKCP4ActualRecoveredPlanarPolar
import AKCH7PuncturedInteriorCoreFaithfulness

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

include same sameScalar sameBase in
/-- The literal two original spin rows equal the SAME original flat source
as smooth cores on the full closed disk, including the axis and outer circle. -/
theorem actualRecoveredVector_planar :
    quotientRowsDerivative parameters length 1 physicalState ![(0,core,scalar)] 0=source 0 ∧
    quotientRowsDerivative parameters length 1 physicalState ![(0,core,scalar)] 1=source 1 := by
  let output := quotientRowsDerivative parameters length 1 physicalState ![(0,core,scalar)]
  have cartesian (direction : Fin 2) :
      ![cartesianSpinFirst output,cartesianSpinSecond output] direction=
        ![cartesianSpinFirst source,cartesianSpinSecond source] direction := by
    apply originalCore_eq_of_openPuncturedValues parameters
    intro point nonzero interior axial
    let index := selectedInnerCollar (originalExhaustionRadius length) (originalExhaustionRadius_tendsto length) ‖point.val‖ nonzero
    have inside : ‖point.val‖∈Ioo (originalExhaustionRadius length index) 1 :=
      ⟨selectedInnerCollar_lt (originalExhaustionRadius length) (originalExhaustionRadius_tendsto length) ‖point.val‖ nonzero,interior⟩
    obtain ⟨angle,polar⟩ := closedPoint_has_polar_angle point
    have equation := actualRecoveredPlanar_force_polar parameters length compact lengthPositive widthHalf widthLength state small
      source flat fields member sameSources allGrades compatible core same scalar sameScalar physicalState sameBase index ‖point.val‖ inside (angle,axial)
    have divisionPoint : Grad.SourceCollarDivision.polarClosedPoint ‖point.val‖ angle
        ((originalExhaustionRadius_positive length lengthPositive index).le.trans inside.1.le) inside.2.le=point := by
      rw [divisionPolarPoint_eq_original]
      exact polar
    have value := congrArg (fun value : ComplexEuclidean 3 => value (⟨direction.val,by omega⟩ : Fin 3)) equation
    simp only [originalPairCircle] at value
    change (WithLp.toLp 2 ![coreValue (cartesianSpinFirst output) _ axial 0,coreValue (cartesianSpinSecond output) _ axial 0,0])
        (⟨direction.val,by omega⟩ : Fin 3)=
      (WithLp.toLp 2 ![coreValue (cartesianSpinFirst source) _ axial 0,coreValue (cartesianSpinSecond source) _ axial 0,0])
        (⟨direction.val,by omega⟩ : Fin 3) at value
    rw [divisionPoint] at value
    apply PiLp.ext
    intro coordinate
    obtain rfl := Fin.eq_zero coordinate
    fin_cases direction <;> exact value
  have first : cartesianSpinFirst output=cartesianSpinFirst source := cartesian 0
  have second : cartesianSpinSecond output=cartesianSpinSecond source := cartesian 1
  constructor
  · change output 0=source 0
    rw [← cartesianSpin_reconstruct_zero output,← cartesianSpin_reconstruct_zero source,first,second]
  · change output 1=source 1
    rw [← cartesianSpin_reconstruct_one output,← cartesianSpin_reconstruct_one source,first,second]

end Grad.OriginalCoreRealization
