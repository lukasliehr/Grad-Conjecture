import AKAH3ActualCorrectedCartesianIntegrability

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 300000
open Set Filter MeasureTheory
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
variable (M : ℝ) (Mnonnegative : 0 ≤ M)
    (stateBound : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 14 ≤ M)
    (vanishing : SourceHigherVanishing source)
    (nativeBound : ∀ index, originalWeightedRetainedNorm parameters (originalExhaustionRadius length index) length
      (originalExhaustionRadius_positive length lengthPositive index)
      ((originalExhaustionRadius_half length lengthPositive index).trans (by norm_num)) lengthPositive (fields index).ofLp.1 ≤
        2 * independentCoupledDataConstant parameters length compact *
          (originalSourceAllocationConstant parameters length 0 * (1 + M) * ‖quotientEta parameters 8 source‖))

variable (compatible : ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)

open Grad.ActualCartesianIntegrability


/-- Multiplication by the actual radial distance loses no disk integrability. -/
theorem radialMultiply_integrable_pair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : SpatialPlane → E) (integrable : IntegrableOn field openUnitDisk)
    (weighted : IntegrableOn (fun point => ‖point‖⁻¹ * ‖field point‖) openUnitDisk) :
    IntegrableOn (fun point => ‖point‖ • field point) openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖‖point‖ • field point‖) openUnitDisk := by
  have measurable := measurable_id.norm.aestronglyMeasurable.smul integrable.aestronglyMeasurable
  have bound : ∀ᵐ point ∂volume.restrict openUnitDisk, ‖‖point‖ • field point‖ ≤ ‖field point‖ := by
    filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point inside
    rw [norm_smul,Real.norm_of_nonneg (norm_nonneg _)]
    exact mul_le_of_le_one_left (norm_nonneg _) inside.le
  constructor
  · exact integrable.norm.mono' measurable bound
  · apply weighted.mono' (measurable_id.norm.inv.aestronglyMeasurable.mul measurable.norm)
    filter_upwards [bound] with point bound
    change ‖‖point‖⁻¹ * ‖‖point‖ • field point‖‖ ≤ ‖point‖⁻¹ * ‖field point‖
    rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr (norm_nonneg _))

/-- The genuine original scalar S, recovered from the already corrected S/r. -/
def actualCartesianScalarCell (cell : ℤ) (point : SpatialPlane) : ComplexEuclidean 1 :=
  ‖point‖ • actualCartesianScalarOverRadiusCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point

include Mnonnegative stateBound vanishing nativeBound compatible in
theorem actualCartesianScalarCell_integrable_pair (cell : ℤ) :
    IntegrableOn (actualCartesianScalarCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖actualCartesianScalarCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point‖) openUnitDisk := by
  have given := actualCartesianScalarOverRadiusCell_integrable_pair parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades
    M Mnonnegative stateBound vanishing nativeBound compatible cell
  exact radialMultiply_integrable_pair _ given.1 given.2

include Mnonnegative stateBound vanishing nativeBound compatible in
theorem actualCartesianJointCell_integrable_pair (cell : ℤ) :
    IntegrableOn (fun point => (actualCartesianVectorCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point,
      actualCartesianScalarCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point)) openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖(actualCartesianVectorCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point,
        actualCartesianScalarCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point)‖) openUnitDisk := by
  have first := actualCartesianVectorCell_integrable_pair parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades
    M Mnonnegative stateBound vanishing nativeBound compatible cell
  have second := actualCartesianScalarCell_integrable_pair parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades
    M Mnonnegative stateBound vanishing nativeBound compatible cell
  exact Grad.PhysicalAxisEquation.jointPhysicalPair_integrable _ _ _ first.1 second.1 first.2 second.2

end Grad.ActualSmoothPhysicalField
