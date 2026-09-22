import AKAM4ActualSourceNormalizedFluxes

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
open Grad.ActualCartesianFlux

/-- The exact coefficients of R=(Jy).grad, in the original Cartesian coordinates. -/
def angularRotationCoordinate (direction : Fin 2) : SpatialPlane →L[ℝ] ℝ :=
  if direction=0 then -(PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 1)
  else PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) 0

def angularTransportFlux {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : SpatialPlane → E) (direction : Fin 2) (point : SpatialPlane) : E :=
  angularRotationCoordinate direction point • field point

 theorem angularTransportFlux_integrable_pair {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : SpatialPlane → E) (integrable : IntegrableOn field openUnitDisk)
    (weighted : IntegrableOn (fun point => ‖point‖⁻¹ * ‖field point‖) openUnitDisk) (direction : Fin 2) :
    IntegrableOn (angularTransportFlux field direction) openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖angularTransportFlux field direction point‖) openUnitDisk := by
  have coordinateBound (point : SpatialPlane) : ‖angularRotationCoordinate direction point‖ ≤ ‖point‖ := by
    by_cases same : direction=0
    · simpa [angularRotationCoordinate,same] using PiLp.norm_apply_le point (1 : Fin 2)
    · simpa [angularRotationCoordinate,same] using PiLp.norm_apply_le point (0 : Fin 2)
  have measurable := (angularRotationCoordinate direction).continuous.aestronglyMeasurable.smul integrable.aestronglyMeasurable
  have bound : ∀ᵐ point ∂volume.restrict openUnitDisk, ‖angularTransportFlux field direction point‖ ≤ ‖field point‖ := by
    filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point inside
    exact (norm_smul _ _).le.trans ((mul_le_mul_of_nonneg_right (coordinateBound point) (norm_nonneg _)).trans
      (mul_le_of_le_one_left (norm_nonneg _) inside.le))
  constructor
  · exact integrable.norm.mono' measurable bound
  · apply weighted.mono' (measurable_id.norm.inv.aestronglyMeasurable.mul measurable.norm)
    filter_upwards [bound] with point bound
    change ‖‖point‖⁻¹ * ‖angularTransportFlux field direction point‖‖ ≤ ‖point‖⁻¹ * ‖field point‖
    rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (norm_nonneg _))]
    exact mul_le_mul_of_nonneg_left bound (inv_nonneg.mpr (norm_nonneg _))

include Mnonnegative stateBound vanishing nativeBound compatible in
 theorem actualCartesianAngularFlux_integrable_pair (cell : ℤ) (direction : Fin 2) :
    IntegrableOn (angularTransportFlux (actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) direction) openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖angularTransportFlux (actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) direction point‖) openUnitDisk := by
  have given := actualCartesianCovariantCell_integrable_pair parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades M Mnonnegative stateBound vanishing nativeBound compatible cell
  exact angularTransportFlux_integrable_pair _ given.1 given.2 direction

include compatible in
/-- The actual global determinant vector is exactly the original signed B times Q a_c before axial projection. -/
 theorem actualCartesianCofactorFluxCell_actual (cell : ℤ) (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc (originalExhaustionRadius length index) 1) (polar : ℝ) :
    actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell
      (spatialPlaneOfPair (polarCoord.symm (radius,polar))) =
      angularCoefficient (fun axial => WithLp.toLp 2
        ((Grad.SourceCollar.originalPhysicalSignedCofactor parameters length state.val.val.epsilon state.val.val.field axial
          (polarClosedPoint radius polar ((originalExhaustionRadius_positive length lengthPositive index).le.trans inside.1) inside.2)).mulVec
          (cartesianCovariantValue polar
            ((cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).fullField
              ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (radius,polar,axial))))) cell :=
  cofactorFluxCell_actual parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive)
    (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields)
    (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades)
    (fun first second ordered => (cartesianSourcePolarAndXi_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).1)
    cell index radius inside polar

/-- The determinant flux uses the same U that AKAE reconstructs: F^T U=Q a_c. -/
 theorem cartesianSource_originalFrameRecovery (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc (originalExhaustionRadius length index) 1) (polar axial : ℝ) :
    WithLp.toLp 2 ((Grad.SourceCollar.originalPhysicalFrameMatrix parameters length state.val.val.epsilon state.val.val.field axial
      (polarClosedPoint radius polar ((originalExhaustionRadius_positive length lengthPositive index).le.trans inside.1) inside.2)).transpose.mulVec
        ((cartesianCorrectedVectorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).fullField
          ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (radius,polar,axial))) =
      cartesianCovariantValue polar
        ((cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).fullField
          ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) (radius,polar,axial)) :=
  (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).fullField_originalFrameRecovery
    parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    (originalExhaustionRadius length index) (originalExhaustionRadius_positive length lengthPositive index)
    ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) radius inside (polar,axial)

end Grad.ActualSmoothPhysicalField
