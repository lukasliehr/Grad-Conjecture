import AKAM2ActualSignedDeterminantFlux

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

/-- The original polar covariant of the SAME native compatible source solution. -/
def cartesianSourcePolarCurves (index : ℕ) : SmoothLowPhysicalRow parameters (originalExhaustionRadius length index)
    (originalExhaustionRadius_positive length lengthPositive index)
    (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index) :=
  actualObservedPolarCurves parameters length compact (originalExhaustionRadius length index)
    (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index)
    lengthPositive widthHalf widthLength state
    (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    source flat (fields index) (member index) (sameSources index) (allGrades index)

/-- The original uncorrected Xi/r coordinate from the SAME seven-field packet. -/
def cartesianSourceXiOverRadiusCurves (index : ℕ) : SmoothLowPhysicalRow parameters (originalExhaustionRadius length index)
    (originalExhaustionRadius_positive length lengthPositive index)
    (cartesianOriginalScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index) :=
  actualObservedXiOverRadiusCurves parameters length compact (originalExhaustionRadius length index)
    (originalExhaustionRadius_positive length lengthPositive index) (originalExhaustionRadius_half length lengthPositive index)
    lengthPositive widthHalf widthLength state
    (originalExhaustionPrimitiveRadius_inverse parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    source flat (fields index) (member index) (sameSources index) (allGrades index)

include compatible in
 theorem cartesianSourcePolarAndXi_compatible (first second : ℕ) (ordered : first ≤ second) :
    originalBulkRestriction 3 (originalExhaustionRadius length second) (originalExhaustionRadius length first)
      (originalExhaustionRadius_antitone length lengthPositive ordered)
      (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields second) =
      cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields first ∧
    originalBulkRestriction 1 (originalExhaustionRadius length second) (originalExhaustionRadius length first)
      (originalExhaustionRadius_antitone length lengthPositive ordered)
      (cartesianOriginalScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields second) =
      cartesianOriginalScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields first := by
  have sourceCompatible := fun first second included =>
    (cartesianExhaustionDatum_restrict parameters length compact lengthPositive widthHalf widthLength state small source flat first second 0 included).symm
  constructor
  · exact (originalCovariantFamilies_compatible parameters length compact (originalExhaustionRadius length)
      (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_half length lengthPositive) lengthPositive state
      (fun index => cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0) fields
      (originalExhaustionRadius_antitone length lengthPositive) sourceCompatible compatible first second ordered).1
  · exact originalScalarOverRadiusFamily_compatible parameters length (originalExhaustionRadius length)
      (originalExhaustionRadius_positive length lengthPositive) (originalExhaustionRadius_half length lengthPositive) lengthPositive
      (fun index => cartesianExhaustionDatum parameters length compact lengthPositive widthHalf widthLength state small source flat index 0) fields
      (originalExhaustionRadius_antitone length lengthPositive) sourceCompatible compatible first second ordered

include Mnonnegative stateBound vanishing nativeBound in
 theorem cartesianSourcePolar_uniformBound (index : ℕ) :
    ‖cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index‖ ≤
      cartesianPhysicalBulkConstant parameters length compact M * ‖quotientEta parameters 8 source‖ :=
  (le_add_of_nonneg_right (norm_nonneg _)).trans
    (cartesianOriginalCovariants_bound parameters length compact lengthPositive widthHalf widthLength state small
      M Mnonnegative stateBound source flat vanishing index (fields index) (nativeBound index))

/-- The actual determinant vector B w for the original solved source family. -/
def actualCartesianCofactorFluxCell (cell : ℤ) : SpatialPlane → ComplexEuclidean 3 :=
  cofactorFluxCell parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length)
    (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields)
    (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) cell

def actualCartesianDeterminantFluxComponent (cell : ℤ) (component : Fin 3) (point : SpatialPlane) : ℂ :=
  determinantFluxProjection length component
    (actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point)

/-- The same Cartesian covariant w=Q a_c, before the inverse transpose. -/
def actualCartesianCovariantCell (cell : ℤ) : SpatialPlane → ComplexEuclidean 3 :=
  gluedCartesianCellField parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length)
    (fun index => cartesianCovariantRow (originalExhaustionRadius length index)
      (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index))
    (fun index => (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).cartesianCovariant) cell

def actualCartesianXiOverRadiusCell (cell : ℤ) : SpatialPlane → ComplexEuclidean 1 :=
  gluedCartesianCellField parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length)
    (cartesianOriginalScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields)
    (cartesianSourceXiOverRadiusCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) cell

def actualCartesianXiCell (cell : ℤ) (point : SpatialPlane) : ComplexEuclidean 1 :=
  ‖point‖ • actualCartesianXiOverRadiusCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point

include Mnonnegative stateBound vanishing nativeBound compatible in
 theorem actualCartesianCofactorFluxCell_integrable_pair (cell : ℤ) :
    IntegrableOn (actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖actualCartesianCofactorFluxCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point‖) openUnitDisk :=
  cofactorFluxCell_integrable_pair parameters length state.val.val.rho state.val.val.epsilon state.val.val.field
    (originalExhaustionPrimitiveRadius_source parameters length compact state.val.val.rho state.val.val.epsilon state.val.val.field small)
    (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive)
    (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields)
    (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades)
    (fun first second ordered => (cartesianSourcePolarAndXi_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).1)
    _ (cartesianSourcePolar_uniformBound parameters length compact lengthPositive widthHalf widthLength state small source flat fields M Mnonnegative stateBound vanishing nativeBound) cell

include Mnonnegative stateBound vanishing nativeBound compatible in
 theorem actualCartesianDeterminantFluxComponent_integrable_pair (cell : ℤ) (component : Fin 3) :
    IntegrableOn (actualCartesianDeterminantFluxComponent parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell component) openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖actualCartesianDeterminantFluxComponent parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell component point‖) openUnitDisk := by
  have given := actualCartesianCofactorFluxCell_integrable_pair parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades M Mnonnegative stateBound vanishing nativeBound compatible cell
  exact Grad.PhysicalAxisEquation.boundedPhysicalFlux_integrable_pair openUnitDisk _ given.1 given.2
    (fun _ => determinantFluxProjection length component) aestronglyMeasurable_const
    ‖determinantFluxProjection length component‖ (Eventually.of_forall (fun _ => le_rfl))

include Mnonnegative stateBound vanishing nativeBound compatible in
 theorem actualCartesianCovariantCell_integrable_pair (cell : ℤ) :
    IntegrableOn (actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖actualCartesianCovariantCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point‖) openUnitDisk := by
  apply sameOriginalPhysicalCell_integrable_pair parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive)
    (fun index => cartesianCovariantRow (originalExhaustionRadius length index)
      (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields index))
    (fun index => (cartesianSourcePolarCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).cartesianCovariant)
    (cartesianCovariantRows_compatible (originalExhaustionRadius length) (originalExhaustionRadius_antitone length lengthPositive)
      (cartesianPolarCovariantFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields)
      (fun first second ordered => (cartesianSourcePolarAndXi_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).1))
    (5 * (cartesianPhysicalBulkConstant parameters length compact M * ‖quotientEta parameters 8 source‖))
  intro index
  exact (cartesianCovariantRow_bound _ _).trans (mul_le_mul_of_nonneg_left
    (cartesianSourcePolar_uniformBound parameters length compact lengthPositive widthHalf widthLength state small source flat fields M Mnonnegative stateBound vanishing nativeBound index) (by norm_num))

include stateBound vanishing nativeBound compatible in
 theorem actualCartesianXiOverRadiusCell_integrable_pair (cell : ℤ) :
    IntegrableOn (actualCartesianXiOverRadiusCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖actualCartesianXiOverRadiusCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point‖) openUnitDisk := by
  apply sameOriginalPhysicalCell_integrable_pair parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive)
    (cartesianOriginalScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields)
    (cartesianSourceXiOverRadiusCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades)
    (fun first second ordered => (cartesianSourcePolarAndXi_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).2)
    (cartesianScalarBulkConstant parameters length compact M * ‖quotientEta parameters 8 source‖)
  intro index
  exact cartesianOriginalScalarOverRadius_bound parameters length compact lengthPositive widthHalf widthLength state small
    M stateBound source flat vanishing index (fields index) (nativeBound index)

include stateBound vanishing nativeBound compatible in
 theorem actualCartesianXiCell_integrable_pair (cell : ℤ) :
    IntegrableOn (actualCartesianXiCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) openUnitDisk ∧
      IntegrableOn (fun point => ‖point‖⁻¹ * ‖actualCartesianXiCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell point‖) openUnitDisk := by
  have given := actualCartesianXiOverRadiusCell_integrable_pair parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades M stateBound vanishing nativeBound compatible cell
  exact radialMultiply_integrable_pair _ given.1 given.2

end Grad.ActualSmoothPhysicalField
