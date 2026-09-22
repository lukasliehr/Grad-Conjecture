import AKAE8ActualCorrectedFamilyCurves

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
/-- The same corrected original Vector field on the whole punctured disk. -/
def actualCartesianVectorField : SpatialPlane × ℝ → ComplexEuclidean 3 :=
  gluedCartesianFamilyField parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (cartesianCorrectedVectorFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (cartesianCorrectedVectorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades)

def actualCartesianVectorCell (cell : ℤ) : SpatialPlane → ComplexEuclidean 3 :=
  gluedCartesianCellField parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (cartesianCorrectedVectorFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (cartesianCorrectedVectorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) cell

def actualCartesianVectorCurve : ℝ → CellL2 3 :=
  gluedPhysicalFamilyCurve parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (cartesianCorrectedVectorFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (cartesianCorrectedVectorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) 0

variable (compatible : ∀ first second (included : originalExhaustionRadius length first ≤ originalExhaustionRadius length second),
      originalFiveBlockRestriction parameters (originalExhaustionRadius length first) (originalExhaustionRadius length second) length
        (originalExhaustionRadius_positive length lengthPositive first) (originalExhaustionRadius_positive length lengthPositive second)
        ((originalExhaustionRadius_half length lengthPositive second).trans_lt (by norm_num)) lengthPositive included (fields first) = fields second)
include compatible in
theorem actualCartesianVectorField_same (index : ℕ) (point : SpatialPlane × ℝ)
    (inside : ‖point.1‖ ∈ Icc (originalExhaustionRadius length index) 1) :
    actualCartesianVectorField parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades point =
      (cartesianCorrectedVectorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).cartesianField
        ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) point :=
  gluedCartesianFamilyField_same parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive) (cartesianCorrectedVectorFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (cartesianCorrectedVectorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) (fun first second ordered => (cartesianCorrectedFamilies_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).1) index point inside

include compatible in
theorem actualCartesianVectorField_smoothAt (point : SpatialPlane × ℝ)
    (nonzero : point.1 ≠ 0) (inside : ‖point.1‖ < 1) :
    ContDiffAt ℝ ∞ (actualCartesianVectorField parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) point :=
  gluedCartesianFamilyField_smoothAt parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive) (cartesianCorrectedVectorFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (cartesianCorrectedVectorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) (fun first second ordered => (cartesianCorrectedFamilies_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).1) point nonzero inside

include compatible in
theorem actualCartesianVectorCell_smoothAt (cell : ℤ) (point : SpatialPlane)
    (nonzero : point ≠ 0) (inside : ‖point‖ < 1) :
    ContDiffAt ℝ ∞ (actualCartesianVectorCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) point :=
  gluedCartesianCellField_smoothAt parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive) (cartesianCorrectedVectorFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (cartesianCorrectedVectorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) (fun first second ordered => (cartesianCorrectedFamilies_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).1) cell point nonzero inside

include compatible in
theorem actualCartesianVectorCell_coefficient (cell : ℤ) (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc (originalExhaustionRadius length index) 1) (angular : ℤ) :
    angularCoefficient (fun polar => actualCartesianVectorCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell
      (spatialPlaneOfPair (polarCoord.symm (radius,polar)))) angular =
        actualCartesianVectorCurve parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades radius (angular,cell) :=
  gluedCartesianCellField_coefficient parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive) (cartesianCorrectedVectorFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (cartesianCorrectedVectorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) (fun first second ordered => (cartesianCorrectedFamilies_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).1) cell index radius inside angular

include compatible in
theorem actualCartesianVectorCurve_same (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc (originalExhaustionRadius length index) 1) :
    actualCartesianVectorCurve parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades radius = (cartesianCorrectedVectorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).physicalCurve 0 radius :=
  gluedPhysicalFamilyCurve_same parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive) (cartesianCorrectedVectorFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (cartesianCorrectedVectorCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) (fun first second ordered => (cartesianCorrectedFamilies_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).1) 0 index radius inside

/-- The same corrected original ScalarOverRadius field on the whole punctured disk. -/
def actualCartesianScalarOverRadiusField : SpatialPlane × ℝ → ComplexEuclidean 1 :=
  gluedCartesianFamilyField parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (cartesianCorrectedScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (cartesianCorrectedScalarOverRadiusCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades)

def actualCartesianScalarOverRadiusCell (cell : ℤ) : SpatialPlane → ComplexEuclidean 1 :=
  gluedCartesianCellField parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (cartesianCorrectedScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (cartesianCorrectedScalarOverRadiusCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) cell

def actualCartesianScalarOverRadiusCurve : ℝ → CellL2 1 :=
  gluedPhysicalFamilyCurve parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (cartesianCorrectedScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (cartesianCorrectedScalarOverRadiusCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) 0

include compatible in
theorem actualCartesianScalarOverRadiusField_same (index : ℕ) (point : SpatialPlane × ℝ)
    (inside : ‖point.1‖ ∈ Icc (originalExhaustionRadius length index) 1) :
    actualCartesianScalarOverRadiusField parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades point =
      (cartesianCorrectedScalarOverRadiusCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).cartesianField
        ((originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num)) point :=
  gluedCartesianFamilyField_same parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive) (cartesianCorrectedScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (cartesianCorrectedScalarOverRadiusCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) (fun first second ordered => (cartesianCorrectedFamilies_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).2) index point inside

include compatible in
theorem actualCartesianScalarOverRadiusField_smoothAt (point : SpatialPlane × ℝ)
    (nonzero : point.1 ≠ 0) (inside : ‖point.1‖ < 1) :
    ContDiffAt ℝ ∞ (actualCartesianScalarOverRadiusField parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) point :=
  gluedCartesianFamilyField_smoothAt parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive) (cartesianCorrectedScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (cartesianCorrectedScalarOverRadiusCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) (fun first second ordered => (cartesianCorrectedFamilies_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).2) point nonzero inside

include compatible in
theorem actualCartesianScalarOverRadiusCell_smoothAt (cell : ℤ) (point : SpatialPlane)
    (nonzero : point ≠ 0) (inside : ‖point‖ < 1) :
    ContDiffAt ℝ ∞ (actualCartesianScalarOverRadiusCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell) point :=
  gluedCartesianCellField_smoothAt parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive) (cartesianCorrectedScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (cartesianCorrectedScalarOverRadiusCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) (fun first second ordered => (cartesianCorrectedFamilies_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).2) cell point nonzero inside

include compatible in
theorem actualCartesianScalarOverRadiusCell_coefficient (cell : ℤ) (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc (originalExhaustionRadius length index) 1) (angular : ℤ) :
    angularCoefficient (fun polar => actualCartesianScalarOverRadiusCell parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades cell
      (spatialPlaneOfPair (polarCoord.symm (radius,polar)))) angular =
        actualCartesianScalarOverRadiusCurve parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades radius (angular,cell) :=
  gluedCartesianCellField_coefficient parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive) (cartesianCorrectedScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (cartesianCorrectedScalarOverRadiusCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) (fun first second ordered => (cartesianCorrectedFamilies_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).2) cell index radius inside angular

include compatible in
theorem actualCartesianScalarOverRadiusCurve_same (index : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc (originalExhaustionRadius length index) 1) :
    actualCartesianScalarOverRadiusCurve parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades radius = (cartesianCorrectedScalarOverRadiusCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades index).physicalCurve 0 radius :=
  gluedPhysicalFamilyCurve_same parameters (originalExhaustionRadius length) (originalExhaustionRadius_positive length lengthPositive)
    (fun index => (originalExhaustionRadius_half length lengthPositive index).trans_lt (by norm_num))
    (originalExhaustionRadius_tendsto length) (originalExhaustionRadius_antitone length lengthPositive) (cartesianCorrectedScalarOverRadiusFamily parameters length compact lengthPositive widthHalf widthLength state small source flat fields) (cartesianCorrectedScalarOverRadiusCurves parameters length compact lengthPositive widthHalf widthLength state small source flat fields member sameSources allGrades) (fun first second ordered => (cartesianCorrectedFamilies_compatible parameters length compact lengthPositive widthHalf widthLength state small source flat fields compatible first second ordered).2) 0 index radius inside

end Grad.ActualSmoothPhysicalField
