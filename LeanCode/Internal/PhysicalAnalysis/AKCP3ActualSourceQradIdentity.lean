import AKCP1LiteralFullFrameForceValue

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.SourceCollarFullSource Grad.ActualSmoothPhysicalField
open Grad.ActualCartesianEquations Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.Constraints Grad.SourceCollar Grad.FinitePhysicalJetLift
open Grad.FlatSourceProjection Grad.QuotientProjection Grad.OriginalKernelCovariantRecovery

 theorem literalCartesianPlanarSource_pair (parameters : PhaseParameters) (source : SmoothQuotient parameters)
    (radius : ℝ) (nonnegative : 0≤radius) (bounded : radius≤1) (angles : ℝ×ℝ) :
    literalCartesianPlanarSource parameters source radius nonnegative bounded angles=
      originalPairCircle (cartesianSpinFirst source) (cartesianSpinSecond source) radius nonnegative bounded angles := by
  change WithLp.toLp 2 ![
    coreValue (cartesianSourceVector source) (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 nonnegative bounded) angles.2 0,
    coreValue (cartesianSourceVector source) (Grad.SourceCollarDivision.polarClosedPoint radius angles.1 nonnegative bounded) angles.2 1,0]=_
  simp only [cartesianSourceVector,vectorTuple,coreValue_add,coreValue_gaugeValueMap]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [originalPairCircle,componentInsertion]

/-- The actual flat source is fixed by the true radial Cartesian complement. -/
theorem literalCartesianPlanarSource_Qrad (parameters : PhaseParameters) (source : SmoothQuotient parameters)
    (flat : IsFlat source) (lower : ℝ) (positive : 0<lower) (bounded : lower<1)
    (radius : ℝ) (inside : radius∈Icc lower 1) (angles : ℝ×ℝ) :
    cartesianRadialMeanFree (literalCartesianPlanarSource parameters source radius (positive.le.trans inside.1) inside.2) angles=
      originalPairCircle (cartesianSpinFirst source) (cartesianSpinSecond source) radius (positive.le.trans inside.1) inside.2 angles := by
  have same := funext (literalCartesianPlanarSource_pair parameters source radius (positive.le.trans inside.1) inside.2)
  rw [same]
  apply originalPairCircle_Qrad parameters
    (cartesianSpinFirst source) (cartesianSpinSecond source) (cartesianSpinFirst source) (cartesianSpinSecond source)
    ?_ rfl lower positive bounded radius inside angles
  change sourceRadialContractionCore source-angularCore parameters 0 (sourceRadialContractionCore source)=_
  rw [sourceRadialContraction_mean_zero source flat,sub_zero]
  rfl

end Grad.OriginalCoreRealization
