import AJE44OriginalSharedInsertedGrade
import AJE46SmoothSourceCurveAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open scoped ContDiff
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.AnnularInverseCalculus
open Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularKernelL2 Grad.AnnularOrbitGenerators Grad.AnnularLowEnergy Grad.AnnularLowOrbit
attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule
  sourceRadialRealInner sourceGraphRealInner sourceKnownBulkRealInner sourceKnownBoundaryRealInner
  sourceKnownGraphRealInner sourceKnownGraphBoundaryRealInner sourceKnownAmbientRealInner
  sourceLowBoundaryRealInner sourceStrongAmbientRealInner


def finiteRadialSourceCurve (lower : ℝ) (field : DivisionRow 1 lower)
    (support : Finset (ℤ × ℤ)) (finite : ∀ mode, mode ∉ support → field mode = 0) (axis : Bool) :
    SourceSmoothCurve (DivisionRow 1 lower) :=
  finiteComplexSourceCurve (sourceAxisFrequency axis) field
    (fun time => orbitLpAction (RadialL2 1 lower) (time • axisVector axis) field)
    (fun time mode => by rw [orbitLpAction_apply,sourceOrbitCharacter_axis]) support finite

def finiteGraphSourceCurve (lower : ℝ) (field : lp (fun _ : ℤ × ℤ => WeightedRadialH1 1 lower) 2)
    (support : Finset (ℤ × ℤ)) (finite : ∀ mode, mode ∉ support → field mode = 0) (axis : Bool) :
    SourceSmoothCurve (lp (fun _ : ℤ × ℤ => WeightedRadialH1 1 lower) 2) :=
  ⟨fun time => sourceGraphTranslation 1 lower (time • axisVector axis) field,
    finiteSourceGraphOrbit_contDiff 1 lower field support finite axis⟩

def finiteOuterSourceCurve (parameters : PhaseParameters) (field : HighBoundaryPrimitive parameters 0 0)
    (support : Finset (ℤ × ℤ)) (finite : ∀ mode, mode ∉ support → field.val mode = 0) (axis : Bool) :
    SourceSmoothCurve (HighBoundaryPrimitive parameters 0 0) := by
  refine ⟨fun time => outerDatumTranslation parameters 0 0 (time • axisVector axis) field,?_⟩
  apply sourceComplexClosedGraph_contDiff (highAngularSubmodule parameters 0 0 1)
  exact finiteLpCharacterOrbit_contDiff (sourceAxisFrequency axis) field.val _
    (fun time mode => by rw [outerDatumTranslation_val,orbitLpAction_apply,sourceOrbitCharacter_axis]) support finite

def finiteHighIncomingCurve (field : AnnularBoundary)
    (support : Finset HighAnnularMode) (finite : ∀ mode, mode ∉ support → field mode = 0) (axis : Bool) :
    SourceSmoothCurve AnnularBoundary :=
  finiteComplexSourceCurve (fun mode : HighAnnularMode => sourceAxisFrequency axis mode.val) field
    (fun time => highIncomingTranslation (time • axisVector axis) field)
    (fun time mode => by rw [highIncomingTranslation_apply,sourceOrbitCharacter_axis]) support finite

def finiteLowIncomingCurve (field : LowEnergyBoundary)
    (support : Finset LowAnnularIndex) (finite : ∀ index, index ∉ support → field index = 0) (axis : Bool) :
    SourceSmoothCurve LowEnergyBoundary :=
  finiteComplexSourceCurve (fun index : LowAnnularIndex => sourceAxisFrequency axis index.2.val) field
    (fun time => lowBoundaryTranslation (time • axisVector axis) field)
    (fun time index => by rw [lowBoundaryTranslation_apply,sourceOrbitCharacter_axis]) support finite

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (data : StrongDataCarrier parameters lower positive bounded 0 0) (support : StrongCutSupport)
    (finite : StrongSupported parameters lower positive bounded support data) (axis : Bool)

def finiteStrongAmbientCurve : SourceSmoothCurve (StrongDataAmbient parameters lower 0 0) :=
  (((SourceSmoothCurve.finite 4 (fun slot =>
      finiteRadialSourceCurve lower (data.val.ofLp.1.ofLp.1.ofLp.1 slot) support.1 (finite.1 slot) axis)).pair
    (SourceSmoothCurve.finite 3 (fun slot =>
      finiteRadialSourceCurve lower (data.val.ofLp.1.ofLp.1.ofLp.2 slot) support.1 (finite.2.1 slot) axis))).pair
    (((finiteGraphSourceCurve lower data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.1 support.1 finite.2.2.1 axis).pair
      (finiteGraphSourceCurve lower data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2 support.1 finite.2.2.2.1 axis)).pair
      ((finiteOuterSourceCurve parameters data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.1 support.1 finite.2.2.2.2.1 axis).pair
        (finiteHighIncomingCurve data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.2 support.2.1 finite.2.2.2.2.2.1 axis)))).pair
    (finiteLowIncomingCurve data.val.ofLp.2 support.2.2 finite.2.2.2.2.2.2 axis)

theorem finiteStrongAmbientCurve_exact (time : ℝ) :
    (finiteStrongAmbientCurve parameters lower positive bounded data support finite axis).curve time =
      strongDataAmbientTranslation parameters lower 0 0 (time • axisVector axis) data.val := rfl

/- Finite Fourier data have genuine smooth orbits in the original full
closed shared Hilbert carrier, including the source radial graph norm. -/
include support finite in
theorem finiteStrongDataOrbit_contDiff :
    ContDiff ℝ ∞ (fun time : ℝ => strongDataTranslation parameters lower positive bounded 0 0 (time • axisVector axis) data) := by
  have smooth := (finiteStrongAmbientCurve parameters lower positive bounded data support finite axis).smooth
  have same : (finiteStrongAmbientCurve parameters lower positive bounded data support finite axis).curve =
      fun time => strongDataAmbientTranslation parameters lower 0 0 (time • axisVector axis) data.val :=
    funext (finiteStrongAmbientCurve_exact parameters lower positive bounded data support finite axis)
  rw [same] at smooth
  let : CompleteSpace (StrongDataCarrier parameters lower positive bounded 0 0) :=
    strongDataCarrierComplete parameters lower positive bounded 0 0
  let : (StrongDataCarrier parameters lower positive bounded 0 0).HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace _
  exact sourceClosedGraph_contDiff (StrongDataCarrier parameters lower positive bounded 0 0) _ smooth

end Grad.AnnularStrongOrbit
