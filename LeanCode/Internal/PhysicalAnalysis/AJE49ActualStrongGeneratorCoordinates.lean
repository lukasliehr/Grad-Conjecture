import AJE48FiniteCompleteStrongOrbit
import AJE47RealSourceGeneratorCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open scoped ContDiff
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.BoundaryKernelAction
open Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularKernelL2 Grad.AnnularOrbitGenerators Grad.AnnularLowEnergy Grad.AnnularLowOrbit Grad.AnnularInverseCalculus
attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)

def strongRawHighInput : StrongDataCarrier parameters lower positive bounded 0 0 →L[ℝ]
    ActualHighKnownAmbient parameters lower 0 0 :=
  (strongSharedProjection parameters lower 0 0).comp (StrongDataCarrier parameters lower positive bounded 0 0).subtypeL

def strongKnownObservation (slot : Fin 4) : StrongDataCarrier parameters lower positive bounded 0 0 →L[ℝ] DivisionRow 1 lower :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 4 => DivisionRow 1 lower) slot).comp ((highKnownWeightedProjection parameters lower 0 0).comp (strongRawHighInput parameters lower positive bounded))

theorem strongKnownObservation_apply (slot : Fin 4) (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    strongKnownObservation parameters lower positive bounded slot data = data.val.ofLp.1.ofLp.1.ofLp.1 slot := rfl

theorem strongKnownObservation_bound (slot : Fin 4) (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    ‖strongKnownObservation parameters lower positive bounded slot data‖ ≤ ‖data‖ := by
  rw [strongKnownObservation_apply]
  exact (StrongDataCarrier.component_bounds parameters lower positive bounded 0 0 data).1 slot

theorem strongKnownObservation_translation (slot : Fin 4) (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (tau : OrbitParameter) (mode : (ℤ × ℤ)) :
    strongKnownObservation parameters lower positive bounded slot
      (strongDataTranslation parameters lower positive bounded 0 0 tau data) mode =
        orbitCharacter tau mode • strongKnownObservation parameters lower positive bounded slot data mode := rfl

def strongAuxiliaryObservation (slot : Fin 3) : StrongDataCarrier parameters lower positive bounded 0 0 →L[ℝ] DivisionRow 1 lower :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 3 => DivisionRow 1 lower) slot).comp ((highKnownAuxiliaryProjection parameters lower 0 0).comp (strongRawHighInput parameters lower positive bounded))

theorem strongAuxiliaryObservation_apply (slot : Fin 3) (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    strongAuxiliaryObservation parameters lower positive bounded slot data = data.val.ofLp.1.ofLp.1.ofLp.2 slot := rfl

theorem strongAuxiliaryObservation_bound (slot : Fin 3) (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    ‖strongAuxiliaryObservation parameters lower positive bounded slot data‖ ≤ ‖data‖ := by
  rw [strongAuxiliaryObservation_apply]
  exact (StrongDataCarrier.component_bounds parameters lower positive bounded 0 0 data).2.1 slot

theorem strongAuxiliaryObservation_translation (slot : Fin 3) (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (tau : OrbitParameter) (mode : (ℤ × ℤ)) :
    strongAuxiliaryObservation parameters lower positive bounded slot
      (strongDataTranslation parameters lower positive bounded 0 0 tau data) mode =
        orbitCharacter tau mode • strongAuxiliaryObservation parameters lower positive bounded slot data mode := rfl

def strongF0Observation  : StrongDataCarrier parameters lower positive bounded 0 0 →L[ℝ] lp (fun _ : ℤ × ℤ => WeightedRadialAmbient 1 lower) 2 :=
  (sourceGraphLpAmbient 1 lower).comp ((highKnownF0GraphProjection parameters lower 0 0).comp (strongRawHighInput parameters lower positive bounded))

theorem strongF0Observation_apply  (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    strongF0Observation parameters lower positive bounded  data = sourceGraphLpAmbient 1 lower data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.1 := rfl

theorem strongF0Observation_bound  (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    ‖strongF0Observation parameters lower positive bounded  data‖ ≤ ‖data‖ := by
  rw [strongF0Observation_apply]
  rw [sourceGraphLpAmbient_norm]
  exact (StrongDataCarrier.component_bounds parameters lower positive bounded 0 0 data).2.2.1

theorem strongF0Observation_translation  (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (tau : OrbitParameter) (mode : (ℤ × ℤ)) :
    strongF0Observation parameters lower positive bounded 
      (strongDataTranslation parameters lower positive bounded 0 0 tau data) mode =
        orbitCharacter tau mode • strongF0Observation parameters lower positive bounded  data mode := rfl

def strongF2Observation  : StrongDataCarrier parameters lower positive bounded 0 0 →L[ℝ] lp (fun _ : ℤ × ℤ => WeightedRadialAmbient 1 lower) 2 :=
  (sourceGraphLpAmbient 1 lower).comp ((highKnownF2GraphProjection parameters lower 0 0).comp (strongRawHighInput parameters lower positive bounded))

theorem strongF2Observation_apply  (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    strongF2Observation parameters lower positive bounded  data = sourceGraphLpAmbient 1 lower data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2 := rfl

theorem strongF2Observation_bound  (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    ‖strongF2Observation parameters lower positive bounded  data‖ ≤ ‖data‖ := by
  rw [strongF2Observation_apply]
  rw [sourceGraphLpAmbient_norm]
  exact (StrongDataCarrier.component_bounds parameters lower positive bounded 0 0 data).2.2.2.1

theorem strongF2Observation_translation  (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (tau : OrbitParameter) (mode : (ℤ × ℤ)) :
    strongF2Observation parameters lower positive bounded 
      (strongDataTranslation parameters lower positive bounded 0 0 tau data) mode =
        orbitCharacter tau mode • strongF2Observation parameters lower positive bounded  data mode := rfl

def strongOuterObservation  : StrongDataCarrier parameters lower positive bounded 0 0 →L[ℝ] NegativeTrace parameters 0 0 1 :=
  ((highAngularSubmodule parameters 0 0 1).subtypeL.restrictScalars ℝ).comp ((highKnownDatumProjection parameters lower 0 0).comp (strongRawHighInput parameters lower positive bounded))

theorem strongOuterObservation_apply  (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    strongOuterObservation parameters lower positive bounded  data = data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.1.val := rfl

theorem strongOuterObservation_bound  (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    ‖strongOuterObservation parameters lower positive bounded  data‖ ≤ ‖data‖ := by
  rw [strongOuterObservation_apply]
  exact (StrongDataCarrier.component_bounds parameters lower positive bounded 0 0 data).2.2.2.2.1

theorem strongOuterObservation_translation  (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (tau : OrbitParameter) (mode : (ℤ × ℤ)) :
    strongOuterObservation parameters lower positive bounded 
      (strongDataTranslation parameters lower positive bounded 0 0 tau data) mode =
        orbitCharacter tau mode • strongOuterObservation parameters lower positive bounded  data mode := rfl

def strongHighIncomingObservation  : StrongDataCarrier parameters lower positive bounded 0 0 →L[ℝ] AnnularBoundary :=
  (highKnownIncomingProjection parameters lower 0 0).comp (strongRawHighInput parameters lower positive bounded)

theorem strongHighIncomingObservation_apply  (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    strongHighIncomingObservation parameters lower positive bounded  data = data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.2 := rfl

theorem strongHighIncomingObservation_bound  (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    ‖strongHighIncomingObservation parameters lower positive bounded  data‖ ≤ ‖data‖ := by
  rw [strongHighIncomingObservation_apply]
  exact (StrongDataCarrier.component_bounds parameters lower positive bounded 0 0 data).2.2.2.2.2.1

theorem strongHighIncomingObservation_translation  (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (tau : OrbitParameter) (mode : HighAnnularMode) :
    strongHighIncomingObservation parameters lower positive bounded 
      (strongDataTranslation parameters lower positive bounded 0 0 tau data) mode =
        orbitCharacter tau mode.val • strongHighIncomingObservation parameters lower positive bounded  data mode := rfl

def strongLowIncomingObservation  : StrongDataCarrier parameters lower positive bounded 0 0 →L[ℝ] LowEnergyBoundary :=
  (strongLowIncomingProjection parameters lower 0 0).comp (StrongDataCarrier parameters lower positive bounded 0 0).subtypeL

theorem strongLowIncomingObservation_apply  (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    strongLowIncomingObservation parameters lower positive bounded  data = data.val.ofLp.2 := rfl

theorem strongLowIncomingObservation_bound  (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    ‖strongLowIncomingObservation parameters lower positive bounded  data‖ ≤ ‖data‖ := by
  rw [strongLowIncomingObservation_apply]
  exact (StrongDataCarrier.component_bounds parameters lower positive bounded 0 0 data).2.2.2.2.2.2

theorem strongLowIncomingObservation_translation  (data : StrongDataCarrier parameters lower positive bounded 0 0)
    (tau : OrbitParameter) (index : LowAnnularIndex) :
    strongLowIncomingObservation parameters lower positive bounded 
      (strongDataTranslation parameters lower positive bounded 0 0 tau data) index =
        orbitCharacter tau index.2.val • strongLowIncomingObservation parameters lower positive bounded  data index := rfl

/-- Derivatives are genuine vectors in the SAME complete shared carrier. -/
def strongAxisGenerator (data : StrongDataCarrier parameters lower positive bounded 0 0) (axis : Bool) (order : ℕ) :
    StrongDataCarrier parameters lower positive bounded 0 0 :=
  iteratedDeriv order (fun time : ℝ => strongDataTranslation parameters lower positive bounded 0 0 (time • axisVector axis) data) 0

variable (data : StrongDataCarrier parameters lower positive bounded 0 0) (support : StrongCutSupport)
    (finite : StrongSupported parameters lower positive bounded support data) (axis : Bool) (order : ℕ)

include support finite in
theorem strongAxisGenerator_Known (slot : Fin 4) (mode : (ℤ × ℤ)) :
    strongKnownObservation parameters lower positive bounded slot
      (strongAxisGenerator parameters lower positive bounded data axis order) mode =
        (Complex.I * (sourceAxisFrequency axis mode : ℂ)) ^ order •
          strongKnownObservation parameters lower positive bounded slot data mode :=
  realSourceGenerator_coordinates (strongKnownObservation parameters lower positive bounded slot) _
    (finiteStrongDataOrbit_contDiff parameters lower positive bounded data support finite axis)
    (fun index : (ℤ × ℤ) => sourceAxisFrequency axis index)
    (strongKnownObservation parameters lower positive bounded slot data)
    (fun time index => (strongKnownObservation_translation parameters lower positive bounded slot data (time • axisVector axis) index).trans
      (congrArg (fun scalar : ℂ => scalar • strongKnownObservation parameters lower positive bounded slot data index)
        (sourceOrbitCharacter_axis axis time index))) order mode

include support finite in
theorem strongAxisGenerator_Auxiliary (slot : Fin 3) (mode : (ℤ × ℤ)) :
    strongAuxiliaryObservation parameters lower positive bounded slot
      (strongAxisGenerator parameters lower positive bounded data axis order) mode =
        (Complex.I * (sourceAxisFrequency axis mode : ℂ)) ^ order •
          strongAuxiliaryObservation parameters lower positive bounded slot data mode :=
  realSourceGenerator_coordinates (strongAuxiliaryObservation parameters lower positive bounded slot) _
    (finiteStrongDataOrbit_contDiff parameters lower positive bounded data support finite axis)
    (fun index : (ℤ × ℤ) => sourceAxisFrequency axis index)
    (strongAuxiliaryObservation parameters lower positive bounded slot data)
    (fun time index => (strongAuxiliaryObservation_translation parameters lower positive bounded slot data (time • axisVector axis) index).trans
      (congrArg (fun scalar : ℂ => scalar • strongAuxiliaryObservation parameters lower positive bounded slot data index)
        (sourceOrbitCharacter_axis axis time index))) order mode

include support finite in
theorem strongAxisGenerator_F0  (mode : (ℤ × ℤ)) :
    strongF0Observation parameters lower positive bounded 
      (strongAxisGenerator parameters lower positive bounded data axis order) mode =
        (Complex.I * (sourceAxisFrequency axis mode : ℂ)) ^ order •
          strongF0Observation parameters lower positive bounded  data mode :=
  realSourceGenerator_coordinates (strongF0Observation parameters lower positive bounded ) _
    (finiteStrongDataOrbit_contDiff parameters lower positive bounded data support finite axis)
    (fun index : (ℤ × ℤ) => sourceAxisFrequency axis index)
    (strongF0Observation parameters lower positive bounded  data)
    (fun time index => (strongF0Observation_translation parameters lower positive bounded  data (time • axisVector axis) index).trans
      (congrArg (fun scalar : ℂ => scalar • strongF0Observation parameters lower positive bounded  data index)
        (sourceOrbitCharacter_axis axis time index))) order mode

include support finite in
theorem strongAxisGenerator_F2  (mode : (ℤ × ℤ)) :
    strongF2Observation parameters lower positive bounded 
      (strongAxisGenerator parameters lower positive bounded data axis order) mode =
        (Complex.I * (sourceAxisFrequency axis mode : ℂ)) ^ order •
          strongF2Observation parameters lower positive bounded  data mode :=
  realSourceGenerator_coordinates (strongF2Observation parameters lower positive bounded ) _
    (finiteStrongDataOrbit_contDiff parameters lower positive bounded data support finite axis)
    (fun index : (ℤ × ℤ) => sourceAxisFrequency axis index)
    (strongF2Observation parameters lower positive bounded  data)
    (fun time index => (strongF2Observation_translation parameters lower positive bounded  data (time • axisVector axis) index).trans
      (congrArg (fun scalar : ℂ => scalar • strongF2Observation parameters lower positive bounded  data index)
        (sourceOrbitCharacter_axis axis time index))) order mode

include support finite in
theorem strongAxisGenerator_Outer  (mode : (ℤ × ℤ)) :
    strongOuterObservation parameters lower positive bounded 
      (strongAxisGenerator parameters lower positive bounded data axis order) mode =
        (Complex.I * (sourceAxisFrequency axis mode : ℂ)) ^ order •
          strongOuterObservation parameters lower positive bounded  data mode :=
  realSourceGenerator_coordinates (strongOuterObservation parameters lower positive bounded ) _
    (finiteStrongDataOrbit_contDiff parameters lower positive bounded data support finite axis)
    (fun index : (ℤ × ℤ) => sourceAxisFrequency axis index)
    (strongOuterObservation parameters lower positive bounded  data)
    (fun time index => (strongOuterObservation_translation parameters lower positive bounded  data (time • axisVector axis) index).trans
      (congrArg (fun scalar : ℂ => scalar • strongOuterObservation parameters lower positive bounded  data index)
        (sourceOrbitCharacter_axis axis time index))) order mode

include support finite in
theorem strongAxisGenerator_HighIncoming  (mode : HighAnnularMode) :
    strongHighIncomingObservation parameters lower positive bounded 
      (strongAxisGenerator parameters lower positive bounded data axis order) mode =
        (Complex.I * (sourceAxisFrequency axis mode.val : ℂ)) ^ order •
          strongHighIncomingObservation parameters lower positive bounded  data mode :=
  realSourceGenerator_coordinates (strongHighIncomingObservation parameters lower positive bounded ) _
    (finiteStrongDataOrbit_contDiff parameters lower positive bounded data support finite axis)
    (fun index : HighAnnularMode => sourceAxisFrequency axis index.val)
    (strongHighIncomingObservation parameters lower positive bounded  data)
    (fun time index => (strongHighIncomingObservation_translation parameters lower positive bounded  data (time • axisVector axis) index).trans
      (congrArg (fun scalar : ℂ => scalar • strongHighIncomingObservation parameters lower positive bounded  data index)
        (sourceOrbitCharacter_axis axis time index.val))) order mode

include support finite in
theorem strongAxisGenerator_LowIncoming  (index : LowAnnularIndex) :
    strongLowIncomingObservation parameters lower positive bounded 
      (strongAxisGenerator parameters lower positive bounded data axis order) index =
        (Complex.I * (sourceAxisFrequency axis index.2.val : ℂ)) ^ order •
          strongLowIncomingObservation parameters lower positive bounded  data index :=
  realSourceGenerator_coordinates (strongLowIncomingObservation parameters lower positive bounded ) _
    (finiteStrongDataOrbit_contDiff parameters lower positive bounded data support finite axis)
    (fun index : LowAnnularIndex => sourceAxisFrequency axis index.2.val)
    (strongLowIncomingObservation parameters lower positive bounded  data)
    (fun time index => (strongLowIncomingObservation_translation parameters lower positive bounded  data (time • axisVector axis) index).trans
      (congrArg (fun scalar : ℂ => scalar • strongLowIncomingObservation parameters lower positive bounded  data index)
        (sourceOrbitCharacter_axis axis time index.2.val))) order index

end Grad.AnnularStrongOrbit
