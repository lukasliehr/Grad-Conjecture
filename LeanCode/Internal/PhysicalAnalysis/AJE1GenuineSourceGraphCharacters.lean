import AIZ1ActualEnergyTranslations
import ASG3CompletedEndpoints

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit

/-- Complex multiplication acts on the genuine smooth radial value and its
actual derivative, before completion in the original real Hilbert graph. -/
def sourceCoreScalar (dimension : ℕ) (scalar : ℂ) (core : SmoothRadialCore dimension) :
    SmoothRadialCore dimension :=
  complexCoreToAccepted dimension (scalar • acceptedCoreToComplex dimension core)

theorem weightedRadialCore_scalar (dimension : ℕ) (lower : ℝ) (scalar : ℂ)
    (core : SmoothRadialCore dimension) :
    weightedRadialCore dimension lower (sourceCoreScalar dimension scalar core) =
      scalar • weightedRadialCore dimension lower core := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    exact weightedCurve_complex_smul lower scalar _

/-- Complex multiplication preserves the actual closed radial derivative
graph. This proves the action on the real carrier rather than assuming a
complex-module structure on it. -/
theorem weightedRadialH1_scalar_mem (dimension : ℕ) (lower : ℝ) (scalar : ℂ)
    (field : WeightedRadialAmbient dimension lower)
    (member : field ∈ WeightedRadialH1 dimension lower) :
    scalar • field ∈ WeightedRadialH1 dimension lower := by
  apply closure_minimal (s := (LinearMap.range (weightedRadialCore dimension lower) : Set _))
    (fun point coreMember => ?_)
    ((LinearMap.range (weightedRadialCore dimension lower)).isClosed_topologicalClosure.preimage
      (continuous_const_smul scalar)) member
  rcases coreMember with ⟨core,rfl⟩
  change scalar • weightedRadialCore dimension lower core ∈ WeightedRadialH1 dimension lower
  rw [← weightedRadialCore_scalar]
  exact Submodule.le_topologicalClosure _ ⟨sourceCoreScalar dimension scalar core,rfl⟩

def sourceGraphScalar (dimension : ℕ) (lower : ℝ) (scalar : ℂ) :
    WeightedRadialH1 dimension lower →L[ℝ] WeightedRadialH1 dimension lower :=
  ((((scalar • ContinuousLinearMap.id ℂ (WeightedRadialAmbient dimension lower)).restrictScalars ℝ).comp
    (WeightedRadialH1 dimension lower).subtypeL)).codRestrict
      (WeightedRadialH1 dimension lower)
      (fun field => weightedRadialH1_scalar_mem dimension lower scalar field.val field.property)

theorem sourceGraphScalar_value (dimension : ℕ) (lower : ℝ) (scalar : ℂ)
    (field : WeightedRadialH1 dimension lower) :
    (sourceGraphScalar dimension lower scalar field).val = scalar • field.val := rfl

theorem sourceGraphScalar_coordinate (dimension : ℕ) (lower : ℝ) (scalar : ℂ)
    (field : WeightedRadialH1 dimension lower) (coordinate : Fin 2) :
    weightedRadialCoordinate dimension lower coordinate (sourceGraphScalar dimension lower scalar field) =
      scalar • weightedRadialCoordinate dimension lower coordinate field := rfl

theorem sourceGraphScalar_norm (dimension : ℕ) (lower : ℝ) (scalar : ℂ)
    (field : WeightedRadialH1 dimension lower) :
    ‖sourceGraphScalar dimension lower scalar field‖ = ‖scalar‖ * ‖field‖ := by
  change ‖scalar • field.val‖ = ‖scalar‖ * ‖field.val‖
  exact norm_smul scalar field.val

theorem sourceGraphScalar_core (dimension : ℕ) (lower : ℝ) (scalar : ℂ)
    (core : SmoothRadialCore dimension) :
    sourceGraphScalar dimension lower scalar (weightedRadialCoreInto dimension lower core) =
      weightedRadialCoreInto dimension lower (sourceCoreScalar dimension scalar core) := by
  apply Subtype.ext
  exact (weightedRadialCore_scalar dimension lower scalar core).symm

theorem sourceGraphScalar_trace (dimension : ℕ) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (endpoint : Fin 2) (scalar : ℂ)
    (field : WeightedRadialH1 dimension lower) :
    weightedRadialTrace dimension lower positive bounded endpoint (sourceGraphScalar dimension lower scalar field) =
      scalar • weightedRadialTrace dimension lower positive bounded endpoint field := by
  apply isClosed_property (weightedRadialCoreInto_denseRange dimension lower)
    (isClosed_eq
      ((weightedRadialTrace dimension lower positive bounded endpoint).continuous.comp
        (sourceGraphScalar dimension lower scalar).continuous)
      ((weightedRadialTrace dimension lower positive bounded endpoint).continuous.const_smul scalar)) _ field
  intro core
  change weightedRadialTrace dimension lower positive bounded endpoint
      (sourceGraphScalar dimension lower scalar (weightedRadialCoreInto dimension lower core)) =
    scalar • weightedRadialTrace dimension lower positive bounded endpoint
      (weightedRadialCoreInto dimension lower core)
  rw [sourceGraphScalar_core, weightedRadialTrace_core, weightedRadialTrace_core]
  rfl

def sourceGraphTranslation (dimension : ℕ) (lower : ℝ) (tau : OrbitParameter) :
    lp (fun _ : ℤ × ℤ => WeightedRadialH1 dimension lower) 2 →L[ℝ]
      lp (fun _ : ℤ × ℤ => WeightedRadialH1 dimension lower) 2 :=
  lpTwoMap (fun mode => sourceGraphScalar dimension lower (orbitCharacter tau mode)) 1 (by norm_num)
    (fun mode field => by rw [sourceGraphScalar_norm,orbitCharacter_norm,one_mul])

theorem sourceGraphTranslation_apply (dimension : ℕ) (lower : ℝ) (tau : OrbitParameter)
    (field : lp (fun _ : ℤ × ℤ => WeightedRadialH1 dimension lower) 2) (mode : ℤ × ℤ) :
    sourceGraphTranslation dimension lower tau field mode =
      sourceGraphScalar dimension lower (orbitCharacter tau mode) (field mode) := rfl

theorem sourceGraphTranslation_norm (dimension : ℕ) (lower : ℝ) (tau : OrbitParameter)
    (field : lp (fun _ : ℤ × ℤ => WeightedRadialH1 dimension lower) 2) :
    ‖sourceGraphTranslation dimension lower tau field‖ = ‖field‖ := by
  have point (mode : ℤ × ℤ) : ‖sourceGraphTranslation dimension lower tau field mode‖ = ‖field mode‖ := by
    rw [sourceGraphTranslation_apply,sourceGraphScalar_norm,orbitCharacter_norm,one_mul]
  exact le_antisymm (lp.norm_mono (by norm_num) (fun mode => (point mode).le))
    (lp.norm_mono (by norm_num) (fun mode => (point mode).ge))

/-- Both genuine graph traces commute with the same physical Fourier character. -/
theorem annularSourceTrace_translation (parameters : PhaseParameters) (dimension : ℕ)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (angular cell : ℕ)
    (endpoint : Fin 2) (tau : OrbitParameter)
    (field : AnnularSourceH1 parameters dimension lower angular cell) :
    annularSourceTrace parameters dimension lower positive bounded angular cell endpoint
      (sourceGraphTranslation dimension lower tau field) =
      orbitLpAction (ComplexEuclidean dimension) tau
        (annularSourceTrace parameters dimension lower positive bounded angular cell endpoint field) := by
  apply lp.ext
  funext mode
  rw [annularSourceTrace_apply,sourceGraphTranslation_apply,sourceGraphScalar_trace,
    orbitLpAction_apply,annularSourceTrace_apply]

end Grad.AnnularStrongOrbit
