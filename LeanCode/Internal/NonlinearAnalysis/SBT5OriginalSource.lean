import SBT4BoundaryAngular
import AXF21CartesianSource
import Q23DerivativeDot

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceBoundaryTrace
open Grad.ClosedJets Grad.CartesianState Grad.AxisCore Grad.QuotientProjection
open Grad.FlatSourceProjection Grad.NonlinearProduct Grad.NonlinearQuotientBounds

def sourceComponent (parameters : PhaseParameters) (grade : ℕ) (coordinate : Fin 4) :
    ZAmbient parameters grade →L[ℂ] AGrade parameters 1 grade :=
  PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 4 => AGrade parameters 1 grade) coordinate

def sourceSpinFirst (parameters : PhaseParameters) (grade : ℕ) :
    ZAmbient parameters grade →L[ℂ] AGrade parameters 1 grade :=
  (1 / 2 : ℂ) • (sourceComponent parameters grade 0 + sourceComponent parameters grade 1)

def sourceSpinSecond (parameters : PhaseParameters) (grade : ℕ) :
    ZAmbient parameters grade →L[ℂ] AGrade parameters 1 grade :=
  (-Complex.I / 2) • (sourceComponent parameters grade 0 - sourceComponent parameters grade 1)

theorem sourceSpinFirst_core (parameters : PhaseParameters) (grade : ℕ) (field : SmoothQuotient parameters) :
    sourceSpinFirst parameters grade (quotientEta parameters grade field) =
      aGradeEta parameters (GradeCore.ofCoreLinear (cartesianSpinFirst field)) := by
  change (1 / 2 : ℂ) • (aGradeEta parameters (GradeCore.ofCoreLinear (field 0)) +
    aGradeEta parameters (GradeCore.ofCoreLinear (field 1))) =
      aGradeEta parameters (GradeCore.ofCoreLinear ((1 / 2 : ℂ) • (field 0 + field 1)))
  rw [map_smul, map_smul, map_add, map_add]

theorem sourceSpinSecond_core (parameters : PhaseParameters) (grade : ℕ) (field : SmoothQuotient parameters) :
    sourceSpinSecond parameters grade (quotientEta parameters grade field) =
      aGradeEta parameters (GradeCore.ofCoreLinear (cartesianSpinSecond field)) := by
  change (-Complex.I / 2) • (aGradeEta parameters (GradeCore.ofCoreLinear (field 0)) -
    aGradeEta parameters (GradeCore.ofCoreLinear (field 1))) =
      aGradeEta parameters (GradeCore.ofCoreLinear ((-Complex.I / 2) • (field 0 - field 1)))
  rw [map_smul, map_smul, map_sub, map_sub]

def sourceCartesianCompleted (parameters : PhaseParameters) (grade : ℕ) :
    ZAmbient parameters grade →L[ℂ] AGrade parameters 2 grade :=
  (q23ValueMapCompleted parameters (componentInsertion 0)).comp (sourceSpinFirst parameters grade) +
    (q23ValueMapCompleted parameters (componentInsertion 1)).comp (sourceSpinSecond parameters grade)

theorem sourceCartesianCompleted_core (parameters : PhaseParameters) (grade : ℕ) (field : SmoothQuotient parameters) :
    sourceCartesianCompleted parameters grade (quotientEta parameters grade field) =
      aGradeEta parameters (GradeCore.ofCoreLinear (cartesianSourceVector field)) := by
  change q23ValueMapCompleted parameters (componentInsertion 0) (sourceSpinFirst parameters grade (quotientEta parameters grade field)) +
    q23ValueMapCompleted parameters (componentInsertion 1) (sourceSpinSecond parameters grade (quotientEta parameters grade field)) = _
  rw [sourceSpinFirst_core, sourceSpinSecond_core, q23ValueMapCompleted_core, q23ValueMapCompleted_core]
  change _ = aGradeEta parameters (GradeCore.ofCoreLinear
    (Grad.Constraints.valueMapCore (componentInsertion 0) parameters (cartesianSpinFirst field) +
      Grad.Constraints.valueMapCore (componentInsertion 1) parameters (cartesianSpinSecond field)))
  rw [map_add, map_add]

/-- The original fourfold Hilbert norm, with its exact spin weight two,
controls the actual two-component Cartesian field. -/
theorem sourceCartesianCompleted_bound (parameters : PhaseParameters) (grade : ℕ)
    (field : ZAmbient parameters grade) :
    ‖sourceCartesianCompleted parameters grade field‖ ≤ ‖field‖ := by
  refine isClosed_property (quotientEta_denseRange parameters grade)
    (isClosed_le (sourceCartesianCompleted parameters grade).continuous.norm continuous_norm) ?_ field
  intro core
  rw [sourceCartesianCompleted_core, aGradeEta_norm]
  change originalGradeNorm grade (cartesianSourceVector core) ≤ quotientNorm parameters grade core
  have identity := originalSpin_cartesian_vector_norm parameters grade core
  have nonnegative : 0 ≤ quotientNorm parameters grade core := norm_nonneg _
  nlinarith [originalGradeNorm_nonnegative grade (cartesianSourceVector core),
    sq_nonneg (originalGradeNorm grade (core 2)), sq_nonneg (originalGradeNorm grade (core 3))]

end Grad.SourceBoundaryTrace
