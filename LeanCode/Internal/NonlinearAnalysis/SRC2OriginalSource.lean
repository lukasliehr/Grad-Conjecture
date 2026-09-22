import SRC1AngularGraph
import AXF21CartesianSource
import Q23DerivativeDot

noncomputable section

namespace Grad.SourceCollarBulk

open Grad.ClosedJets Grad.CartesianState Grad.AxisCore Grad.QuotientProjection
open Grad.FlatSourceProjection Grad.NonlinearProduct Grad.NonlinearQuotientBounds

/-- One actual coordinate of the completed fourfold original source. -/
def originalSourceComponent (parameters : PhaseParameters) (grade : ℕ)
    (coordinate : Fin 4) :
    ZAmbient parameters grade →L[ℂ] AGrade parameters 1 grade :=
  PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 4 => AGrade parameters 1 grade) coordinate

@[simp] theorem originalSourceComponent_apply (parameters : PhaseParameters)
    (grade : ℕ) (coordinate : Fin 4) (source : ZAmbient parameters grade) :
    originalSourceComponent parameters grade coordinate source = source coordinate := rfl

theorem originalSourceComponent_core (parameters : PhaseParameters) (grade : ℕ)
    (coordinate : Fin 4) (source : SmoothQuotient parameters) :
    originalSourceComponent parameters grade coordinate
        (quotientEta parameters grade source) =
      aGradeEta parameters (GradeCore.ofCoreLinear (source coordinate)) := rfl

theorem originalSourceComponent_bound (parameters : PhaseParameters) (grade : ℕ)
    (coordinate : Fin 4) (source : ZAmbient parameters grade) :
    ‖originalSourceComponent parameters grade coordinate source‖ ≤ ‖source‖ :=
  zComponent_norm_le parameters grade coordinate source

def originalSourceSpinFirst (parameters : PhaseParameters) (grade : ℕ) :
    ZAmbient parameters grade →L[ℂ] AGrade parameters 1 grade :=
  (1 / 2 : ℂ) •
    (originalSourceComponent parameters grade 0 +
      originalSourceComponent parameters grade 1)

def originalSourceSpinSecond (parameters : PhaseParameters) (grade : ℕ) :
    ZAmbient parameters grade →L[ℂ] AGrade parameters 1 grade :=
  (-Complex.I / 2) •
    (originalSourceComponent parameters grade 0 -
      originalSourceComponent parameters grade 1)

theorem originalSourceSpinFirst_core (parameters : PhaseParameters) (grade : ℕ)
    (source : SmoothQuotient parameters) :
    originalSourceSpinFirst parameters grade (quotientEta parameters grade source) =
      aGradeEta parameters
        (GradeCore.ofCoreLinear (cartesianSpinFirst source)) := by
  change (1 / 2 : ℂ) •
      (aGradeEta parameters (GradeCore.ofCoreLinear (source 0)) +
        aGradeEta parameters (GradeCore.ofCoreLinear (source 1))) =
    aGradeEta parameters
      (GradeCore.ofCoreLinear ((1 / 2 : ℂ) • (source 0 + source 1)))
  rw [map_smul, map_smul, map_add, map_add]

theorem originalSourceSpinSecond_core (parameters : PhaseParameters) (grade : ℕ)
    (source : SmoothQuotient parameters) :
    originalSourceSpinSecond parameters grade (quotientEta parameters grade source) =
      aGradeEta parameters
        (GradeCore.ofCoreLinear (cartesianSpinSecond source)) := by
  change (-Complex.I / 2) •
      (aGradeEta parameters (GradeCore.ofCoreLinear (source 0)) -
        aGradeEta parameters (GradeCore.ofCoreLinear (source 1))) =
    aGradeEta parameters
      (GradeCore.ofCoreLinear ((-Complex.I / 2) • (source 0 - source 1)))
  rw [map_smul, map_smul, map_sub, map_sub]

/-- Exact completed Cartesian two-vector reconstructed from the two spin
coordinates. Its norm is controlled by the literal fourfold Hilbert source
norm, with the BS3 factor two used in the core proof. -/
def originalSourcePlanar (parameters : PhaseParameters) (grade : ℕ) :
    ZAmbient parameters grade →L[ℂ] AGrade parameters 2 grade :=
  (q23ValueMapCompleted parameters (componentInsertion 0)).comp
      (originalSourceSpinFirst parameters grade) +
    (q23ValueMapCompleted parameters (componentInsertion 1)).comp
      (originalSourceSpinSecond parameters grade)

theorem originalSourcePlanar_core (parameters : PhaseParameters) (grade : ℕ)
    (source : SmoothQuotient parameters) :
    originalSourcePlanar parameters grade (quotientEta parameters grade source) =
      aGradeEta parameters
        (GradeCore.ofCoreLinear (cartesianSourceVector source)) := by
  change q23ValueMapCompleted parameters (componentInsertion 0)
      (originalSourceSpinFirst parameters grade (quotientEta parameters grade source)) +
    q23ValueMapCompleted parameters (componentInsertion 1)
      (originalSourceSpinSecond parameters grade (quotientEta parameters grade source)) = _
  rw [originalSourceSpinFirst_core, originalSourceSpinSecond_core,
    q23ValueMapCompleted_core, q23ValueMapCompleted_core]
  change _ = aGradeEta parameters (GradeCore.ofCoreLinear
    (Grad.Constraints.valueMapCore (componentInsertion 0) parameters
        (cartesianSpinFirst source) +
      Grad.Constraints.valueMapCore (componentInsertion 1) parameters
        (cartesianSpinSecond source)))
  rw [map_add, map_add]

theorem originalSourcePlanar_bound (parameters : PhaseParameters) (grade : ℕ)
    (source : ZAmbient parameters grade) :
    ‖originalSourcePlanar parameters grade source‖ ≤ ‖source‖ := by
  refine isClosed_property (quotientEta_denseRange parameters grade)
    (isClosed_le (originalSourcePlanar parameters grade).continuous.norm continuous_norm) ?_ source
  intro core
  rw [originalSourcePlanar_core, aGradeEta_norm]
  change originalGradeNorm grade (cartesianSourceVector core) ≤
    quotientNorm parameters grade core
  have identity := originalSpin_cartesian_vector_norm parameters grade core
  have nonnegative : 0 ≤ quotientNorm parameters grade core := norm_nonneg _
  nlinarith [originalGradeNorm_nonnegative grade (cartesianSourceVector core),
    sq_nonneg (originalGradeNorm grade (core 2)),
    sq_nonneg (originalGradeNorm grade (core 3))]

end Grad.SourceCollarBulk
