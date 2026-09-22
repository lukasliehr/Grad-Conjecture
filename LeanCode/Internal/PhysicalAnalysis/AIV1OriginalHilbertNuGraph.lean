import AIQ15UniformPhysicalHighInverseConsumer
import ADZ10UniformHighComparison
import ADX3CompatibleOmegaGrades

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularOriginalHigh
open Grad.ClosedJets Grad.AnnularVariational Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.CircularHighRegularity Grad.AnnularSourceGraph Grad.AnnularHighTilt Grad.GaugeCoefficients.Physical.WeightedTrace

def originalNuCoordinates (lower : ℝ) :
    AnnularOmegaAmbient lower →L[ℂ] AnnularFluxGraphAmbient lower :=
  (annularOmegaValue lower).prod (annularOmegaSlope lower)

/-- AK5 with its literal Hilbert sum norm and genuine ordinary derivative. -/
def originalNuGraph (lower : ℝ) (positive : 0 < lower) :
    Submodule ℂ (AnnularOmegaAmbient lower) :=
  (annularFluxWeakGraph lower positive).comap (originalNuCoordinates lower).toLinearMap

theorem originalNuGraph_closed (lower : ℝ) (positive : 0 < lower) :
    IsClosed (originalNuGraph lower positive : Set (AnnularOmegaAmbient lower)) :=
  (annularFluxWeakGraph_closed lower positive).preimage (originalNuCoordinates lower).continuous

instance originalNuGraph_complete (lower : ℝ) (positive : 0 < lower) :
    CompleteSpace (originalNuGraph lower positive) :=
  (originalNuGraph_closed lower positive).completeSpace_coe

theorem originalNuGraph_norm_sq (lower : ℝ) (positive : 0 < lower)
    (field : originalNuGraph lower positive) :
    ‖field‖ ^ 2 = ‖field.val 0‖ ^ 2 + ‖field.val 1‖ ^ 2 := by
  change ‖field.val‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]

theorem originalNuGraph_mem_iff (lower : ℝ) (positive : 0 < lower)
    (field : AnnularOmegaAmbient lower) :
    field ∈ originalNuGraph lower positive ↔
      ∀ mode, CollarWeakDerivative lower (radialOrdinary 1 lower positive (field 0 mode))
        ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 : ℝ) •
          radialOrdinary 1 lower positive (field 1 mode)) := Iff.rfl

def originalNuIntoPair (lower : ℝ) (positive : 0 < lower) :
    originalNuGraph lower positive →L[ℂ] annularFluxWeakGraph lower positive :=
  ((originalNuCoordinates lower).comp (originalNuGraph lower positive).subtypeL).codRestrict
    (annularFluxWeakGraph lower positive) (fun field => field.property)

def originalNuFromPairCoordinates (lower : ℝ) :
    AnnularFluxGraphAmbient lower →L[ℂ] AnnularOmegaAmbient lower :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => AnnularBulk lower)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![ContinuousLinearMap.fst ℂ _ _, ContinuousLinearMap.snd ℂ _ _])

def originalNuFromPair (lower : ℝ) (positive : 0 < lower) :
    annularFluxWeakGraph lower positive →L[ℂ] originalNuGraph lower positive :=
  ((originalNuFromPairCoordinates lower).comp (annularFluxWeakGraph lower positive).subtypeL).codRestrict
    (originalNuGraph lower positive) (fun field => field.property)

/-- Only the norm presentation changes; both coordinates are unchanged. -/
def originalNuPairEquivalence (lower : ℝ) (positive : 0 < lower) :
    originalNuGraph lower positive ≃L[ℂ] annularFluxWeakGraph lower positive where
  toLinearEquiv :=
    { toLinearMap := (originalNuIntoPair lower positive).toLinearMap
      invFun := originalNuFromPair lower positive
      left_inv := by
        intro field
        apply Subtype.ext
        apply PiLp.ext
        intro coordinate
        fin_cases coordinate <;> rfl
      right_inv := fun field => Subtype.ext (Prod.ext rfl rfl) }
  continuous_toFun := (originalNuIntoPair lower positive).continuous
  continuous_invFun := (originalNuFromPair lower positive).continuous

/-- Literal normalization between the two closed Hilbert derivative graphs. -/
def originalNuOmegaEquivalence (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) :
    originalNuGraph lower positive ≃L[ℂ] annularOmegaGraph lower length positive lengthPositive :=
  (originalNuPairEquivalence lower positive).trans
    (annularOmegaNormalizationEquivalence lower length positive lengthPositive).symm

theorem originalNuOmegaEquivalence_value (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (field : originalNuGraph lower positive) :
    (originalNuOmegaEquivalence lower length positive lengthPositive field).val 0 = field.val 0 := rfl

theorem originalNuOmegaEquivalence_slope (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (field : originalNuGraph lower positive) :
    (originalNuOmegaEquivalence lower length positive lengthPositive field).val 1 =
      annularNuToOmega lower length positive lengthPositive (field.val 1) := rfl

theorem originalNuOmegaEquivalence_symm_value (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (field : annularOmegaGraph lower length positive lengthPositive) :
    ((originalNuOmegaEquivalence lower length positive lengthPositive).symm field).val 0 = field.val 0 := rfl

theorem originalNuOmegaEquivalence_symm_slope (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (field : annularOmegaGraph lower length positive lengthPositive) :
    ((originalNuOmegaEquivalence lower length positive lengthPositive).symm field).val 1 =
      annularOmegaToNu lower length positive lengthPositive (field.val 1) := rfl

end Grad.AnnularOriginalHigh
