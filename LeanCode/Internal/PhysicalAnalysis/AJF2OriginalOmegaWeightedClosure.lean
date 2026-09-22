import AJF1OriginalHighEnergyWeightedClosure
import AIZ2ActualFluxTranslations
import AJB18OriginalLowGradeMembership

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Filter
open scoped Topology BigOperators
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularOmegaGraph Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularLowOrbit Grad.CircularHighRegularity Grad.AnnularReconstruction

/-- Arbitrary scalar Fourier weights preserve the genuine Domega weak
derivative when BOTH original normalized coordinates are square summable. -/
def fluxSummableMultiplier (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : annularOmegaGraph lower length positive lengthPositive)
    (coefficient : HighAnnularMode → ℂ)
    (summable : ∀ coordinate : Fin 2, Memℓp (fun index => coefficient index • field.val coordinate index) 2) :
    annularOmegaGraph lower length positive lengthPositive :=
  ⟨WithLp.toLp 2 (fun coordinate => ⟨fun index => coefficient index • field.val coordinate index, summable coordinate⟩), by
    rw [annularOmegaGraph_mem_iff]
    intro index
    change CollarWeakDerivative lower
      (radialOrdinary 1 lower positive (coefficient index • field.val 0 index))
      (collarScalar 1 lower (annularOmegaCurve lower length positive index)
        (radialOrdinary 1 lower positive (coefficient index • field.val 1 index)))
    rw [map_smul, map_smul, map_smul]
    exact collarWeakDerivative_complex_smul lower (coefficient index) _ _
      ((annularOmegaGraph_mem_iff lower length positive lengthPositive field.val).mp field.property index)⟩

theorem fluxSummableMultiplier_apply (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : annularOmegaGraph lower length positive lengthPositive)
    (coefficient : HighAnnularMode → ℂ)
    (summable : ∀ coordinate : Fin 2, Memℓp (fun index => coefficient index • field.val coordinate index) 2)
    (coordinate : Fin 2) (index : HighAnnularMode) :
    (fluxSummableMultiplier lower length positive lengthPositive field coefficient summable).val coordinate index =
      coefficient index • field.val coordinate index := rfl

def fluxStoredCoordinate (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (coordinate : Fin 2) :
    annularOmegaGraph lower length positive lengthPositive →L[ℂ] AnnularBulk lower :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => AnnularBulk lower) coordinate).comp
    (annularOmegaGraph lower length positive lengthPositive).subtypeL

theorem fluxStoredCoordinate_bound (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (coordinate : Fin 2) (field : annularOmegaGraph lower length positive lengthPositive) :
    ‖field.val coordinate‖ ≤ ‖field‖ := by
  have squared := annularOmegaGraph_norm_sq lower length positive lengthPositive field
  fin_cases coordinate
  · change ‖field.val 0‖ ≤ ‖field‖
    nlinarith only [squared, norm_nonneg field, norm_nonneg (field.val 0), norm_nonneg (field.val 1),
      sq_nonneg ‖field.val 0‖, sq_nonneg ‖field.val 1‖]
  · change ‖field.val 1‖ ≤ ‖field‖
    nlinarith only [squared, norm_nonneg field, norm_nonneg (field.val 0), norm_nonneg (field.val 1),
      sq_nonneg ‖field.val 0‖, sq_nonneg ‖field.val 1‖]

end Grad.AnnularHighGenerators
