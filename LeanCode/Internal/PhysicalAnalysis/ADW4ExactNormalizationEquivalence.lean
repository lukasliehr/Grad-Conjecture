import ADW3LiteralClosedOmegaGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularOmegaGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularGrades Grad.AnnularFluxTrace
open Grad.CircularHighRegularity Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Bounded inverse normalization, with the ORIGINAL Hilbert norm retained
on the omega graph. The comparison graph is used only through an equivalence. -/
def annularOmegaFromNuCoordinates (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    AnnularFluxGraphAmbient lower →L[ℂ] AnnularOmegaAmbient lower :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 2 => AnnularBulk lower)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![ContinuousLinearMap.fst ℂ _ _,
      (annularNuToOmega lower length positive lengthPositive).comp (ContinuousLinearMap.snd ℂ _ _)])

theorem annularOmegaCoordinates_right (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : AnnularFluxGraphAmbient lower) :
    annularOmegaNuCoordinates lower length positive lengthPositive
      (annularOmegaFromNuCoordinates lower length positive lengthPositive field) = field := by
  apply Prod.ext
  · rfl
  · exact annularOmegaToNu_right lower length positive lengthPositive field.2

theorem annularOmegaCoordinates_left (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : AnnularOmegaAmbient lower) :
    annularOmegaFromNuCoordinates lower length positive lengthPositive
      (annularOmegaNuCoordinates lower length positive lengthPositive field) = field := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · rfl
  · exact annularNuToOmega_left lower length positive lengthPositive (field 1)

theorem annularOmegaFromNu_mem (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : annularFluxWeakGraph lower positive) :
    annularOmegaFromNuCoordinates lower length positive lengthPositive field.val ∈
      annularOmegaGraph lower length positive lengthPositive := by
  change annularOmegaNuCoordinates lower length positive lengthPositive
    (annularOmegaFromNuCoordinates lower length positive lengthPositive field.val) ∈ annularFluxWeakGraph lower positive
  rw [annularOmegaCoordinates_right]
  exact field.property

def annularOmegaFromNu (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    annularFluxWeakGraph lower positive →L[ℂ] annularOmegaGraph lower length positive lengthPositive :=
  ((annularOmegaFromNuCoordinates lower length positive lengthPositive).comp
    (annularFluxWeakGraph lower positive).subtypeL).codRestrict
      (annularOmegaGraph lower length positive lengthPositive)
      (annularOmegaFromNu_mem lower length positive lengthPositive)

def annularOmegaNormalizationEquivalence (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    annularOmegaGraph lower length positive lengthPositive ≃L[ℂ] annularFluxWeakGraph lower positive where
  toLinearEquiv :=
    { toLinearMap := (annularOmegaIntoNu lower length positive lengthPositive).toLinearMap
      invFun := annularOmegaFromNu lower length positive lengthPositive
      left_inv := fun field => Subtype.ext (annularOmegaCoordinates_left lower length positive lengthPositive field.val)
      right_inv := fun field => Subtype.ext (annularOmegaCoordinates_right lower length positive lengthPositive field.val) }
  continuous_toFun := (annularOmegaIntoNu lower length positive lengthPositive).continuous
  continuous_invFun := (annularOmegaFromNu lower length positive lengthPositive).continuous

theorem annularOmegaCurve_original (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    annularOmegaCurve lower length positive mode radius =
      Real.sqrt (((mode.val.1 : ℝ) / radius)^2 + ((mode.val.2 : ℝ) / length)^2) := by
  change annularOmega length (max lower radius) mode = _
  rw [max_eq_right inside.1]
  rfl

end Grad.AnnularOmegaGraph
