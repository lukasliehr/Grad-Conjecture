import AAQ11ExactPhysicalTraceEstimate

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularFluxTrace
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

def annularFluxPhysicalQSection (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (data : annularFluxWeakGraph lower positive)
    (mode : HighAnnularMode) : RadialContinuousSection 1 lower :=
  radialSectionScalar lower (annularInversePhase parameters mode.val.2)
    (annularFluxSection lower positive bounded data mode)

def annularFluxPhysicalPSection (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (data : annularFluxWeakGraph lower positive)
    (mode : HighAnnularMode) : RadialContinuousSection 1 lower :=
  (-(annularDSymbol mode)⁻¹) • annularFluxPhysicalQSection parameters lower positive bounded data mode

theorem annularFluxPhysicalQSection_bulk (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (data : annularFluxWeakGraph lower positive)
    (mode : HighAnnularMode) :
    radialSectionL2 1 lower positive bounded.le (annularFluxPhysicalQSection parameters lower positive bounded data mode) =
      collarScalar 1 lower (annularInversePhase parameters mode.val.2)
        (annularFluxGraphValue lower positive mode data.val) := by
  unfold annularFluxPhysicalQSection
  rw [radialSectionL2_scalar, annularFluxSection_bulk]

theorem annularFluxPhysicalPSection_D (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (data : annularFluxWeakGraph lower positive)
    (mode : HighAnnularMode) (radius : Icc lower (1 : ℝ)) :
    annularDSymbol mode • annularFluxPhysicalPSection parameters lower positive bounded data mode radius =
      -annularFluxPhysicalQSection parameters lower positive bounded data mode radius := by
  change annularDSymbol mode • (-(annularDSymbol mode)⁻¹ • (_ : ComplexEuclidean 1)) = _
  rw [smul_smul, mul_neg, mul_inv_cancel₀ (annularDSymbol_ne_zero mode), neg_smul, one_smul]

def annularPhysicalNegativeTraceWeight (parameters : PhaseParameters) (lower : ℝ)
    (endpoint : Fin 2) (mode : HighAnnularMode) : ℝ :=
  (Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2))⁻¹ *
    Real.exp (radialPhase parameters (radialEndpointRadius lower endpoint) mode.val.2)

theorem annularFluxPhysicalQ_normalization (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (endpoint : Fin 2)
    (data : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) :
    annularPhysicalNegativeTraceWeight parameters lower endpoint mode •
      annularFluxPhysicalQSection parameters lower positive bounded data mode
        ⟨radialEndpointRadius lower endpoint, radialEndpointRadius_mem lower bounded.le endpoint⟩ =
      annularFluxTrace lower positive bounded endpoint data mode := by
  rw [annularFluxTrace_apply]
  change ((Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2))⁻¹ *
      Real.exp (radialPhase parameters (radialEndpointRadius lower endpoint) mode.val.2)) •
    (Real.exp (-radialPhase parameters (radialEndpointRadius lower endpoint) mode.val.2) • (_ : ComplexEuclidean 1)) = _
  rw [smul_smul, mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- P_e is normalized by nu^-1/2 e^Phi D. Thus its endpoint map is the
negative of the q endpoint map and has exactly the same norm. -/
def annularFluxNaturalPTrace (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (endpoint : Fin 2) :
    annularFluxWeakGraph lower positive →L[ℂ] AnnularBoundary := -annularFluxTrace lower positive bounded endpoint

theorem annularFluxNaturalPTrace_apply (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (endpoint : Fin 2)
    (data : annularFluxWeakGraph lower positive) (mode : HighAnnularMode) :
    annularFluxNaturalPTrace lower positive bounded endpoint data mode =
      annularPhysicalNegativeTraceWeight parameters lower endpoint mode •
        (annularDSymbol mode • annularFluxPhysicalPSection parameters lower positive bounded data mode
          ⟨radialEndpointRadius lower endpoint, radialEndpointRadius_mem lower bounded.le endpoint⟩) := by
  rw [annularFluxPhysicalPSection_D, smul_neg, annularFluxPhysicalQ_normalization]
  rfl

theorem annularFluxNaturalPTrace_norm (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (endpoint : Fin 2) (data : annularFluxWeakGraph lower positive) :
    ‖annularFluxNaturalPTrace lower positive bounded endpoint data‖ = ‖annularFluxTrace lower positive bounded endpoint data‖ :=
  norm_neg _

end Grad.AnnularFluxTrace
