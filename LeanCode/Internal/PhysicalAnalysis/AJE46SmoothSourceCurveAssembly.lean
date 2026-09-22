import AJE45FiniteSourceGraphOrbitSmoothness
import AJE42SharedAmbientFiniteCut
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open scoped ContDiff
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularKernelL2 Grad.AnnularOrbitGenerators Grad.AnnularLowEnergy Grad.AnnularLowOrbit

/-- Smoothness is stored before assembling the actual large Hilbert product. -/
structure SourceSmoothCurve (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  curve : ℝ → E
  smooth : ContDiff ℝ ∞ curve

def SourceSmoothCurve.pair {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (first : SourceSmoothCurve E) (second : SourceSmoothCurve F) :
    SourceSmoothCurve (WithLp 2 (E × F)) :=
  ⟨fun time => WithLp.toLp 2 (first.curve time,second.curve time),
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.contDiff.comp (first.smooth.prodMk second.smooth)⟩

def SourceSmoothCurve.finite {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (curves : Fin n → SourceSmoothCurve E) : SourceSmoothCurve (PiLp 2 (fun _ : Fin n => E)) :=
  ⟨fun time => WithLp.toLp 2 (fun slot => (curves slot).curve time),
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => E)).symm.contDiff.comp
      (contDiff_pi.mpr (fun slot => (curves slot).smooth))⟩

def finiteComplexSourceCurve {ι V : Type*} [DecidableEq ι]
    [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedSpace ℝ V] [IsScalarTower ℝ ℂ V]
    (frequency : ι → ℤ) (field : lp (fun _ : ι => V) 2)
    (curve : ℝ → lp (fun _ : ι => V) 2)
    (character : ∀ time index, curve time index = cellExponential (frequency index) time • field index)
    (support : Finset ι) (finite : ∀ index, index ∉ support → field index = 0) :
    SourceSmoothCurve (lp (fun _ : ι => V) 2) :=
  ⟨curve,finiteLpCharacterOrbit_contDiff frequency field curve character support finite⟩

section Closed
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (graph : Submodule ℝ E) [graph.HasOrthogonalProjection]

theorem sourceClosedGraph_contDiff (curve : ℝ → graph)
    (smooth : ContDiff ℝ ∞ (fun time => (curve time).val)) : ContDiff ℝ ∞ curve := by
  have composed := graph.orthogonalProjectionOnto.contDiff.comp smooth
  simpa only [Function.comp_def,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self] using composed
end Closed

section ComplexClosed
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    (graph : Submodule ℂ E) [graph.HasOrthogonalProjection]

theorem sourceComplexClosedGraph_contDiff (curve : ℝ → graph)
    (smooth : ContDiff ℝ ∞ (fun time => (curve time).val)) : ContDiff ℝ ∞ curve := by
  have composed := (graph.orthogonalProjectionOnto.restrictScalars ℝ).contDiff.comp smooth
  have same : (fun time => (graph.orthogonalProjectionOnto.restrictScalars ℝ) (curve time).val) = curve := by
    funext time
    exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (curve time)
  exact same ▸ composed
end ComplexClosed

/-- Real Hilbert structure uses the unchanged norm of every coordinate. -/
local instance sourceRadialRealInner (lower : ℝ) : InnerProductSpace ℝ (RadialL2 1 lower) :=
  InnerProductSpace.rclikeToReal ℂ (RadialL2 1 lower)
local instance sourceGraphRealInner (lower : ℝ) : InnerProductSpace ℝ (WeightedRadialH1 1 lower) := by
  letI : InnerProductSpace ℝ (WeightedRadialAmbient 1 lower) := inferInstance
  exact Submodule.innerProductSpace (WeightedRadialH1 1 lower)
local instance sourceKnownBulkRealInner (lower : ℝ) : InnerProductSpace ℝ (HighKnownBulkHilbert lower) :=
  InnerProductSpace.rclikeToReal ℂ (HighKnownBulkHilbert lower)
local instance sourceKnownBoundaryRealInner (parameters : PhaseParameters) :
    InnerProductSpace ℝ (HighKnownBoundaryHilbert parameters 0 0) :=
  InnerProductSpace.rclikeToReal ℂ (HighKnownBoundaryHilbert parameters 0 0)
local instance sourceKnownGraphRealInner (parameters : PhaseParameters) (lower : ℝ) :
    InnerProductSpace ℝ (HighKnownGraphHilbert parameters lower) := inferInstance
local instance sourceKnownGraphBoundaryRealInner (parameters : PhaseParameters) (lower : ℝ) :
    InnerProductSpace ℝ (HighKnownGraphBoundaryHilbert parameters lower 0 0) := inferInstance
local instance sourceKnownAmbientRealInner (parameters : PhaseParameters) (lower : ℝ) :
    InnerProductSpace ℝ (ActualHighKnownAmbient parameters lower 0 0) := inferInstance
local instance sourceLowBoundaryRealInner : InnerProductSpace ℝ LowEnergyBoundary :=
  InnerProductSpace.rclikeToReal ℂ LowEnergyBoundary
local instance sourceStrongAmbientRealInner (parameters : PhaseParameters) (lower : ℝ) :
    InnerProductSpace ℝ (StrongDataAmbient parameters lower 0 0) := inferInstance

end Grad.AnnularStrongOrbit
