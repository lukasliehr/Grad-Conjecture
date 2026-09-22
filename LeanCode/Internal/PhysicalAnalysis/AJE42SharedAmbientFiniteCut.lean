import AJE41ExactSourceGraphCut
import AJE34KnownLowBaseAndSharedBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set Filter
open scoped Topology BigOperators
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularKernelL2 Grad.AnnularOrbitGenerators Grad.AnnularLowEnergy
attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule

abbrev StrongCutSupport := Finset (ℤ × ℤ) × (Finset HighAnnularMode × Finset LowAnnularIndex)
def strongCutFilter : Filter StrongCutSupport := atTop ×ˢ (atTop ×ˢ atTop)

structure SourceContraction (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  mapping : E →L[ℝ] E
  bound : ∀ field, ‖mapping field‖ ≤ ‖field‖
def SourceContraction.pair {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (first : SourceContraction E) (second : SourceContraction F) :
    SourceContraction (WithLp 2 (E × F)) :=
  ⟨sourceHilbertPairMap first.mapping second.mapping,
    sourceHilbertPairMap_bound first.mapping second.mapping first.bound second.bound⟩
def SourceContraction.finite {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (mapping : SourceContraction E) : SourceContraction (PiLp 2 (fun _ : Fin n => E)) :=
  ⟨sourceFiniteHilbertMap n mapping.mapping,sourceFiniteHilbertMap_bound n mapping.mapping mapping.bound⟩
def sourceCutContraction {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (support : Finset ι) : SourceContraction (lp (fun _ : ι => E) 2) :=
  ⟨sourceLpCut support,sourceLpCut_bound support⟩
def outerCutContraction (parameters : PhaseParameters) (support : Finset (ℤ × ℤ)) :
    SourceContraction (Grad.ActualBoundaryPrimitives.HighBoundaryPrimitive parameters 0 0) :=
  ⟨outerDatumCut parameters 0 0 support,outerDatumCut_bound parameters 0 0 support⟩
def highKnownCutContraction (parameters : PhaseParameters) (lower : ℝ) (support : StrongCutSupport) :
    SourceContraction (ActualHighKnownAmbient parameters lower 0 0) :=
  ((sourceCutContraction support.1).finite 4 |>.pair ((sourceCutContraction support.1).finite 3)).pair
    (((sourceCutContraction support.1).pair (sourceCutContraction support.1)).pair
      ((outerCutContraction parameters support.1).pair (sourceCutContraction support.2.1)))

def highKnownAmbientCut (parameters : PhaseParameters) (lower : ℝ) (support : StrongCutSupport) :
    ActualHighKnownAmbient parameters lower 0 0 →L[ℝ] ActualHighKnownAmbient parameters lower 0 0 :=
  (highKnownCutContraction parameters lower support).mapping

theorem highKnownAmbientCut_bound (parameters : PhaseParameters) (lower : ℝ)
    (support : StrongCutSupport) (data : ActualHighKnownAmbient parameters lower 0 0) :
    ‖highKnownAmbientCut parameters lower support data‖ ≤ ‖data‖ :=
  (highKnownCutContraction parameters lower support).bound data

def strongCutContraction (parameters : PhaseParameters) (lower : ℝ) (support : StrongCutSupport) :
    SourceContraction (StrongDataAmbient parameters lower 0 0) :=
  (highKnownCutContraction parameters lower support).pair (sourceCutContraction support.2.2)

def strongDataAmbientCut (parameters : PhaseParameters) (lower : ℝ) (support : StrongCutSupport) :
    StrongDataAmbient parameters lower 0 0 →L[ℝ] StrongDataAmbient parameters lower 0 0 :=
  (strongCutContraction parameters lower support).mapping

theorem strongDataAmbientCut_bound (parameters : PhaseParameters) (lower : ℝ)
    (support : StrongCutSupport) (data : StrongDataAmbient parameters lower 0 0) :
    ‖strongDataAmbientCut parameters lower support data‖ ≤ ‖data‖ :=
  (strongCutContraction parameters lower support).bound data

theorem sourceFiniteHilbertMap_tendsto {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (n : ℕ) (filter : Filter ι) (mapping : ι → E →L[ℝ] E) (data : PiLp 2 (fun _ : Fin n => E))
    (limit : ∀ field, Tendsto (fun index => mapping index field) filter (𝓝 field)) :
    Tendsto (fun index => sourceFiniteHilbertMap n (mapping index) data) filter (𝓝 data) := by
  have coordinate : Tendsto (fun index => fun slot => mapping index (data slot)) filter (𝓝 data.ofLp) :=
    tendsto_pi_nhds.mpr (fun slot => limit (data slot))
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => E)).symm.continuous.tendsto data.ofLp).comp coordinate

theorem strongCut_first_tendsto : Tendsto (fun support : StrongCutSupport => support.1) strongCutFilter atTop := tendsto_fst

theorem strongCut_high_tendsto : Tendsto (fun support : StrongCutSupport => support.2.1) strongCutFilter atTop :=
  tendsto_fst.comp tendsto_snd

theorem strongCut_low_tendsto : Tendsto (fun support : StrongCutSupport => support.2.2) strongCutFilter atTop :=
  tendsto_snd.comp tendsto_snd

theorem strongCut_lp_tendsto {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (field : lp (fun _ : ℤ × ℤ => E) 2) :
    Tendsto (fun support : StrongCutSupport => sourceLpCut support.1 field) strongCutFilter (𝓝 field) :=
  (sourceLpCut_tendsto field).comp strongCut_first_tendsto

theorem highKnownAmbientCut_tendsto (parameters : PhaseParameters) (lower : ℝ)
    (data : ActualHighKnownAmbient parameters lower 0 0) :
    Tendsto (fun support => highKnownAmbientCut parameters lower support data) strongCutFilter (𝓝 data) :=
  sourceHilbertPairMap_tendsto _ _ _ data
    (sourceHilbertPairMap_tendsto _ _ _ data.ofLp.1
      (sourceFiniteHilbertMap_tendsto 4 _ _ _ strongCut_lp_tendsto)
      (sourceFiniteHilbertMap_tendsto 3 _ _ _ strongCut_lp_tendsto))
    (sourceHilbertPairMap_tendsto _ _ _ data.ofLp.2
      (sourceHilbertPairMap_tendsto _ _ _ data.ofLp.2.ofLp.1
        (strongCut_lp_tendsto _) (strongCut_lp_tendsto _))
      (sourceHilbertPairMap_tendsto _ _ _ data.ofLp.2.ofLp.2
        ((outerDatumCut_tendsto parameters 0 0 _).comp strongCut_first_tendsto)
        ((sourceLpCut_tendsto _).comp strongCut_high_tendsto)))

theorem strongDataAmbientCut_tendsto (parameters : PhaseParameters) (lower : ℝ)
    (data : StrongDataAmbient parameters lower 0 0) :
    Tendsto (fun support => strongDataAmbientCut parameters lower support data) strongCutFilter (𝓝 data) :=
  sourceHilbertPairMap_tendsto _ _ _ data (highKnownAmbientCut_tendsto parameters lower data.ofLp.1)
    ((sourceLpCut_tendsto data.ofLp.2).comp strongCut_low_tendsto)

end Grad.AnnularStrongOrbit
