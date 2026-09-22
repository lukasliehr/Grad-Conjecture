import AJE42SharedAmbientFiniteCut

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set Filter
open scoped Topology BigOperators
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.SourceCollarFullSource Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularKernelL2 Grad.AnnularOrbitGenerators Grad.AnnularLowEnergy
attribute [local instance] knownAmbientNormed knownAmbientSeminormed knownAmbientRealNormed knownAmbientRealModule
  strongCarrierNormed strongCarrierSeminormed strongCarrierRealNormed strongCarrierRealModule

private theorem meanFree_cut (lower : ℝ) (support : Finset (ℤ × ℤ)) (field : DivisionRow 1 lower)
    (fixed : meanFreeRow lower field = field) : meanFreeRow lower (sourceLpCut support field) = sourceLpCut support field := by
  apply (meanFreeRow_fixed_iff lower _).mpr
  intro mode zero
  rw [sourceLpCut_apply,(meanFreeRow_fixed_iff lower _).mp fixed mode zero]
  split_ifs <;> rfl

private theorem weightedCompatibility_cut (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (support : Finset (ℤ × ℤ))
    (first : HighF0SourceGraph parameters lower) (second : HighF2SourceGraph parameters lower)
    (known : HighKnownSourceBulk lower)
    (compatible : WeightedGraphCompatibility parameters lower 0 (first,second) known) :
    WeightedGraphCompatibility parameters lower 0 (sourceLpCut support first,sourceLpCut support second)
      (sourceFiniteHilbertMap 4 (sourceLpCut support) known) := by
  obtain ⟨f0,rf0,f2⟩ := (weightedGraphCompatibility_iff_rows parameters lower positive bounded 0 0 first second known).mp compatible
  apply (weightedGraphCompatibility_iff_rows parameters lower positive bounded 0 0 _ _ _).mpr
  constructor
  · change sourceLpCut support (known 0) = divisionHighWeight lower positive bounded
      (unweightedSourceF0Bulk parameters lower (sourceLpCut support first))
    rw [unweightedSourceF0Bulk_cut,divisionHighWeight_cut]
    exact congrArg (sourceLpCut support) f0
  constructor
  · change sourceLpCut support (known 1) = divisionHighWeight lower positive bounded
      (unweightedSourceRF0Bulk parameters lower (sourceLpCut support first))
    rw [unweightedSourceRF0Bulk_cut,divisionHighWeight_cut]
    exact congrArg (sourceLpCut support) rf0
  · change sourceLpCut support (known 2) = divisionHighWeight lower positive bounded
      (unweightedSourceF2Bulk parameters lower (sourceLpCut support second))
    rw [unweightedSourceF2Bulk_cut,divisionHighWeight_cut]
    exact congrArg (sourceLpCut support) f2

def SourceContraction.restrict {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (mapping : SourceContraction E) (graph : Submodule ℝ E)
    (preserves : ∀ field : graph, mapping.mapping field.val ∈ graph) : SourceContraction graph :=
  ⟨(mapping.mapping.comp graph.subtypeL).codRestrict graph preserves,fun field => mapping.bound field.val⟩

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)

theorem strongDataAmbientCut_mem (support : StrongCutSupport)
    (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    strongDataAmbientCut parameters lower support data.val ∈ StrongDataCarrier parameters lower positive bounded 0 0 := by
  let result := strongDataAmbientCut parameters lower support data.val
  have compatible : result.ofLp.1 ∈ highKnownCompatibilityCarrier parameters lower positive bounded 0 0 := by
    apply (highKnownCompatibilityCarrier_mem_iff parameters lower positive bounded 0 0 _).mpr
    exact weightedCompatibility_cut parameters lower positive bounded support.1
      data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.1 data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2
      data.val.ofLp.1.ofLp.1.ofLp.1 (StrongDataCarrier.compatibility parameters lower positive bounded 0 0 data)
  have angularRelation : result ∈ strongAngularCarrier parameters lower 0 0 := by
    apply (strongAngularCarrier_mem_iff parameters lower 0 0 _).mpr
    intro mode
    change sourceLpCut support.1 (data.val.ofLp.1.ofLp.1.ofLp.2 1) mode =
      (Complex.I * (mode.1 : ℂ)) • sourceLpCut support.1 (data.val.ofLp.1.ofLp.1.ofLp.2 0) mode
    rw [sourceLpCut_apply,sourceLpCut_apply]
    by_cases inside : mode ∈ support.1
    · simp only [inside,if_true]
      exact StrongDataCarrier.angular_relation parameters lower positive bounded 0 0 data mode
    · simp only [inside,if_false,smul_zero]
  have mean := StrongDataCarrier.mean_free parameters lower positive bounded 0 0 data
  have f2Mean : meanFreeRow lower (highKnownWeightedF2 parameters lower 0 0 result.ofLp.1) = highKnownWeightedF2 parameters lower 0 0 result.ofLp.1 :=
    meanFree_cut lower support.1 _ mean.1
  have fMean : meanFreeRow lower (highKnownWeightedF parameters lower 0 0 result.ofLp.1) = highKnownWeightedF parameters lower 0 0 result.ofLp.1 :=
    meanFree_cut lower support.1 _ mean.2.1
  have gMean : meanFreeRow lower (highKnownWeightedG parameters lower 0 0 result.ofLp.1) = highKnownWeightedG parameters lower 0 0 result.ofLp.1 :=
    meanFree_cut lower support.1 _ mean.2.2
  have spare : highKnownWeightedRqv parameters lower 0 0 result.ofLp.1 = 0 := by
    change sourceLpCut support.1 (highKnownWeightedRqv parameters lower 0 0 data.val.ofLp.1) = 0
    rw [StrongDataCarrier.spare_zero parameters lower positive bounded 0 0 data,map_zero]
  exact ⟨⟨⟨⟨⟨compatible,angularRelation⟩,sub_eq_zero.mpr f2Mean⟩,sub_eq_zero.mpr fMean⟩,sub_eq_zero.mpr gMean⟩,spare⟩

def strongDataCutContraction (support : StrongCutSupport) :
    SourceContraction (StrongDataCarrier parameters lower positive bounded 0 0) :=
  (strongCutContraction parameters lower support).restrict
    (StrongDataCarrier parameters lower positive bounded 0 0)
    (strongDataAmbientCut_mem parameters lower positive bounded support)

/-- Literal Fourier cut on the SAME complete shared strong carrier. -/
def strongDataCut (support : StrongCutSupport) :
    StrongDataCarrier parameters lower positive bounded 0 0 →L[ℝ] StrongDataCarrier parameters lower positive bounded 0 0 :=
  (strongDataCutContraction parameters lower positive bounded support).mapping

theorem strongDataCut_val (support : StrongCutSupport) (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    (strongDataCut parameters lower positive bounded support data).val = strongDataAmbientCut parameters lower support data.val := rfl

theorem strongDataCut_bound (support : StrongCutSupport) (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    ‖strongDataCut parameters lower positive bounded support data‖ ≤ ‖data‖ :=
  (strongDataCutContraction parameters lower positive bounded support).bound data

theorem strongDataCut_tendsto (data : StrongDataCarrier parameters lower positive bounded 0 0) :
    Tendsto (fun support => strongDataCut parameters lower positive bounded support data) strongCutFilter (𝓝 data) :=
  tendsto_subtype_rng.mpr (strongDataAmbientCut_tendsto parameters lower data.val)

end Grad.AnnularStrongOrbit
