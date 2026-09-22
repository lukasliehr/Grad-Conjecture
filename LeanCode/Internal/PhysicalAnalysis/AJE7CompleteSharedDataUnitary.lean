import AJE6SharedWeightedAmbientUnitary

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 300000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.SourceCollarFullSource Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularLowEnergy Grad.AnnularLowOrbit

private theorem meanFree_translation (lower : ℝ) (tau : OrbitParameter) (field : DivisionRow 1 lower)
    (fixed : meanFreeRow lower field = field) :
    meanFreeRow lower (orbitLpAction (RadialL2 1 lower) tau field) =
      orbitLpAction (RadialL2 1 lower) tau field := by
  apply (meanFreeRow_fixed_iff lower _).mpr
  intro mode zero
  rw [orbitLpAction_apply,(meanFreeRow_fixed_iff lower _).mp fixed mode zero,smul_zero]

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (angular cell : ℕ)

include positive bounded in
private theorem weightedCompatibility_translation (tau : OrbitParameter)
    (first : HighF0SourceGraph parameters lower) (second : HighF2SourceGraph parameters lower)
    (known : HighKnownSourceBulk lower)
    (compatible : WeightedGraphCompatibility parameters lower (angular + cell) (first,second) known) :
    WeightedGraphCompatibility parameters lower (angular + cell)
      (sourceGraphTranslation 1 lower tau first,sourceGraphTranslation 1 lower tau second)
      (WithLp.toLp 2 (fun slot => orbitLpAction (RadialL2 1 lower) tau (known slot))) := by
  obtain ⟨f0,rf0,f2⟩ := (weightedGraphCompatibility_iff_rows parameters lower positive bounded angular cell first second known).mp compatible
  apply (weightedGraphCompatibility_iff_rows parameters lower positive bounded angular cell _ _ _).mpr
  constructor
  · change orbitLpAction (RadialL2 1 lower) tau (known 0) =
      divisionHighWeight lower positive bounded (unweightedSourceF0Bulk parameters lower (sourceGraphTranslation 1 lower tau first))
    rw [unweightedSourceF0Bulk_translation,divisionHighWeight_translation]
    exact congrArg (orbitLpAction (RadialL2 1 lower) tau) f0
  constructor
  · change orbitLpAction (RadialL2 1 lower) tau (known 1) =
      divisionHighWeight lower positive bounded (unweightedSourceRF0Bulk parameters lower (sourceGraphTranslation 1 lower tau first))
    rw [unweightedSourceRF0Bulk_translation,divisionHighWeight_translation]
    exact congrArg (orbitLpAction (RadialL2 1 lower) tau) rf0
  · change orbitLpAction (RadialL2 1 lower) tau (known 2) =
      divisionHighWeight lower positive bounded (unweightedSourceF2Bulk parameters lower (sourceGraphTranslation 1 lower tau second))
    rw [unweightedSourceF2Bulk_translation,divisionHighWeight_translation]
    exact congrArg (orbitLpAction (RadialL2 1 lower) tau) f2

theorem strongDataAmbientTranslation_mem (tau : OrbitParameter)
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    strongDataAmbientTranslation parameters lower angular cell tau data.val ∈
      StrongDataCarrier parameters lower positive bounded angular cell := by
  let result := strongDataAmbientTranslation parameters lower angular cell tau data.val
  have compatible : result.ofLp.1 ∈ highKnownCompatibilityCarrier parameters lower positive bounded angular cell := by
    apply (highKnownCompatibilityCarrier_mem_iff parameters lower positive bounded angular cell _).mpr
    exact weightedCompatibility_translation parameters lower positive bounded angular cell tau
      data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.1 data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2
      data.val.ofLp.1.ofLp.1.ofLp.1 (StrongDataCarrier.compatibility parameters lower positive bounded angular cell data)
  have angularRelation : result ∈ strongAngularCarrier parameters lower angular cell := by
    apply (strongAngularCarrier_mem_iff parameters lower angular cell _).mpr
    intro mode
    change orbitCharacter tau mode • (data.val.ofLp.1.ofLp.1.ofLp.2 1 mode) =
      (Complex.I * (mode.1 : ℂ)) • (orbitCharacter tau mode • (data.val.ofLp.1.ofLp.1.ofLp.2 0 mode))
    have relation := StrongDataCarrier.angular_relation parameters lower positive bounded angular cell data mode
    change data.val.ofLp.1.ofLp.1.ofLp.2 1 mode =
      (Complex.I * (mode.1 : ℂ)) • (data.val.ofLp.1.ofLp.1.ofLp.2 0 mode) at relation
    rw [relation]
    exact smul_comm _ _ _
  have mean := StrongDataCarrier.mean_free parameters lower positive bounded angular cell data
  have f2Mean : meanFreeRow lower (highKnownWeightedF2 parameters lower angular cell result.ofLp.1) =
      highKnownWeightedF2 parameters lower angular cell result.ofLp.1 :=
    meanFree_translation lower tau _ mean.1
  have fMean : meanFreeRow lower (highKnownWeightedF parameters lower angular cell result.ofLp.1) =
      highKnownWeightedF parameters lower angular cell result.ofLp.1 :=
    meanFree_translation lower tau _ mean.2.1
  have gMean : meanFreeRow lower (highKnownWeightedG parameters lower angular cell result.ofLp.1) =
      highKnownWeightedG parameters lower angular cell result.ofLp.1 :=
    meanFree_translation lower tau _ mean.2.2
  have spare : highKnownWeightedRqv parameters lower angular cell result.ofLp.1 = 0 := by
    change orbitLpAction (RadialL2 1 lower) tau
      (highKnownWeightedRqv parameters lower angular cell data.val.ofLp.1) = 0
    rw [StrongDataCarrier.spare_zero parameters lower positive bounded angular cell data,map_zero]
  exact ⟨⟨⟨⟨⟨compatible,angularRelation⟩,sub_eq_zero.mpr f2Mean⟩,
    sub_eq_zero.mpr fMean⟩,sub_eq_zero.mpr gMean⟩,spare⟩

/-- Genuine simultaneous source and incoming-data translation on the
single complete BF4 carrier, with unchanged graph and analytic norms. -/
def strongDataTranslation (tau : OrbitParameter) :
    StrongDataCarrier parameters lower positive bounded angular cell →L[ℝ]
      StrongDataCarrier parameters lower positive bounded angular cell :=
  ((strongDataAmbientTranslation parameters lower angular cell tau).toContinuousLinearEquiv.toContinuousLinearMap.comp
    (StrongDataCarrier parameters lower positive bounded angular cell).subtypeL).codRestrict
    (StrongDataCarrier parameters lower positive bounded angular cell)
    (strongDataAmbientTranslation_mem parameters lower positive bounded angular cell tau)

theorem strongDataTranslation_val (tau : OrbitParameter)
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    (strongDataTranslation parameters lower positive bounded angular cell tau data).val =
      strongDataAmbientTranslation parameters lower angular cell tau data.val := rfl

theorem strongDataTranslation_inverse (tau : OrbitParameter)
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    strongDataTranslation parameters lower positive bounded angular cell tau
      (strongDataTranslation parameters lower positive bounded angular cell (-tau) data) = data := by
  apply Subtype.ext
  exact (strongDataAmbientTranslation parameters lower angular cell tau).apply_symm_apply data.val

theorem strongDataTranslation_norm (tau : OrbitParameter)
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    ‖strongDataTranslation parameters lower positive bounded angular cell tau data‖ = ‖data‖ :=
  (strongDataAmbientTranslation parameters lower angular cell tau).norm_map data.val

def strongDataTranslationEquivalence (tau : OrbitParameter) :
    StrongDataCarrier parameters lower positive bounded angular cell ≃ₗᵢ[ℝ]
      StrongDataCarrier parameters lower positive bounded angular cell where
  toLinearEquiv :=
    { (strongDataTranslation parameters lower positive bounded angular cell tau).toLinearMap with
      invFun := strongDataTranslation parameters lower positive bounded angular cell (-tau)
      left_inv := by
        intro data
        change strongDataTranslation parameters lower positive bounded angular cell (-tau)
          (strongDataTranslation parameters lower positive bounded angular cell tau data) = data
        simpa only [neg_neg] using strongDataTranslation_inverse parameters lower positive bounded angular cell (-tau) data
      right_inv := strongDataTranslation_inverse parameters lower positive bounded angular cell tau }
  norm_map' := strongDataTranslation_norm parameters lower positive bounded angular cell tau

end Grad.AnnularStrongOrbit
