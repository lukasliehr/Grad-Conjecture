import AIY12IndependentOriginalStrongCarrier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongData
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarFullSource
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentSource Grad.AnnularHighTilt Grad.AnnularLowEnergy Grad.AnnularCrossMaps
open Grad.ActualBoundaryPrimitives

private theorem inverseRpowSmul {E : Type*} [AddCommGroup E] [Module ℝ E]
    (lower : ℝ) (positive : 0 < lower) (x : E) :
    lower ^ (9 / 4 : ℝ) • (lower ^ (-9 / 4 : ℝ) • x) = x := by
  rw [smul_smul, ← Real.rpow_add positive]
  norm_num

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length) (angular cell : ℕ)

/-- Canonical BF4 datum of any independently prescribed original strong
AK20 datum.  The two source graphs create all three shared source rows;
the single original strengthened g creates the actual g and Rg rows. -/
def originalToStrongAmbient (data : OriginalStrongCarrier parameters lower angular cell) :
    StrongDataAmbient parameters lower angular cell :=
  WithLp.toLp 2
    (WithLp.toLp 2
      (WithLp.toLp 2
        (WithLp.toLp 2 ![
          divisionHighWeight lower positive bounded
            (unweightedSourceF0Bulk parameters lower data.val.ofLp.1.ofLp.1.ofLp.1),
          divisionHighWeight lower positive bounded
            (unweightedSourceRF0Bulk parameters lower data.val.ofLp.1.ofLp.1.ofLp.1),
          divisionHighWeight lower positive bounded
            (unweightedSourceF2Bulk parameters lower data.val.ofLp.1.ofLp.1.ofLp.2),
          divisionHighWeight lower positive bounded data.val.ofLp.1.ofLp.2.ofLp.1],
        WithLp.toLp 2 ![
          divisionHighWeight lower positive bounded
            (originalAngularDecode lower data.val.ofLp.1.ofLp.2.ofLp.2),
          divisionHighWeight lower positive bounded
            (sourceAngularBulk lower data.val.ofLp.1.ofLp.2.ofLp.2), 0]),
      WithLp.toLp 2 (data.val.ofLp.1.ofLp.1,
        WithLp.toLp 2 (data.val.ofLp.2.ofLp.1,
          lower ^ (-9 / 4 : ℝ) • data.val.ofLp.2.ofLp.2.ofLp.1))),
    originalLowIncomingWeightMap parameters lower length positive bounded lengthPositive
      data.val.ofLp.2.ofLp.2.ofLp.2)

theorem originalToStrongAmbient_mem (data : OriginalStrongCarrier parameters lower angular cell) :
    originalToStrongAmbient parameters lower length positive bounded lengthPositive angular cell data ∈
      StrongDataCarrier parameters lower positive bounded angular cell := by
  let result := originalToStrongAmbient parameters lower length positive bounded lengthPositive angular cell data
  have mean := OriginalStrongCarrier.mean_free parameters lower angular cell data
  have compatible : result.ofLp.1 ∈ highKnownCompatibilityCarrier parameters lower positive bounded angular cell := by
    apply (highKnownCompatibilityCarrier_mem_iff parameters lower positive bounded angular cell _).mpr
    apply (weightedGraphCompatibility_iff_rows parameters lower positive bounded angular cell _ _ _).mpr
    exact ⟨rfl,rfl,rfl⟩
  have angularRelation : result ∈ strongAngularCarrier parameters lower angular cell := by
    apply (strongAngularCarrier_mem_iff parameters lower angular cell _).mpr
    intro mode
    change scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
      (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)
      (sourceAngularBulk lower data.val.ofLp.1.ofLp.2.ofLp.2 mode) =
      (Complex.I * (mode.1 : ℂ)) • scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
      (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)
      (originalAngularDecode lower data.val.ofLp.1.ofLp.2.ofLp.2 mode)
    rw [originalAngularDecode_relation, map_smul]
  have f2Mean : meanFreeRow lower (highKnownWeightedF2 parameters lower angular cell result.ofLp.1) =
      highKnownWeightedF2 parameters lower angular cell result.ofLp.1 := by
    apply (meanFreeRow_fixed_iff lower _).mpr
    intro mode zero
    exact divisionHighWeight_zero_mode lower positive bounded _ mode (mean.1 mode zero)
  have fMean : meanFreeRow lower (highKnownWeightedF parameters lower angular cell result.ofLp.1) =
      highKnownWeightedF parameters lower angular cell result.ofLp.1 := by
    apply (meanFreeRow_fixed_iff lower _).mpr
    intro mode zero
    exact divisionHighWeight_zero_mode lower positive bounded _ mode (mean.2.1 mode zero)
  have gMean : meanFreeRow lower (highKnownWeightedG parameters lower angular cell result.ofLp.1) =
      highKnownWeightedG parameters lower angular cell result.ofLp.1 := by
    apply (meanFreeRow_fixed_iff lower _).mpr
    intro mode zero
    apply divisionHighWeight_zero_mode lower positive bounded _ mode
    change (((1 + |(mode.1 : ℝ)|)⁻¹ : ℝ) : ℂ) • data.val.ofLp.1.ofLp.2.ofLp.2 mode = 0
    rw [mean.2.2 mode zero, smul_zero]
  exact ⟨⟨⟨⟨⟨compatible,angularRelation⟩,sub_eq_zero.mpr f2Mean⟩,
    sub_eq_zero.mpr fMean⟩,sub_eq_zero.mpr gMean⟩,rfl⟩

def originalToStrong (data : OriginalStrongCarrier parameters lower angular cell) :
    StrongDataCarrier parameters lower positive bounded angular cell :=
  ⟨originalToStrongAmbient parameters lower length positive bounded lengthPositive angular cell data,
    originalToStrongAmbient_mem parameters lower length positive bounded lengthPositive angular cell data⟩

/-- Every independently prescribed original strong datum is represented,
with the same physical coordinates; no range-surjectivity premise is used. -/
theorem strongToOriginal_originalToStrong (data : OriginalStrongCarrier parameters lower angular cell) :
    strongToOriginal parameters lower angular cell length positive bounded lengthPositive
      (originalToStrong parameters lower length positive bounded lengthPositive angular cell data) = data := by
  apply Subtype.ext
  apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
  apply Prod.ext
  · apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
    apply Prod.ext
    · rfl
    · apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
      apply Prod.ext
      · exact divisionHighUnweight_weight lower positive bounded data.val.ofLp.1.ofLp.2.ofLp.1
      · change strengthenedG lower
          (divisionHighUnweight lower positive bounded
            (divisionHighWeight lower positive bounded (originalAngularDecode lower data.val.ofLp.1.ofLp.2.ofLp.2)))
          (divisionHighUnweight lower positive bounded
            (divisionHighWeight lower positive bounded (sourceAngularBulk lower data.val.ofLp.1.ofLp.2.ofLp.2))) =
          data.val.ofLp.1.ofLp.2.ofLp.2
        rw [divisionHighUnweight_weight, divisionHighUnweight_weight, strengthenedG_originalAngularDecode]
  · apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
    apply Prod.ext
    · rfl
    · apply (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).injective
      apply Prod.ext
      · exact inverseRpowSmul lower positive data.val.ofLp.2.ofLp.2.ofLp.1
      · exact (originalLowIncomingWeightMap_inverse parameters lower length positive bounded lengthPositive
          data.val.ofLp.2.ofLp.2.ofLp.2).2

end Grad.AnnularStrongData
