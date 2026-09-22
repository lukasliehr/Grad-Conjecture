import AIY10OriginalStrongNormComparison

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongData
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentSource Grad.AnnularHighTilt Grad.AnnularLowEnergy Grad.AnnularCrossMaps
open Grad.ActualBoundaryPrimitives

private theorem finishBF5Forward {S M R C a b c d e f g h i j k : ℝ}
    (total : S ≤ a + b + c + d + e + f + g + h + i + j + k)
    (ha : a ≤ R * M) (hb : b ≤ R * M) (hc : c ≤ R * M)
    (hd : d ≤ R * M) (he : e ≤ R * M) (hf : f ≤ R * M)
    (hg : g ≤ R * M) (hh : h ≤ R * M) (hi : i ≤ R * M)
    (hj : j ≤ R * M) (hk : k ≤ C * R * M) : S ≤ ((10 + C) * R) * M := by
  linarith only [total,ha,hb,hc,hd,he,hf,hg,hh,hi,hj,hk]

private theorem normScaleInverse {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R t : ℝ) (nonnegative : 0 ≤ t) (inverse : R * t = 1) (x : E) :
    R * ‖t • x‖ = ‖x‖ := by
  rw [norm_smul, Real.norm_of_nonneg nonnegative, ← mul_assoc, inverse, one_mul]

variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length) (angular cell : ℕ)

private theorem originalStrongForwardAux
    (data : StrongDataCarrier parameters lower positive bounded angular cell)
    (original : OriginalStrongAmbient parameters lower angular cell)
    (originalGraphs : original.ofLp.1.ofLp.1 = data.val.ofLp.1.ofLp.2.ofLp.1)
    (originalF : original.ofLp.1.ofLp.2.ofLp.1 = divisionHighUnweight lower positive bounded
      (data.val.ofLp.1.ofLp.1.ofLp.1 3))
    (originalG : original.ofLp.1.ofLp.2.ofLp.2 = strengthenedG lower
      (divisionHighUnweight lower positive bounded (data.val.ofLp.1.ofLp.1.ofLp.2 0))
      (divisionHighUnweight lower positive bounded (data.val.ofLp.1.ofLp.1.ofLp.2 1)))
    (originalOuter : original.ofLp.2.ofLp.1 = data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.1)
    (originalHigh : original.ofLp.2.ofLp.2.ofLp.1 = lower ^ (9 / 4 : ℝ) • data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.2)
    (originalLow : original.ofLp.2.ofLp.2.ofLp.2 =
      originalLowIncomingUnweightMap parameters lower length positive bounded lengthPositive data.val.ofLp.2) :
    ‖data‖ ≤ ((10 + originalLowIncomingConstant parameters length) * lower ^ (-9 / 4 : ℝ)) * ‖original‖ := by
  let R := lower ^ (-9 / 4 : ℝ)
  have Rpositive : 0 < R := Real.rpow_pos_of_pos positive _
  have Rone : 1 ≤ R := Real.one_le_rpow_of_pos_of_le_one_of_nonpos positive bounded (by norm_num)
  have powerInverse : R * lower ^ (9 / 4 : ℝ) = 1 := by
    dsimp only [R]
    rw [← Real.rpow_add positive]
    norm_num
  have rowBound (field : DivisionRow 1 lower) :
      ‖divisionHighWeight lower positive bounded field‖ ≤ R * ‖field‖ := by
    simpa only [R, highTiltExponent, neg_div] using divisionHighWeight_bound lower positive bounded field
  obtain ⟨f0Original,f2Original,fOriginal,gOriginal,outerOriginal,highOriginal,lowOriginal⟩ :=
    originalStrongAmbient_component_bounds parameters lower angular cell original
  rw [originalGraphs] at f0Original f2Original
  rw [originalF] at fOriginal
  rw [originalG] at gOriginal
  rw [originalOuter] at outerOriginal
  rw [originalLow] at lowOriginal
  have source := (weightedGraphCompatibility_iff_rows parameters lower positive bounded angular cell
    data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.1 data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2
    data.val.ofLp.1.ofLp.1.ofLp.1).mp
      (StrongDataCarrier.compatibility parameters lower positive bounded angular cell data)
  have f0Graph : ‖data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.1‖ ≤ ‖original‖ := f0Original
  have f2Graph : ‖data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2‖ ≤ ‖original‖ := f2Original
  have f0 : ‖data.val.ofLp.1.ofLp.1.ofLp.1 0‖ ≤ R * ‖original‖ := by
    rw [source.1]
    exact (rowBound _).trans (mul_le_mul_of_nonneg_left
      ((unweightedSourceF0Bulk_bound parameters lower _).trans f0Graph) Rpositive.le)
  have rf0 : ‖data.val.ofLp.1.ofLp.1.ofLp.1 1‖ ≤ R * ‖original‖ := by
    rw [source.2.1]
    exact (rowBound _).trans (mul_le_mul_of_nonneg_left
      ((unweightedSourceRF0Bulk_bound parameters lower _).trans f0Graph) Rpositive.le)
  have f2 : ‖data.val.ofLp.1.ofLp.1.ofLp.1 2‖ ≤ R * ‖original‖ := by
    rw [source.2.2]
    exact (rowBound _).trans (mul_le_mul_of_nonneg_left
      ((unweightedSourceF2Bulk_bound parameters lower _).trans f2Graph) Rpositive.le)
  have f : ‖data.val.ofLp.1.ofLp.1.ofLp.1 3‖ ≤ R * ‖original‖ := by
    have result := (rowBound (divisionHighUnweight lower positive bounded
      (data.val.ofLp.1.ofLp.1.ofLp.1 3))).trans
      (mul_le_mul_of_nonneg_left fOriginal Rpositive.le)
    rw [divisionHighWeight_unweight] at result
    exact result
  have angularRelation := divisionHighUnweight_angular lower positive bounded
    (data.val.ofLp.1.ofLp.1.ofLp.2 0) (data.val.ofLp.1.ofLp.1.ofLp.2 1)
    (StrongDataCarrier.angular_relation parameters lower positive bounded angular cell data)
  have gUnweighted := strengthenedG_component_bounds lower
    (divisionHighUnweight lower positive bounded (data.val.ofLp.1.ofLp.1.ofLp.2 0))
    (divisionHighUnweight lower positive bounded (data.val.ofLp.1.ofLp.1.ofLp.2 1)) angularRelation
  have g : ‖data.val.ofLp.1.ofLp.1.ofLp.2 0‖ ≤ R * ‖original‖ := by
    have result := (rowBound (divisionHighUnweight lower positive bounded
      (data.val.ofLp.1.ofLp.1.ofLp.2 0))).trans
      (mul_le_mul_of_nonneg_left (gUnweighted.1.trans gOriginal) Rpositive.le)
    rw [divisionHighWeight_unweight] at result
    exact result
  have rg : ‖data.val.ofLp.1.ofLp.1.ofLp.2 1‖ ≤ R * ‖original‖ := by
    have result := (rowBound (divisionHighUnweight lower positive bounded
      (data.val.ofLp.1.ofLp.1.ofLp.2 1))).trans
      (mul_le_mul_of_nonneg_left (gUnweighted.2.trans gOriginal) Rpositive.le)
    rw [divisionHighWeight_unweight] at result
    exact result
  have scaleOriginal : ‖original‖ ≤ R * ‖original‖ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right Rone (norm_nonneg original)
  have f0GraphScaled := f0Graph.trans scaleOriginal
  have f2GraphScaled := f2Graph.trans scaleOriginal
  have outer : ‖data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.1‖ ≤ R * ‖original‖ :=
    outerOriginal.trans scaleOriginal
  have high : ‖data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.2‖ ≤ R * ‖original‖ := by
    have equality : R * ‖original.ofLp.2.ofLp.2.ofLp.1‖ =
        ‖data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.2‖ := by
      rw [originalHigh]
      exact normScaleInverse R (lower ^ (9 / 4 : ℝ))
        (Real.rpow_pos_of_pos positive _).le powerInverse _
    rw [← equality]
    exact mul_le_mul_of_nonneg_left highOriginal Rpositive.le
  have low : ‖data.val.ofLp.2‖ ≤ originalLowIncomingConstant parameters length * R * ‖original‖ := by
    have result := originalLowIncomingWeightMap_bound parameters lower length positive bounded lengthPositive
      (originalLowIncomingUnweightMap parameters lower length positive bounded lengthPositive data.val.ofLp.2)
    rw [(originalLowIncomingWeightMap_inverse parameters lower length positive bounded lengthPositive data.val.ofLp.2).1] at result
    apply result.trans
    apply mul_le_mul_of_nonneg_left lowOriginal
    have := lowOuterFrequencyConstant_two_le length lengthPositive
    have : 1 ≤ lowBalanceConstant length parameters.gamma := le_max_left _ _
    unfold originalLowIncomingConstant
    positivity
  have total := StrongDataCarrier.norm_le_sum parameters lower positive bounded angular cell data
  change ‖data‖ ≤ ((10 + originalLowIncomingConstant parameters length) * R) * ‖original‖
  exact finishBF5Forward total f0 rf0 f2 f g rg f0GraphScaled f2GraphScaled outer high low


/-- Forward BF5 comparison for the exact original seven datum norm. The only
collar cost is lower^(-9/4); the constant is fixed before lower and the
physical state, and no new angular order is required. -/
theorem strongOriginalCoordinateMap_lowerBound
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    ‖data‖ ≤ ((10 + originalLowIncomingConstant parameters length) * lower ^ (-9 / 4 : ℝ)) *
      ‖strongOriginalCoordinateMap parameters lower length positive bounded lengthPositive angular cell data‖ := by
  have coordinates := strongOriginalCoordinateMap_exact parameters lower length positive bounded lengthPositive angular cell data
  exact originalStrongForwardAux parameters lower length positive bounded lengthPositive angular cell data _
    coordinates.1 coordinates.2.1 coordinates.2.2.1 coordinates.2.2.2.1
    coordinates.2.2.2.2.1 coordinates.2.2.2.2.2

end Grad.AnnularStrongData
