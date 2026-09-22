import AKN32SameFullG3Grades
import AKL4ExactOriginalExhaustionSolve

noncomputable section
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.SourceCollarFullSource Grad.SourceCollarCoefficients Grad.AnnularCurrentSource
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.ConstrainedGrades
open Grad.SourceCollarBulk Grad.AnnularStrongData Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularExhaustionEstimate Grad.AnnularStrongOrbit Grad.AnnularVariational Grad.AnnularHighTilt
attribute [local instance] Grad.AnnularStrongOrbit.knownAmbientNormed Grad.AnnularStrongOrbit.knownAmbientSeminormed Grad.AnnularStrongOrbit.knownAmbientRealNormed Grad.AnnularStrongOrbit.knownAmbientRealModule
  Grad.AnnularStrongOrbit.strongCarrierNormed Grad.AnnularStrongOrbit.strongCarrierSeminormed Grad.AnnularStrongOrbit.strongCarrierRealNormed Grad.AnnularStrongOrbit.strongCarrierRealModule

theorem divisionHighWeight_real_family (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (high low : DivisionRow 1 lower) (coefficient : ℤ × ℤ → ℝ)
    (same : ∀ mode, high mode = coefficient mode • low mode) (mode : ℤ × ℤ) :
    divisionHighWeight lower positive bounded high mode =
      coefficient mode • divisionHighWeight lower positive bounded low mode := by
  rw [divisionHighWeight_mode, divisionHighWeight_mode, same]
  exact (scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
    (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)).map_smul_of_tower _ _

private theorem radialCoordinate_real_scale (lower : ℝ) (a b : ℝ)
    (high low : WeightedRadialH1 1 lower) (same : high = a • low) :
    b • weightedRadialCoordinate 1 lower 0 high = a • (b • weightedRadialCoordinate 1 lower 0 low) := by
  rw [same, map_smul]
  exact smul_comm _ _ _

private theorem radialCoordinate_complex_scale (lower : ℝ) (a : ℝ) (b : ℂ)
    (high low : WeightedRadialH1 1 lower) (same : high = a • low) :
    b • weightedRadialCoordinate 1 lower 0 high = a • (b • weightedRadialCoordinate 1 lower 0 low) := by
  rw [same, map_smul]
  exact smul_comm _ _ _

/-- Exact BF reconstruction preserves an insertion on all four original
source blocks. The two independent boundary tuples are zero. -/
theorem originalWeightedDatum_inserted_sources (parameters : PhaseParameters) (lower L : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < L) (grade : ℕ)
    (low high : OriginalStrongCarrier parameters lower 0 0)
    (first : ∀ mode, high.val.ofLp.1.ofLp.1.ofLp.1 mode = Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 ^ grade • low.val.ofLp.1.ofLp.1.ofLp.1 mode)
    (second : ∀ mode, high.val.ofLp.1.ofLp.1.ofLp.2 mode = Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 ^ grade • low.val.ofLp.1.ofLp.1.ofLp.2 mode)
    (third : ∀ mode, high.val.ofLp.1.ofLp.2.ofLp.1 mode = Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 ^ grade • low.val.ofLp.1.ofLp.2.ofLp.1 mode)
    (fourth : ∀ mode, high.val.ofLp.1.ofLp.2.ofLp.2 mode = Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 ^ grade • low.val.ofLp.1.ofLp.2.ofLp.2 mode)
    (lowBoundary : low.val.ofLp.2 = 0) (highBoundary : high.val.ofLp.2 = 0) :
    StrongInsertedGrade parameters lower positive bounded grade
      (originalWeightedDatum parameters lower L positive bounded lengthPositive low)
      (originalWeightedDatum parameters lower L positive bounded lengthPositive high) := by
  have f0 (mode : ℤ × ℤ) : unweightedSourceF0Bulk parameters lower high.val.ofLp.1.ofLp.1.ofLp.1 mode =
      Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 ^ grade • unweightedSourceF0Bulk parameters lower low.val.ofLp.1.ofLp.1.ofLp.1 mode := by
    change sourceGradeRatio 0 0 1 0 mode • weightedRadialCoordinate 1 lower 0 (high.val.ofLp.1.ofLp.1.ofLp.1 mode) =
      _ • (sourceGradeRatio 0 0 1 0 mode • weightedRadialCoordinate 1 lower 0 (low.val.ofLp.1.ofLp.1.ofLp.1 mode))
    exact radialCoordinate_real_scale lower _ _ _ _ (first mode)
  have rf0 (mode : ℤ × ℤ) : unweightedSourceRF0Bulk parameters lower high.val.ofLp.1.ofLp.1.ofLp.1 mode =
      Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 ^ grade • unweightedSourceRF0Bulk parameters lower low.val.ofLp.1.ofLp.1.ofLp.1 mode := by
    change sourceAngularRatio mode • weightedRadialCoordinate 1 lower 0 (high.val.ofLp.1.ofLp.1.ofLp.1 mode) =
      _ • (sourceAngularRatio mode • weightedRadialCoordinate 1 lower 0 (low.val.ofLp.1.ofLp.1.ofLp.1 mode))
    exact radialCoordinate_complex_scale lower _ _ _ _ (first mode)
  have f2 (mode : ℤ × ℤ) : unweightedSourceF2Bulk parameters lower high.val.ofLp.1.ofLp.1.ofLp.2 mode =
      Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 ^ grade • unweightedSourceF2Bulk parameters lower low.val.ofLp.1.ofLp.1.ofLp.2 mode := by
    change weightedRadialCoordinate 1 lower 0 (high.val.ofLp.1.ofLp.1.ofLp.2 mode) =
      _ • weightedRadialCoordinate 1 lower 0 (low.val.ofLp.1.ofLp.1.ofLp.2 mode)
    exact (congrArg (weightedRadialCoordinate 1 lower 0) (second mode)).trans
      ((weightedRadialCoordinate 1 lower 0).map_smul _ _)
  have g (mode : ℤ × ℤ) : originalAngularDecode lower high.val.ofLp.1.ofLp.2.ofLp.2 mode =
      Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 ^ grade • originalAngularDecode lower low.val.ofLp.1.ofLp.2.ofLp.2 mode := by
    change ((((1 + |(mode.1 : ℝ)|)⁻¹ : ℝ) : ℂ)) • high.val.ofLp.1.ofLp.2.ofLp.2 mode =
      _ • (((((1 + |(mode.1 : ℝ)|)⁻¹ : ℝ) : ℂ)) • low.val.ofLp.1.ofLp.2.ofLp.2 mode)
    exact (congrArg (fun value : RadialL2 1 lower => ((((1 + |(mode.1 : ℝ)|)⁻¹ : ℝ) : ℂ)) • value) (fourth mode)).trans
      (smul_comm _ _ _)
  have rg (mode : ℤ × ℤ) : sourceAngularBulk lower high.val.ofLp.1.ofLp.2.ofLp.2 mode =
      Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 ^ grade • sourceAngularBulk lower low.val.ofLp.1.ofLp.2.ofLp.2 mode := by
    change sourceAngularRatio mode • high.val.ofLp.1.ofLp.2.ofLp.2 mode =
      _ • (sourceAngularRatio mode • low.val.ofLp.1.ofLp.2.ofLp.2 mode)
    exact (congrArg (fun value : RadialL2 1 lower => sourceAngularRatio mode • value) (fourth mode)).trans
      (smul_comm _ _ _)
  rw [originalWeightedDatum_explicit, originalWeightedDatum_explicit]
  refine ⟨?_, ?_, first, second, ?_, ?_, ?_⟩
  · intro slot mode
    fin_cases slot
    · exact divisionHighWeight_real_family lower positive bounded _ _ _ f0 mode
    · exact divisionHighWeight_real_family lower positive bounded _ _ _ rf0 mode
    · exact divisionHighWeight_real_family lower positive bounded _ _ _ f2 mode
    · exact divisionHighWeight_real_family lower positive bounded _ _ _ third mode
  · intro slot mode
    fin_cases slot
    · exact divisionHighWeight_real_family lower positive bounded _ _ _ g mode
    · exact divisionHighWeight_real_family lower positive bounded _ _ _ rg mode
    · change (0 : RadialL2 1 lower) = _ • (0 : RadialL2 1 lower)
      rw [smul_zero]
  · intro mode
    change high.val.ofLp.2.ofLp.1.val mode = _ • low.val.ofLp.2.ofLp.1.val mode
    rw [highBoundary, lowBoundary]
    change (0 : ComplexEuclidean 1) = _ • (0 : ComplexEuclidean 1)
    rw [smul_zero]
  · intro mode
    change (lower ^ (-9 / 4 : ℝ) • high.val.ofLp.2.ofLp.2.ofLp.1) mode =
      _ • (lower ^ (-9 / 4 : ℝ) • low.val.ofLp.2.ofLp.2.ofLp.1) mode
    rw [highBoundary, lowBoundary]
    simp only [WithLp.ofLp_zero, Prod.fst_zero, Prod.snd_zero, smul_zero, lp.coeFn_zero, Pi.zero_apply]
  · intro index
    change originalLowIncomingWeightMap parameters lower L positive bounded lengthPositive high.val.ofLp.2.ofLp.2.ofLp.2 index =
      _ • originalLowIncomingWeightMap parameters lower L positive bounded lengthPositive low.val.ofLp.2.ofLp.2.ofLp.2 index
    rw [highBoundary, lowBoundary]
    simp only [WithLp.ofLp_zero, Prod.snd_zero, map_zero, lp.coeFn_zero, Pi.zero_apply, smul_zero]

end Grad.ExhaustionSourceAllocation
