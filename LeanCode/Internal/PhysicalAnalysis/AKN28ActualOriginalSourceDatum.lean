import AKN27StoredOriginalMeanConstraints
import AKL1LiteralExhaustionWeightedNorms

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.SourceCollarFullSource Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace Grad.AnnularCurrentSource
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.Constraints Grad.BoundaryTrace
open Grad.SourceCollarBulk Grad.AnnularStrongData Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation

theorem actualOriginalF2Graph_mean_zero (parameters : PhaseParameters) (L lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (mode : ℤ × ℤ) (modeZero : mode.1 = 0) :
    unweightedSourceF2Bulk parameters lower
      (actualOriginalF2Graph parameters L lower positive bounded grade source) mode = 0 := by
  unfold unweightedSourceF2Bulk
  rw [actualOriginalF2Graph_value]
  change (L : ℂ)⁻¹ • _ = (0 : RadialL2 1 lower)
  rw [restrictedCore_row_mean_zero parameters (source 3) flat.1.1 lower positive bounded.le
    (by omega : grade + 0 ≤ grade + 1) mode modeZero, smul_zero]

theorem actualOriginalF1Row_mean_zero (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (mode : ℤ × ℤ) (modeZero : mode.1 = 0) :
    actualOriginalF1Row parameters lower positive bounded grade source mode = 0 := by
  rw [actualOriginalF1Row_value]
  change annularWeightLoweringRatio mode • _ = (0 : RadialL2 1 lower)
  rw [radialRestrictionCore_row_mean_zero parameters (cartesianSourceVector source)
    ((isFlat_iff_cartesian source).mp flat).1 lower positive bounded
    (by omega : grade + 1 + 0 ≤ grade + 2) mode modeZero, smul_zero]

theorem fullG3Row_core_mean_zero {grade power : ℕ}
    (parameters : PhaseParameters) (L rho epsilon : ℝ) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (paid : power + 3 ≤ grade)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (mode : ℤ × ℤ) (modeZero : mode.1 = 0) :
    fullG3Row (power := power) parameters L rho epsilon field small lower positive bounded paid
      (quotientEta parameters grade source) mode = 0 := by
  change (L : ℂ)⁻¹ • completedRestrictionRow (power := power) (radial := 0)
    lower positive bounded parameters (by omega)
    (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) (source 2))) mode +
      meanFreeRow lower _ mode = 0
  rw [meanFreeRow_apply, if_pos modeZero, add_zero,
    restrictedCore_row_mean_zero parameters (source 2) flat.1.2.1 lower positive bounded
      (by omega : power + 0 ≤ grade) mode modeZero, smul_zero]

theorem actualOriginalG3Row_mean_zero (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source)
    (mode : ℤ × ℤ) (modeZero : mode.1 = 0) :
    actualOriginalG3Row parameters L rho epsilon field small lower positive bounded grade source mode = 0 := by
  rw [actualOriginalG3Row, strengthenedG_mode lower _ _
    (fun other => g3AngularRow_mode parameters L rho epsilon field small lower positive bounded (by omega) _ other)]
  change _ • (annularWeightLoweringRatio mode • _) = (0 : RadialL2 1 lower)
  rw [fullG3Row_core_mean_zero parameters L rho epsilon field small lower positive bounded
    (by omega : grade + 1 + 3 ≤ grade + 6) source flat mode modeZero, smul_zero, smul_zero]

/-- The original four source blocks, with independent physical outer datum,
high incoming d and low incoming k all zero. The source-induced outer forcing
is retained by the accepted inverse; it is not erased here. -/
def actualOriginalSourceDatum (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    OriginalStrongCarrier parameters lower 0 0 := by
  let datum : OriginalStrongAmbient parameters lower 0 0 := WithLp.toLp 2
    (WithLp.toLp 2
      (WithLp.toLp 2 (actualOriginalF0Graph parameters lower positive bounded grade source,
        actualOriginalF2Graph parameters L lower positive bounded grade source),
       WithLp.toLp 2 (actualOriginalF1Row parameters lower positive bounded.le grade source,
        actualOriginalG3Row parameters L rho epsilon field small lower positive bounded.le grade source)), 0)
  refine ⟨datum, ⟨⟨?_, ?_⟩, ?_⟩⟩
  · change meanFreeRow lower (unweightedSourceF2Bulk parameters lower
        (actualOriginalF2Graph parameters L lower positive bounded grade source)) - _ = 0
    apply sub_eq_zero.mpr
    exact (meanFreeRow_fixed_iff lower _).mpr
      (actualOriginalF2Graph_mean_zero parameters L lower positive bounded grade source flat)
  · change meanFreeRow lower (actualOriginalF1Row parameters lower positive bounded.le grade source) - _ = 0
    apply sub_eq_zero.mpr
    exact (meanFreeRow_fixed_iff lower _).mpr
      (actualOriginalF1Row_mean_zero parameters lower positive bounded.le grade source flat)
  · change meanFreeRow lower (actualOriginalG3Row parameters L rho epsilon field small lower positive bounded.le grade source) - _ = 0
    apply sub_eq_zero.mpr
    exact (meanFreeRow_fixed_iff lower _).mpr
      (actualOriginalG3Row_mean_zero parameters L rho epsilon field small lower positive bounded.le grade source flat)

theorem actualOriginalSourceDatum_source4 (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    (actualOriginalSourceDatum parameters L rho epsilon field small lower positive bounded grade source flat).val.ofLp.1 =
      WithLp.toLp 2 (WithLp.toLp 2 (actualOriginalF0Graph parameters lower positive bounded grade source,
        actualOriginalF2Graph parameters L lower positive bounded grade source),
       WithLp.toLp 2 (actualOriginalF1Row parameters lower positive bounded.le grade source,
        actualOriginalG3Row parameters L rho epsilon field small lower positive bounded.le grade source)) := rfl

theorem actualOriginalSourceDatum_boundary (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    (actualOriginalSourceDatum parameters L rho epsilon field small lower positive bounded grade source flat).val.ofLp.2 = 0 := rfl

end Grad.ExhaustionSourceAllocation
