import AKN30ExactEXSourceAllocationBound

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.SourceCollarFullSource Grad.SourceCollarCoefficients Grad.AnnularCurrentSource
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.ConstrainedGrades
open Grad.SourceCollarBulk Grad.AnnularStrongData Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularExhaustionEstimate

theorem radialL2_real_smul (dimension : ℕ) (lower scalar : ℝ) (field : RadialL2 dimension lower) :
    (scalar : ℂ) • field = scalar • field := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (scalar : ℂ) field, Lp.coeFn_smul scalar field] with radius complex real
  rw [complex, real]
  exact Complex.coe_smul scalar (field radius)

theorem restrictedCore_frame_inserted (parameters : PhaseParameters) (field : ACore parameters 2)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (grade base : ℕ) (mode : ℤ × ℤ) :
    let high := completedRestrictionRow (power := grade + base) (radial := 0) lower positive bounded parameters
      (by omega : grade + base + 0 ≤ grade + base + 1)
      (aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade + base + 1) field))
    let low := completedRestrictionRow (power := base) (radial := 0) lower positive bounded parameters
      (by omega : base + 0 ≤ base + 1)
      (aGradeEta parameters (GradeCore.ofCoreLinear (grade := base + 1) field))
    radialRowContraction lower positive (grade + base) high mode =
      ((annularFrequency mode.1 mode.2 : ℂ) ^ grade) • radialRowContraction lower positive base low mode ∧
    tangentialRowContraction lower positive (grade + base) high mode =
      ((annularFrequency mode.1 mode.2 : ℂ) ^ grade) • tangentialRowContraction lower positive base low mode := by
  dsimp only
  have high := restrictionCore_rows_compatible parameters field lower positive bounded
    (by omega : grade + base + 0 ≤ grade + base + 1)
  have low := restrictionCore_rows_compatible parameters field lower positive bounded
    (by omega : base + 0 ≤ base + 1)
  have radialHigh := high.radial positive mode
  have radialLow := low.radial positive mode
  have tangentHigh := high.tangential positive mode
  have tangentLow := low.tangential positive mode
  have same := restrictionRow_core_grade_independent (power := 0) (radial := 0) parameters field lower positive bounded
    (by omega : 0 + 0 ≤ base + 1) (by omega : 0 + 0 ≤ grade + base + 1)
  rw [same] at radialLow tangentLow
  rw [radialHigh, radialLow, tangentHigh, tangentLow]
  simp only [pow_add, mul_smul, and_self]

theorem actualOriginalF1Row_inserted (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (mode : ℤ × ℤ) :
    actualOriginalF1Row parameters lower positive bounded grade source mode =
      annularFrequency mode.1 mode.2 ^ grade • actualOriginalF1Row parameters lower positive bounded 0 source mode := by
  rw [actualOriginalF1Row_value, actualOriginalF1Row_value]
  change annularWeightLoweringRatio mode • _ = _ • (annularWeightLoweringRatio mode • _)
  rw [(restrictedCore_frame_inserted parameters (cartesianSourceVector source) lower positive bounded grade 1 mode).1,
    smul_comm (annularWeightLoweringRatio mode), ← Complex.ofReal_pow, radialL2_real_smul]

theorem actualOriginalF0Graph_inserted (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (mode : ℤ × ℤ) :
    actualOriginalF0Graph parameters lower positive bounded grade source mode =
      annularFrequency mode.1 mode.2 ^ grade • actualOriginalF0Graph parameters lower positive bounded 0 source mode := by
  apply weightedRadial_value_injective 1 lower positive bounded.le
  rw [map_smul]
  change annularSourceCoordinate parameters 1 lower 1 0 0
      (actualOriginalF0Graph parameters lower positive bounded grade source) mode =
    _ • annularSourceCoordinate parameters 1 lower 1 0 0
      (actualOriginalF0Graph parameters lower positive bounded 0 source) mode
  rw [actualOriginalF0Graph_value, actualOriginalF0Graph_value]
  change annularS11Ratio mode • _ = _ • (annularS11Ratio mode • _)
  rw [(restrictedCore_frame_inserted parameters (cartesianSourceVector source) lower positive bounded.le grade 1 mode).2,
    smul_comm (annularS11Ratio mode), ← Complex.ofReal_pow, radialL2_real_smul]

theorem actualOriginalF2Graph_inserted (parameters : PhaseParameters) (L lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (mode : ℤ × ℤ) :
    actualOriginalF2Graph parameters L lower positive bounded grade source mode =
      annularFrequency mode.1 mode.2 ^ grade • actualOriginalF2Graph parameters L lower positive bounded 0 source mode := by
  apply weightedRadial_value_injective 1 lower positive bounded.le
  rw [map_smul]
  change annularSourceCoordinate parameters 1 lower 0 0 0
      (actualOriginalF2Graph parameters L lower positive bounded grade source) mode =
    _ • annularSourceCoordinate parameters 1 lower 0 0 0
      (actualOriginalF2Graph parameters L lower positive bounded 0 source) mode
  rw [actualOriginalF2Graph_value, actualOriginalF2Graph_value]
  simp only [lp.coeFn_smul, Pi.smul_apply]
  rw [restrictionCore_rows_compatible parameters (source 3) lower positive bounded.le
    (by omega : grade + 0 ≤ grade + 1) mode]
  rw [restrictionRow_core_grade_independent parameters (source 3) lower positive bounded.le
    (by omega : 0 + 0 ≤ grade + 1) (by norm_num : 0 + 0 ≤ 0 + 1)]
  rw [smul_comm (L : ℂ)⁻¹, ← Complex.ofReal_pow, radialL2_real_smul]

end Grad.ExhaustionSourceAllocation
