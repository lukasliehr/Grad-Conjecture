import AKR10PolynomialTupleJetBulk

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularOriginalLow Grad.AnnularLowEnergy Grad.AnnularCurrentLow
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Exact original AJ6 constants, used only on a fixed collar. -/
def tupleAJGrowthConstant (parameters : PhaseParameters) (lower length : ℝ) : ℝ :=
  |(Real.sqrt 3 * length)⁻¹| + |originalLowCenterScale parameters lower length| + 1

theorem tupleAJGrowthConstant_one_le (parameters : PhaseParameters) (lower length : ℝ) :
    1 ≤ tupleAJGrowthConstant parameters lower length := by
  unfold tupleAJGrowthConstant
  linarith [abs_nonneg ((Real.sqrt 3 * length)⁻¹),abs_nonneg (originalLowCenterScale parameters lower length)]

theorem tupleAJScale_bound (parameters : PhaseParameters) (lower length : ℝ) (mode : LowAnnularMode) :
    |originalLowScale parameters lower length mode| ≤ tupleAJGrowthConstant parameters lower length := by
  unfold originalLowScale tupleAJGrowthConstant
  split_ifs <;> linarith [abs_nonneg ((Real.sqrt 3 * length)⁻¹),abs_nonneg (originalLowCenterScale parameters lower length)]

/-- Rows are (S_ell Lambda xi, R p), with their literal Lambda^-1
radial derivative coordinates. The phase is already in the tuple jets. -/
def tupleAJCoefficient (parameters : PhaseParameters) (lower length : ℝ)
    (row coordinate : Fin 2) (mode : LowAnnularMode) : ℂ :=
  if row = 0 then
    if coordinate = 0 then ((originalLowScale parameters lower length mode * cellFrequency mode.val.2 : ℝ) : ℂ)
    else (originalLowScale parameters lower length mode : ℂ)
  else
    if coordinate = 0 then Complex.I * (mode.val.1 : ℂ)
    else (cellFrequency mode.val.2 : ℂ)⁻¹ * (Complex.I * (mode.val.1 : ℂ))

theorem tupleAJCoefficient_growth (parameters : PhaseParameters) (lower length : ℝ)
    (row coordinate : Fin 2) (mode : LowAnnularMode) :
    ‖tupleAJCoefficient parameters lower length row coordinate mode‖ ≤
      tupleAJGrowthConstant parameters lower length * annularFrequency mode.val.1 mode.val.2 ^ 1 := by
  have scale := tupleAJScale_bound parameters lower length mode
  have one := tupleAJGrowthConstant_one_le parameters lower length
  have frequency : 1 ≤ annularFrequency mode.val.1 mode.val.2 := by
    unfold annularFrequency
    linarith [abs_nonneg (mode.val.1 : ℝ),abs_nonneg (mode.val.2 : ℝ)]
  have angular : |(mode.val.1 : ℝ)| ≤ annularFrequency mode.val.1 mode.val.2 := by
    unfold annularFrequency
    linarith [abs_nonneg (mode.val.2 : ℝ)]
  have cell : cellFrequency mode.val.2 ≤ annularFrequency mode.val.1 mode.val.2 := by
    apply (Grad.PhaseAlgebra.cellFrequency_le_polynomial mode.val.2).trans
    change 1 + |(mode.val.2 : ℝ)| ≤ 1 + |(mode.val.1 : ℝ)| + |(mode.val.2 : ℝ)|
    linarith [abs_nonneg (mode.val.1 : ℝ)]
  have invCell : (cellFrequency mode.val.2)⁻¹ ≤ 1 := by
    exact (inv_le_one₀ (cellFrequency_pos _)).2 (cellFrequency_one_le _)
  have angularNorm : ‖Complex.I * (mode.val.1 : ℂ)‖ = |(mode.val.1 : ℝ)| := by
    rw [norm_mul,Complex.norm_I,one_mul]
    rw [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
  rw [pow_one]
  fin_cases row <;> fin_cases coordinate
  · change ‖((originalLowScale parameters lower length mode * cellFrequency mode.val.2 : ℝ) : ℂ)‖ ≤ _
    rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos (cellFrequency_pos _)]
    exact mul_le_mul scale cell (cellFrequency_pos _).le (zero_le_one.trans one)
  · change ‖(originalLowScale parameters lower length mode : ℂ)‖ ≤ _
    rw [Complex.norm_real,Real.norm_eq_abs]
    exact scale.trans (le_mul_of_one_le_right (zero_le_one.trans one) frequency)
  · change ‖Complex.I * (mode.val.1 : ℂ)‖ ≤ _
    rw [angularNorm]
    exact angular.trans (le_mul_of_one_le_left (zero_le_one.trans frequency) one)
  · change ‖(cellFrequency mode.val.2 : ℂ)⁻¹ * (Complex.I * (mode.val.1 : ℂ))‖ ≤ _
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_of_nonneg (cellFrequency_pos _).le,angularNorm]
    exact (mul_le_mul_of_nonneg_right invCell (abs_nonneg _)).trans
      ((one_mul _).le.trans (angular.trans (le_mul_of_one_le_left (zero_le_one.trans frequency) one)))

end Grad.AnnularOriginalCoreRealization
