import ADY5LowIncomingTraceBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace
open Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

abbrev LowEnergyBoundary := lp (fun _ : LowAnnularIndex => ComplexEuclidean 1) 2

def lowIncomingFamily (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) : LowEnergyBoundary :=
  ⟨lowIncomingCoefficient lower length positive bounded field,
    (lp.memℓp ((lowIncomingConstant lower) • (lpNormFamily (field.val 0) + lpNormFamily (field.val 1)))).mono'
      (fun index => by
        change ‖lowIncomingCoefficient lower length positive bounded field index‖ ≤
          ‖lowIncomingConstant lower • (‖field.val 0 index‖ + ‖field.val 1 index‖)‖
        rw [norm_smul, Real.norm_of_nonneg (lowIncomingConstant_nonneg lower positive),
          Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
        exact lowIncomingCoefficient_bound lower length positive bounded field index)⟩

theorem lowIncomingFamily_bound (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) :
    ‖lowIncomingFamily lower length positive bounded field‖ ≤
      lowIncomingConstant lower * (‖field.val 0‖ + ‖field.val 1‖) := by
  calc
    _ ≤ ‖lowIncomingConstant lower • (lpNormFamily (field.val 0) + lpNormFamily (field.val 1))‖ := by
      apply lp.norm_mono (by norm_num)
      intro index
      change ‖lowIncomingCoefficient lower length positive bounded field index‖ ≤
        ‖lowIncomingConstant lower • (‖field.val 0 index‖ + ‖field.val 1 index‖)‖
      rw [norm_smul, Real.norm_of_nonneg (lowIncomingConstant_nonneg lower positive),
        Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
      exact lowIncomingCoefficient_bound lower length positive bounded field index
    _ = lowIncomingConstant lower * ‖lpNormFamily (field.val 0) + lpNormFamily (field.val 1)‖ := by
      rw [norm_smul, Real.norm_of_nonneg (lowIncomingConstant_nonneg lower positive)]
    _ ≤ lowIncomingConstant lower * (‖lpNormFamily (field.val 0)‖ + ‖lpNormFamily (field.val 1)‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (lowIncomingConstant_nonneg lower positive)
    _ = _ := by rw [lpNormFamily_norm, lpNormFamily_norm]

def lowIncomingLinear (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    lowEnergyGraph lower length positive →ₗ[ℂ] LowEnergyBoundary where
  toFun := lowIncomingFamily lower length positive bounded
  map_add' first second := by
    apply lp.ext
    funext index
    change lowIncomingCoefficient lower length positive bounded (first + second) index =
      lowIncomingCoefficient lower length positive bounded first index + lowIncomingCoefficient lower length positive bounded second index
    unfold lowIncomingCoefficient lowEnergyEndpoint
    rw [lowEnergySection_add]
    exact smul_add _ _ _
  map_smul' scalar field := by
    apply lp.ext
    funext index
    change lowIncomingCoefficient lower length positive bounded (scalar • field) index =
      scalar • lowIncomingCoefficient lower length positive bounded field index
    unfold lowIncomingCoefficient lowEnergyEndpoint
    rw [lowEnergySection_smul]
    exact smul_comm (lower ^ (-(7 / 4 : ℝ)) * (Real.sqrt (lowMu length lower index.2.val.2))⁻¹) scalar
      (lowEnergySection lower length positive bounded field index
        ⟨radialEndpointRadius lower 0, radialEndpointRadius_mem lower bounded.le 0⟩)

theorem lowIncomingLinear_bound (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) :
    ‖lowIncomingLinear lower length positive bounded field‖ ≤ (2 * lowIncomingConstant lower) * ‖field‖ := by
  have square := lowEnergyGraph_norm_sq lower length positive field
  have first : ‖field.val 0‖ ≤ ‖field‖ := by nlinarith [norm_nonneg field, sq_nonneg ‖field.val 1‖]
  have second : ‖field.val 1‖ ≤ ‖field‖ := by nlinarith [norm_nonneg field, sq_nonneg ‖field.val 0‖]
  exact (lowIncomingFamily_bound lower length positive bounded field).trans
    ((mul_le_mul_of_nonneg_left (by linarith : ‖field.val 0‖ + ‖field.val 1‖ ≤ 2 * ‖field‖)
      (lowIncomingConstant_nonneg lower positive)).trans_eq (by ring))

/-- Actual bounded trace into exactly the BE18 incoming data space. -/
def lowIncomingTrace (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1) :
    lowEnergyGraph lower length positive →L[ℂ] LowEnergyBoundary :=
  (lowIncomingLinear lower length positive bounded).mkContinuous (2 * lowIncomingConstant lower)
    (lowIncomingLinear_bound lower length positive bounded)

theorem lowIncomingTrace_apply (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) (index : LowAnnularIndex) :
    lowIncomingTrace lower length positive bounded field index =
      (lower ^ (-(7 / 4 : ℝ)) * (Real.sqrt (lowMu length lower index.2.val.2))⁻¹) •
        lowEnergyEndpoint lower length positive bounded 0 field index := rfl

theorem lowIncomingTrace_norm_sq (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) :
    ‖lowIncomingTrace lower length positive bounded field‖ ^ 2 =
      ∑' index : LowAnnularIndex, lower ^ (-(7 / 2 : ℝ)) * (lowMu length lower index.2.val.2)⁻¹ *
        ‖lowEnergyEndpoint lower length positive bounded 0 field index‖ ^ 2 := by
  have formula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (lowIncomingTrace lower length positive bounded field)
  norm_num at formula
  exact formula.trans (tsum_congr (fun index => lowIncomingCoefficient_norm_sq lower length positive bounded field index))

/-- The source is an arbitrary rho-L2 field and the incoming datum is arbitrary
in its prescribed half-order space. Both coordinates use a Hilbert sum. -/
abbrev LowEnergyData (lower : ℝ) := WithLp 2 (LowEnergyBulk lower × LowEnergyBoundary)

def lowDataResidual (lower : ℝ) (positive : 0 < lower) (data : LowEnergyData lower)
    (index : LowAnnularIndex) : CollarL2 (ComplexEuclidean 1) lower :=
  collarScalar 1 lower (lowStorageInverse lower positive) (data.ofLp.1 index)

def lowDataIncoming (lower length : ℝ) (data : LowEnergyData lower)
    (index : LowAnnularIndex) : ComplexEuclidean 1 :=
  (lower ^ (7 / 4 : ℝ) * Real.sqrt (lowMu length lower index.2.val.2)) • data.ofLp.2 index

theorem lowDataIncoming_normalization (lower length : ℝ) (positive : 0 < lower)
    (data : LowEnergyData lower) (index : LowAnnularIndex) :
    (lower ^ (-(7 / 4 : ℝ)) * (Real.sqrt (lowMu length lower index.2.val.2))⁻¹) •
      lowDataIncoming lower length data index = data.ofLp.2 index := by
  unfold lowDataIncoming
  rw [smul_smul]
  have product : (lower ^ (-(7 / 4 : ℝ)) * (Real.sqrt (lowMu length lower index.2.val.2))⁻¹) *
      (lower ^ (7 / 4 : ℝ) * Real.sqrt (lowMu length lower index.2.val.2)) = 1 := by
    calc
      _ = (lower ^ (-(7 / 4 : ℝ)) * lower ^ (7 / 4 : ℝ)) *
          ((Real.sqrt (lowMu length lower index.2.val.2))⁻¹ * Real.sqrt (lowMu length lower index.2.val.2)) := by ring
      _ = 1 := by rw [← Real.rpow_add positive, neg_add_cancel, Real.rpow_zero,
        inv_mul_cancel₀ (Real.sqrt_pos.mpr (lowMu_pos length lower index.2.val.2 positive)).ne', mul_one]
  rw [product, one_smul]

theorem lowDataIncoming_norm_sq (lower length : ℝ) (positive : 0 < lower)
    (data : LowEnergyData lower) (index : LowAnnularIndex) :
    ‖data.ofLp.2 index‖ ^ 2 = lower ^ (-(7 / 2 : ℝ)) * (lowMu length lower index.2.val.2)⁻¹ *
      ‖lowDataIncoming lower length data index‖ ^ 2 := by
  rw [← lowDataIncoming_normalization lower length positive data index, norm_smul,
    Real.norm_of_nonneg (by positivity), mul_pow, mul_pow, inv_pow, Real.sq_sqrt (lowMu_nonneg _ _ _)]
  have weight : (lower ^ (-(7 / 4 : ℝ))) ^ 2 = lower ^ (-(7 / 2 : ℝ)) := by
    rw [pow_two, ← Real.rpow_add positive]
    norm_num
  rw [weight]

/-- Literal BE18 data norm: there is no independent outer trace or source constraint. -/
theorem lowEnergyData_norm_sq (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (data : LowEnergyData lower) :
    ‖data‖ ^ 2 =
      (∑' index : LowAnnularIndex, ∫ radius in lower..1, radius ^ (-(7 / 2 : ℝ)) *
        ‖lowDataResidual lower positive data index radius‖ ^ 2) +
      (∑' index : LowAnnularIndex, lower ^ (-(7 / 2 : ℝ)) * (lowMu length lower index.2.val.2)⁻¹ *
        ‖lowDataIncoming lower length data index‖ ^ 2) := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  have first := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) data.ofLp.1
  have second := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) data.ofLp.2
  norm_num at first second
  rw [first, second]
  congr 1
  · exact tsum_congr (fun index => lowWeighted_norm_sq lower positive bounded (data.ofLp.1 index))
  · exact tsum_congr (fun index => lowDataIncoming_norm_sq lower length positive data index)

end Grad.AnnularLowEnergy
