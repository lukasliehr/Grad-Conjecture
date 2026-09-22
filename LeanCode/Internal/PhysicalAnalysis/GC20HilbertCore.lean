import GC20ScalarTrace
import GC21Boundary

noncomputable section

open MeasureTheory Set
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.WeightedTrace

variable (Value : Type*) [NormedAddCommGroup Value] [InnerProductSpace ℝ Value]

/-- Genuine C¹ graphs, before taking the collar H¹ completion. -/
def collarSmoothGraph : Submodule ℝ (C(ℝ, Value) × C(ℝ, Value)) where
  carrier := {pair | ∀ point : ℝ, HasDerivAt pair.1 (pair.2 point) point}
  zero_mem' := fun _ => hasDerivAt_const _ _
  add_mem' := by
    intro first second firstLaw secondLaw point
    exact (firstLaw point).add (secondLaw point)
  smul_mem' := by
    intro scalar pair law point
    exact (law point).const_smul scalar

abbrev CollarL2 (lower : ℝ) := Lp Value 2 (volume.restrict (Icc lower 1))

omit [InnerProductSpace ℝ Value] in
theorem collarContinuous_memLp (lower : ℝ) (curve : C(ℝ, Value)) :
    MemLp curve 2 (volume.restrict (Icc lower 1)) := by
  apply (memLp_two_iff_integrable_sq_norm curve.continuous.aestronglyMeasurable).2
  exact (curve.continuous.norm.pow 2).integrableOn_Icc

def collarContinuousL2 (lower : ℝ) : C(ℝ, Value) →ₗ[ℝ] CollarL2 Value lower where
  toFun curve := (collarContinuous_memLp Value lower curve).toLp curve
  map_add' first second := by
    exact MemLp.toLp_add (collarContinuous_memLp Value lower first) (collarContinuous_memLp Value lower second)
  map_smul' scalar curve := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (collarContinuous_memLp Value lower (scalar • curve)),
      Lp.coeFn_smul scalar ((collarContinuous_memLp Value lower curve).toLp curve),
      MemLp.coeFn_toLp (collarContinuous_memLp Value lower curve)] with point first second third
    change _ = (scalar • (collarContinuous_memLp Value lower curve).toLp curve) point
    rw [first, second]
    change scalar • curve point = scalar • _
    rw [third]

theorem collarContinuousL2_norm_sq (lower : ℝ) (lowerOne : lower ≤ 1) (curve : C(ℝ, Value)) :
    ‖collarContinuousL2 Value lower curve‖ ^ 2 = ∫ point in lower..1, ‖curve point‖ ^ 2 := by
  have normFormula : ‖collarContinuousL2 Value lower curve‖ ^ 2 =
      ∫ point : ℝ, ‖collarContinuousL2 Value lower curve point‖ ^ 2 ∂volume.restrict (Icc lower 1) := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
  rw [normFormula]
  rw [intervalIntegral.integral_of_le lowerOne, ← integral_Icc_eq_integral_Ioc]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp (collarContinuous_memLp Value lower curve)] with point equality
  change ‖(collarContinuous_memLp Value lower curve).toLp curve point‖ ^ 2 = _
  rw [equality]

abbrev CollarH1Ambient (lower : ℝ) := PiLp 2 (fun _ : Fin 2 => CollarL2 Value lower)

def collarGraphLinear (lower : ℝ) : collarSmoothGraph Value →ₗ[ℝ] CollarH1Ambient Value lower where
  toFun pair := WithLp.toLp 2 ![collarContinuousL2 Value lower pair.val.1, collarContinuousL2 Value lower pair.val.2]
  map_add' first second := by
    apply PiLp.ext
    intro entry
    fin_cases entry <;> simp [map_add]
  map_smul' scalar pair := by
    apply PiLp.ext
    intro entry
    fin_cases entry <;> simp [map_smul]

def collarEndpointLinear : collarSmoothGraph Value →ₗ[ℝ] Value where
  toFun pair := pair.val.1 1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem collarGraphLinear_norm_sq (lower : ℝ) (lowerOne : lower ≤ 1) (pair : collarSmoothGraph Value) :
    ‖collarGraphLinear Value lower pair‖ ^ 2 =
      (∫ point in lower..1, ‖pair.val.1 point‖ ^ 2) + (∫ point in lower..1, ‖pair.val.2 point‖ ^ 2) := by
  rw [PiLp.norm_sq_eq_of_L2]
  rw [Fin.sum_univ_two]
  change ‖collarContinuousL2 Value lower pair.val.1‖ ^ 2 + ‖collarContinuousL2 Value lower pair.val.2‖ ^ 2 = _
  rw [collarContinuousL2_norm_sq Value lower lowerOne, collarContinuousL2_norm_sq Value lower lowerOne]

theorem collarGraph_endpoint_bound (lower : ℝ) (lowerOne : lower < 1) (pair : collarSmoothGraph Value) :
    ‖collarEndpointLinear Value pair‖ ≤ Real.sqrt (collarTraceConstant lower) * ‖collarGraphLinear Value lower pair‖ := by
  have bound := scalar_collar_trace pair.val.1 pair.val.2 lower 1 lowerOne le_rfl
    pair.val.1.continuous pair.val.2.continuous (fun point _ => pair.property point)
  simp only [one_mul, inv_one] at bound
  rw [← collarGraphLinear_norm_sq Value lower lowerOne.le pair] at bound
  have nonnegative : 0 ≤ collarTraceConstant lower := (zero_le_one.trans (collarTraceConstant_one_le lowerOne))
  have rooted := Real.sqrt_le_sqrt bound
  simpa only [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), Real.sqrt_mul nonnegative,
    collarEndpointLinear, LinearMap.coe_mk, AddHom.coe_mk] using rooted

end Grad.GaugeCoefficients.Physical.WeightedTrace
