import RadialWeightedInterface
import ProductPhaseDerivative

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace Grad.NonlinearRadial

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct

def dilationLinear (scale : ℝ) : SpatialPlane →L[ℝ] SpatialPlane :=
  scale • ContinuousLinearMap.id ℝ SpatialPlane

@[simp] theorem dilationLinear_apply (scale : ℝ) (point : SpatialPlane) :
    dilationLinear scale point = scale • point := rfl

theorem dilationLinear_norm (scale : ℝ) : ‖dilationLinear scale‖ = |scale| := by
  rw [dilationLinear, norm_smul, ContinuousLinearMap.norm_id, mul_one, Real.norm_eq_abs]

theorem dilation_mem_closed {scale : ℝ} (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1)
    (point : ClosedDisk) : scale • point.val ∈ closedUnitDisk := by
  change ‖scale • point.val‖ ≤ 1
  rw [norm_smul, Real.norm_of_nonneg nonnegative]
  exact (mul_le_of_le_one_left (norm_nonneg point.val) bounded).trans point.property

def dilationPoint (scale : ℝ) (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1)
    (point : ClosedDisk) : ClosedDisk :=
  ⟨scale • point.val, dilation_mem_closed nonnegative bounded point⟩

def dilationClosedMap (scale : ℝ) (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1) :
    C(ClosedDisk, ClosedDisk) :=
  ⟨dilationPoint scale nonnegative bounded,
    ((continuous_const : Continuous fun _ : ClosedDisk => scale).smul
      continuous_subtype_val).subtype_mk _⟩

def dilationJet {dimension : ℕ} (scale : ℝ) (field : ClosedJet dimension) : ClosedJet dimension :=
  globalClosedJet (fun point => smoothClosedExtension field (scale • point))
    ((smoothClosedExtension_smooth field).comp (dilationLinear scale).contDiff)

theorem dilationJet_value {dimension : ℕ} (scale : ℝ) (field : ClosedJet dimension)
    (point : ClosedDisk) :
    (dilationJet scale field).value point = smoothClosedExtension field (scale • point.val) := rfl

theorem dilationJet_value_closed {dimension : ℕ} {scale : ℝ}
    (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1) (field : ClosedJet dimension)
    (point : ClosedDisk) :
    (dilationJet scale field).value point = field.value (dilationPoint scale nonnegative bounded point) :=
  smoothClosedExtension_value field (dilationPoint scale nonnegative bounded point)

theorem cartesianDerivative_dilation {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (scale : ℝ) (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field)
    {rank : ℕ} (word : CartesianWord rank) (point : SpatialPlane) :
    cartesianDerivative rank word (fun source => field (scale • source)) point =
      scale ^ rank • cartesianDerivative rank word field (scale • point) := by
  change iteratedFDeriv ℝ rank (field ∘ dilationLinear scale) point
      (fun index => spatialBasis (word index)) = _
  rw [(dilationLinear scale).iteratedFDeriv_comp_right (i := rank) smooth point (by exact_mod_cast le_top),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp only [dilationLinear_apply, ContinuousMultilinearMap.map_smul_univ,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rfl

theorem dilationJet_derivative {dimension rank : ℕ} {scale : ℝ}
    (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1) (field : ClosedJet dimension)
    (word : CartesianWord rank) (point : ClosedDisk) :
    closedDerivative (dilationJet scale field) rank word point =
      scale ^ rank • closedDerivative field rank word (dilationPoint scale nonnegative bounded point) := by
  rw [dilationJet, globalClosedJet_derivative,
    cartesianDerivative_dilation scale _ (smoothClosedExtension_smooth field)]
  exact congrArg (fun value => scale ^ rank • value)
    (smoothClosedExtension_derivative field word (dilationPoint scale nonnegative bounded point))

end Grad.NonlinearRadial
