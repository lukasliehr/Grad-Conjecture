import BL2Profile

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.AnalyticWeights.Higher

def radialLineLinear : ℝ →L[ℝ] SpatialPlane :=
  ContinuousLinearMap.toSpanSingleton ℝ (-radialLine 0)

theorem radialLineLinear_norm : ‖radialLineLinear‖ = 1 := by
  rw [radialLineLinear, ContinuousLinearMap.norm_toSpanSingleton, norm_neg, radialLine_norm]
  norm_num

theorem radialLine_affine (time : ℝ) : radialLine time = radialLineLinear time + radialLine 0 := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [radialLine, radialLineLinear, ContinuousLinearMap.toSpanSingleton_apply]
  ring

theorem radialLine_iteratedDeriv_bound {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field)
    (order : ℕ) (time : ℝ) :
    ‖iteratedDeriv order (fun source => field (radialLine source)) time‖ ≤
      ‖iteratedFDeriv ℝ order field (radialLine time)‖ := by
  rw [← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have representation : (fun source => field (radialLine source)) =
      (fun point : SpatialPlane => field (point + radialLine 0)) ∘ radialLineLinear := by
    funext source
    rw [radialLine_affine]
    rfl
  have translatedSmooth : ContDiff ℝ ∞ (fun point : SpatialPlane => field (point + radialLine 0)) :=
    smooth.comp (contDiff_id.add contDiff_const)
  rw [representation, radialLineLinear.iteratedFDeriv_comp_right
    translatedSmooth time
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))]
  have bound := (iteratedFDeriv ℝ order (fun point : SpatialPlane => field (point + radialLine 0))
    (radialLineLinear time)).norm_compContinuousLinearMap_le (fun _ => radialLineLinear)
  simpa only [radialLineLinear_norm, Finset.prod_const_one, mul_one,
    iteratedFDeriv_comp_add_right, ← radialLine_affine] using bound

def physicalWeightDerivativeConstant (order : ℕ) (gamma : ℝ) : ℝ :=
  if order = 0 then 1 else partitionProductConstant order * weightCost order gamma 1

theorem physicalWeightDerivativeConstant_nonnegative (order : ℕ) (gamma : ℝ)
    (gammaNonnegative : 0 ≤ gamma) : 0 ≤ physicalWeightDerivativeConstant order gamma := by
  unfold physicalWeightDerivativeConstant
  split_ifs with zeroOrder
  · exact zero_le_one
  · apply mul_nonneg (partitionProductConstant_nonnegative _)
    simp only [weightCost, if_neg zeroOrder, one_pow, mul_one]
    exact mul_nonneg gammaNonnegative (pow_nonneg (by linarith) _)

theorem cartesianWeight_iterated_bound (parameters : PhaseParameters) (cell : ℤ)
    (order : ℕ) (point : SpatialPlane) :
    ‖iteratedFDeriv ℝ order (cartesianWeight parameters cell) point‖ ≤
      physicalWeightDerivativeConstant order parameters.gamma * cartesianWeight parameters cell point *
        cellFrequency cell ^ order := by
  by_cases zeroOrder : order = 0
  · subst order
    rw [norm_iteratedFDeriv_zero, Real.norm_of_nonneg (cartesianWeight_pos parameters cell point).le]
    simp [physicalWeightDerivativeConstant]
  · rw [show cartesianWeight parameters cell =
        Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma 1 cell by rfl]
    simpa only [cellFrequency, physicalWeightDerivativeConstant, if_neg zeroOrder] using
      physicalWeight_iterated_norm_bound parameters.sigma0 parameters.gamma 1 cell
        parameters.gamma_pos.le (by norm_num) order (by omega) point

def radialWeight (parameters : PhaseParameters) (cell : ℤ) (time : ℝ) : ℝ :=
  cartesianWeight parameters cell (radialLine time)

theorem radialWeight_smooth (parameters : PhaseParameters) (cell : ℤ) :
    ContDiff ℝ ∞ (radialWeight parameters cell) :=
  (cartesianWeight_contDiff parameters cell).comp radialLine_smooth

theorem radialWeight_iterated_bound (parameters : PhaseParameters) (cell : ℤ)
    (order : ℕ) (time : ℝ) :
    ‖iteratedDeriv order (radialWeight parameters cell) time‖ ≤
      physicalWeightDerivativeConstant order parameters.gamma * radialWeight parameters cell time *
        cellFrequency cell ^ order :=
  (radialLine_iteratedDeriv_bound _ (cartesianWeight_contDiff parameters cell) order time).trans
    (cartesianWeight_iterated_bound parameters cell order (radialLine time))

end Grad.BoundaryLift
