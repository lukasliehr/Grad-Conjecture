import AKU3CurrentLeadingSourceSystem

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
open scoped Topology ContDiff
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ChartAxisLift
open Grad.NonlinearQuotientBounds Grad.NonlinearDivision

/-- The JF cutoff is fixed once: one through radius1/8 and zero from1/4. -/
def finiteLiftCutoff : SpatialPlane → ℝ := radialCap (1/2) (by norm_num)

theorem finiteLiftCutoff_smooth : ContDiff ℝ ∞ finiteLiftCutoff :=
  radialCap_smooth (1/2) (by norm_num)

theorem finiteLiftCutoff_one (point : SpatialPlane) (inside : ‖point‖ ≤ 1/8) :
    finiteLiftCutoff point = 1 :=
  radialCap_one (1/2) (by norm_num) point (by norm_num; exact inside)

theorem finiteLiftCutoff_zero (point : SpatialPlane) (outside : 1/4 ≤ ‖point‖) :
    finiteLiftCutoff point = 0 :=
  radialCap_zero (1/2) (by norm_num) point (by norm_num; exact outside)

def localizedFiniteJet {dimension : ℕ} (field : ClosedJet dimension) : ClosedJet dimension :=
  globalClosedJet (fun point => finiteLiftCutoff point • smoothClosedExtension field point)
    (finiteLiftCutoff_smooth.smul (smoothClosedExtension_smooth field))

theorem localizedFiniteJet_value {dimension : ℕ} (field : ClosedJet dimension) (point : ClosedDisk) :
    (localizedFiniteJet field).value point = finiteLiftCutoff point.val • field.value point := by
  rw [localizedFiniteJet,globalClosedJet_value,smoothClosedExtension_value]

theorem localizedFiniteJet_value_zero {dimension : ℕ} (field : ClosedJet dimension)
    (point : ClosedDisk) (outside : 1/4 ≤ ‖point.val‖) :
    (localizedFiniteJet field).value point = 0 := by
  rw [localizedFiniteJet_value,finiteLiftCutoff_zero point.val outside,zero_smul]

/-- Every genuine axis derivative is preserved, so the cutoff changes no
source jet of any finite order. -/
theorem localizedFiniteJet_axis_derivative {dimension order : ℕ} (field : ClosedJet dimension)
    (word : CartesianWord order) :
    closedDerivative (localizedFiniteJet field) order word closedOrigin =
      closedDerivative field order word closedOrigin := by
  have agreement : EqOn (fun point => finiteLiftCutoff point • smoothClosedExtension field point)
      (smoothClosedExtension field) (Metric.ball (0 : SpatialPlane) (1/8)) := by
    intro point member
    have inside : ‖point‖ ≤ 1/8 := (by simpa only [Metric.mem_ball,dist_zero_right] using member : ‖point‖ < 1/8).le
    dsimp only
    rw [finiteLiftCutoff_one point inside,one_smul]
  have zeroInside : (0 : SpatialPlane) ∈ Metric.ball (0 : SpatialPlane) (1/8) := by simp
  have derivatives := iteratedFDerivWithin_congr (𝕜 := ℝ) agreement zeroInside order
  rw [iteratedFDerivWithin_of_isOpen order Metric.isOpen_ball zeroInside,
    iteratedFDerivWithin_of_isOpen order Metric.isOpen_ball zeroInside] at derivatives
  rw [localizedFiniteJet,globalClosedJet_derivative,← smoothClosedExtension_derivative field word]
  exact congrArg (fun derivative => derivative (fun index => spatialBasis (word index))) derivatives

def localizedFiniteJetLinear (dimension : ℕ) : ClosedJet dimension →ₗ[ℂ] ClosedJet dimension where
  toFun := localizedFiniteJet
  map_add' first second := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    simp only [localizedFiniteJet_value,closedJet_value_add,ContinuousMap.add_apply,smul_add]
  map_smul' scalar field := by
    change localizedFiniteJet (scalar • field) = scalar • localizedFiniteJet field
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    simp only [localizedFiniteJet_value,closedJet_value_smul,ContinuousMap.smul_apply]
    exact smul_comm _ _ _

end Grad.FinitePhysicalJetLift
