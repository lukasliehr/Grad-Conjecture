import AKBS2OriginalSourceJointDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 950000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualOriginalSourceFirst
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers
open Grad.CartesianStartup Grad.ActualOriginalSourceMoments Grad.PhysicalAxisEquation
open Grad.RepresentedKernel.SpatialProduct Grad.WeakTesting Grad.WeakTesting.Commutation

private theorem scalarSource_derivative {dimension : ℕ}
    (function : Spatial → PhysicalValue dimension) (smooth : ContDiff ℝ ∞ function)
    (vector : PhysicalValue dimension) (direction : Fin 2) (point : Spatial) :
    directionDerivative direction (fun point => inner ℂ vector (function point)) point =
      inner ℂ vector (fderiv ℝ function point (spatialBasis direction)) := by
  let mapping := (innerSL ℂ vector).restrictScalars ℝ
  have identity := (mapping.hasFDerivAt.comp point
    ((smooth.differentiable (by simp) point).hasFDerivAt)).fderiv
  exact congrArg (fun derivative : Spatial →L[ℝ] ℂ => derivative (spatialDirection direction)) identity

variable {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)

/-- The full joint derivative is the genuine first weak derivative of the SAME weighted original source. -/
theorem originalSourceJointField_firstWeak (direction : Fin 2) :
    HasWeakOrderedDerivative dimension openUnitDisk 1 (startupFirstWord direction)
      (originalSourceJointField parameters field 0) (originalSourceJointDerivative parameters field direction) := by
  apply (hasWeakOrderedDerivative_iff_integral dimension openUnitDisk 1 (startupFirstWord direction) _ _).mpr
  intro cell vector test smooth compact supported
  let raw := originalWeightedSourceCell parameters field cell
  have rawSmooth : ContDiff ℝ ∞ raw := originalWeightedSourceCell_smooth parameters field cell
  have scalarSmooth : ContDiff ℝ ∞ (fun point => inner ℂ vector (raw point)) :=
    ((innerSL ℂ vector).restrictScalars ℝ).contDiff.comp rawSmooth
  have ibp := vectorFirstDerivative_ibp openUnitDisk openUnitDisk_isOpen test smooth compact supported
    (fun point => inner ℂ vector (raw point)) scalarSmooth.contDiffOn direction
  have firstSame : (∫ point in openUnitDisk, test point • inner ℂ vector
      (originalSourceJointDerivative parameters field direction point cell)) =
      ∫ point in openUnitDisk, test point • directionDerivative direction
        (fun point => inner ℂ vector (raw point)) point := by
    apply integral_congr_ae
    filter_upwards [originalSourceJointDerivative_same parameters field direction] with point same
    rw [same cell,scalarSource_derivative raw rawSmooth vector direction point]
  rw [firstSame,ibp,pow_one,neg_one_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [originalSourceJointField_weightedCell parameters field] with point same
  rw [same cell]
  congr 1
  simp only [orderedTestDerivative,iteratedFDeriv_one_apply]
  rfl

/-- Original source regularity, assembled by the accepted first-graph constructor from the stored grade. -/
def originalSourceFirst : StartupFirst dimension :=
  startupFirstGraph (originalSourceJointField parameters field 0)
    (originalSourceJointDerivative parameters field) (originalSourceJointField_firstWeak parameters field)

theorem originalSourceFirst_base :
    Grad.WeightedJets.base dimension 1 openUnitDisk (fun _ => 0) (originalSourceFirst parameters field) =
      (originalSourceMoments parameters field).field :=
  startupFirstGraph_base _ _ _

theorem originalSourceFirst_norm_sq :
    ‖originalSourceFirst parameters field‖^2 =
      ‖(originalSourceMoments parameters field).field‖^2 +
        ‖originalSourceJointDerivative parameters field 0‖^2 +
        ‖originalSourceJointDerivative parameters field 1‖^2 :=
  startupFirstGraph_norm_sq _ _ _

end Grad.ActualOriginalSourceFirst
