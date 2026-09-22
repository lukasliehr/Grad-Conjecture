import NGP02ExteriorBound

noncomputable section

set_option maxHeartbeats 800000

open Set
open scoped BigOperators

namespace Grad.CartesianState

open Grad.ClosedJets
open Grad.DiskExtension.Operator

local instance ngp02TorusCellPeriodPositive : Fact (0 < 2 * Real.pi) :=
  ⟨by positivity⟩

@[simp] theorem torusPhysicalOperatorDerivative_basis
    {dimension order : ℕ} (field : TorusSmoothField dimension)
    (point : TorusCellDomain) (word : MixedCartesianWord order) :
    torusPhysicalOperatorDerivative field order point
        (fun position => spatialCellBasis (word position)) =
      torusDerivative field order word point := by
  classical
  change (∑ coefficientWord : MixedCartesianWord order,
      (spatialCellWordCoefficient coefficientWord).smulRight
        (torusDerivative field order coefficientWord point))
        (fun position => spatialCellBasis (word position)) = _
  rw [sum_apply]
  rw [Finset.sum_eq_single word]
  · rw [ContinuousMultilinearMap.smulRight_apply,
      spatialCellWordCoefficient_basis, if_pos rfl, one_smul]
  · intro other _ otherNe
    rw [ContinuousMultilinearMap.smulRight_apply,
      spatialCellWordCoefficient_basis, if_neg otherNe, zero_smul]
  · simp

theorem physicalCollar_mem_fundamentalIocSquare
    (point : PhysicalCollar) : point.val ∈ fundamentalIocSquare := by
  have normLe : ‖point.val‖ ≤ (4 / 3 : ℝ) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using point.property
  have firstLe := spatialPlane_coordinate_abs_le_norm point.val (0 : Fin 2)
  have secondLe := spatialPlane_coordinate_abs_le_norm point.val (1 : Fin 2)
  constructor <;> constructor <;>
    linarith [le_abs_self (point.val 0), neg_abs_le (point.val 0),
      le_abs_self (point.val 1), neg_abs_le (point.val 1)]

theorem physicalCollarToTorus_eq_torusCellPoint
    (point : PhysicalCollar) (cell : CellCircle) :
    physicalCollarToTorus (point, cell) =
      torusCellPoint
        (assembleSpatialCell point.val (physicalCellRepresentative cell)) := by
  unfold physicalCollarToTorus torusCellPoint
  change (((((point.val 0 : ℝ) : SpatialCircle),
      ((point.val 1 : ℝ) : SpatialCircle)), cell)) =
    (((((point.val 0 : ℝ) : SpatialCircle),
      ((point.val 1 : ℝ) : SpatialCircle)),
        ((physicalCellRepresentative cell : ℝ) : CellCircle)))
  rw [physicalCellRepresentative_coe]

/-- On the whole physical collar the descended torus derivative is exactly
the all-order ambient derivative built by P09. -/
theorem torusPhysicalOperatorDerivative_periodized_at_collar
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (point : PhysicalCollar) (cell : CellCircle) :
    torusPhysicalOperatorDerivative (periodizedExtension field) order
        (physicalCollarToTorus (point, cell)) =
      ambientHigherDerivative field order
        (assembleSpatialCell point.val (physicalCellRepresentative cell)) := by
  apply continuousMultilinearMap_ext_spatialCellBasis
  intro word
  rw [torusPhysicalOperatorDerivative_basis,
    physicalCollarToTorus_eq_torusCellPoint]
  rw [periodized_mixedDerivative_eq_ambient_on_fundamental
    field word point.val (physicalCellRepresentative cell)
      (physicalCollar_mem_fundamentalIocSquare point)]
  unfold mixedCartesianDerivative
  rw [← ambientHigherDerivative_eq_iteratedFDeriv_ambient]

theorem collarPhysicalOperatorDerivative_point_bound
    {dimension grade order : ℕ} (field : DiskCellClosedJet dimension)
    (upper : order ≤ grade) (point : PhysicalCollarDomain) :
    ‖collarPhysicalOperatorDerivative (periodizedExtension field) order point‖ ≤
      physicalExtensionCNormFactor grade *
        closedPhysicalCNorm field grade := by
  change ‖torusPhysicalOperatorDerivative (periodizedExtension field) order
      (physicalCollarToTorus point)‖ ≤ _
  rw [torusPhysicalOperatorDerivative_periodized_at_collar]
  exact ambientHigherDerivative_norm_le_physicalCNorm
    field grade order point.2 point.1 upper

theorem collarPhysicalOperatorDerivative_norm_bound
    {dimension grade order : ℕ} (field : DiskCellClosedJet dimension)
    (upper : order ≤ grade) :
    ‖collarPhysicalOperatorDerivative (periodizedExtension field) order‖ ≤
      physicalExtensionCNormFactor grade *
        closedPhysicalCNorm field grade := by
  rw [ContinuousMap.norm_le _
    (mul_nonneg (physicalExtensionCNormFactor_nonnegative grade)
      (closedPhysicalCNorm_nonnegative field))]
  intro point
  exact collarPhysicalOperatorDerivative_point_bound field upper point

/-- Exact all-order physical collar estimate for the single P09 extension. -/
theorem collarPhysicalCNorm_periodizedExtension_bound
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (grade : ℕ) :
    collarPhysicalCNorm (periodizedExtension field) grade ≤
      physicalExtensionCNormFactor grade *
        closedPhysicalCNorm field grade := by
  unfold collarPhysicalCNorm
  rw [Finset.max'_le_iff]
  intro value valueMembership
  rw [collarPhysicalDerivativeNorms, Finset.mem_image] at valueMembership
  obtain ⟨order, _, rfl⟩ := valueMembership
  exact collarPhysicalOperatorDerivative_norm_bound field
    (Nat.lt_succ_iff.mp order.isLt)

end Grad.CartesianState
