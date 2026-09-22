import GaugeSeedInverse

noncomputable section

set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints

/-- The literal real coordinate functional on the spatial plane. -/
def coordinateLinearMap (coordinate : Fin 2) : SpatialPlane →L[ℝ] ℝ :=
  PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) coordinate

theorem coordinate_list_derivative (mapping : SpatialPlane →L[ℝ] ℝ)
    (direction : Fin 2) (rest : List (Fin 2)) :
    cartesianListDerivative (direction :: rest) mapping =
      fun _ => if rest = [] then mapping (spatialBasis direction) else 0 := by
  induction rest generalizing direction with
  | nil =>
    funext point
    simp [cartesianListDerivative, ContinuousLinearMap.fderiv]
  | cons next tail inductionHypothesis =>
    funext point
    show fderiv ℝ (cartesianListDerivative (next :: tail) mapping) point
      (spatialBasis direction) = _
    rw [inductionHypothesis next]
    simp

theorem coordinate_derivative_bound (coordinate : Fin 2) {rank : ℕ}
    (word : CartesianWord rank) (point : ClosedDisk) :
    ‖cartesianDerivative rank word (coordinateLinearMap coordinate) point.val‖ ≤ 1 := by
  cases rank with
  | zero =>
    change ‖point.val coordinate‖ ≤ 1
    exact (PiLp.norm_apply_le point.val coordinate).trans point.property
  | succ rank =>
    rw [← cartesianListDerivative_ofFn isOpen_univ (rank + 1) word
      (coordinateLinearMap coordinate).contDiff.contDiffOn (mem_univ point.val),
      List.ofFn_succ, coordinate_list_derivative]
    split_ifs
    · change ‖spatialBasis (word 0) coordinate‖ ≤ 1
      exact (PiLp.norm_apply_le (spatialBasis (word 0)) coordinate).trans_eq
        (by simp [spatialBasis, PiLp.norm_single])
    · simp

/-- Multiplication of a closed jet by one literal real coordinate. -/
def realCoordinateJet {dimension : ℕ} (coordinate : Fin 2) (field : ClosedJet dimension) :
    ClosedJet dimension :=
  smoothScalarWeightedJet (coordinateLinearMap coordinate)
    (coordinateLinearMap coordinate).contDiff field

theorem realCoordinateJet_value {dimension : ℕ} (coordinate : Fin 2)
    (field : ClosedJet dimension) (point : ClosedDisk) :
    (realCoordinateJet coordinate field).value point =
      point.val coordinate • field.value point := rfl

theorem realCoordinateJet_add {dimension : ℕ} (coordinate : Fin 2)
    (first second : ClosedJet dimension) :
    realCoordinateJet coordinate (first + second) =
      realCoordinateJet coordinate first + realCoordinateJet coordinate second := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [realCoordinateJet_value, closedJet_value_add, ContinuousMap.add_apply, smul_add]

theorem realCoordinateJet_smul {dimension : ℕ} (coordinate : Fin 2) (scalar : ℂ)
    (field : ClosedJet dimension) :
    realCoordinateJet coordinate (scalar • field) =
      scalar • realCoordinateJet coordinate field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [realCoordinateJet_value, closedJet_value_smul, ContinuousMap.smul_apply]
  rw [smul_comm]

/-- The generic derivative law of a smooth-scalar weighted jet. -/
theorem smoothScalarWeightedJet_closedDerivative {dimension : ℕ}
    (scalar : SpatialPlane → ℝ) (scalarSmooth : ContDiff ℝ ∞ scalar)
    (field : ClosedJet dimension) (order : ℕ) (word : CartesianWord order) :
    closedDerivative (smoothScalarWeightedJet scalar scalarSmooth field) order word =
      smoothScalarDerivativeExtension scalar scalarSmooth field order word := by
  symm
  apply cartesianExtension_unique
  exact smoothScalarDerivativeExtension_spec scalar scalarSmooth field order word

theorem realCoordinateJet_phaseWeighted {dimension : ℕ} (parameters : PhaseParameters)
    (cell : ℤ) (coordinate : Fin 2) (field : ClosedJet dimension) :
    phaseWeightedJet parameters cell (realCoordinateJet coordinate field) =
      realCoordinateJet coordinate (phaseWeightedJet parameters cell field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change cartesianWeight parameters cell point.val •
      (point.val coordinate • field.value point) =
    point.val coordinate • (cartesianWeight parameters cell point.val • field.value point)
  exact smul_comm _ _ _

/-- Pointwise norm domination between continuous closed maps gives disk `L²`
norm domination. -/
theorem closedContinuousToDiskL2_norm_le_of_pointwise {dimension : ℕ}
    (first second : ContinuousMap ClosedDisk (ComplexEuclidean dimension))
    (bound : ∀ point : ClosedDisk, ‖first point‖ ≤ ‖second point‖) :
    ‖closedContinuousToDiskL2 first‖ ≤ ‖closedContinuousToDiskL2 second‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  apply ENNReal.toReal_mono (Lp.eLpNorm_ne_top (closedContinuousToDiskL2 second))
  apply eLpNorm_mono_ae
  filter_upwards [closedContinuousToDiskL2_ae first, closedContinuousToDiskL2_ae second,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point firstAt secondAt membership
  rw [firstAt, secondAt,
    show closedDiskLift first point = first ⟨point, openDiskMembershipClosed point membership⟩
      by simp [closedDiskLift, openDiskMembershipClosed point membership],
    show closedDiskLift second point = second ⟨point, openDiskMembershipClosed point membership⟩
      by simp [closedDiskLift, openDiskMembershipClosed point membership]]
  exact bound _

/-- One Leibniz summand of a coordinate-multiplied derivative. -/
def coordinateLeibnizTerm {dimension : ℕ} (coordinate : Fin 2) (field : ClosedJet dimension)
    {order : ℕ} (word : CartesianWord order) (selected : Finset (Fin order)) :
    ContinuousMap ClosedDisk (ComplexEuclidean dimension) where
  toFun point := smoothScalarDerivativeFactor (coordinateLinearMap coordinate)
      (coordinateLinearMap coordinate).contDiff order word selected point •
    closedDerivative field selectedᶜ.card
      (Grad.AnalyticWeights.Higher.subword word selectedᶜ) point
  continuous_toFun := (smoothScalarDerivativeFactor (coordinateLinearMap coordinate)
      (coordinateLinearMap coordinate).contDiff order word selected).continuous.smul
    (closedDerivative field selectedᶜ.card
      (Grad.AnalyticWeights.Higher.subword word selectedᶜ)).continuous

theorem coordinateExtension_eq_sum {dimension : ℕ} (coordinate : Fin 2)
    (field : ClosedJet dimension) {order : ℕ} (word : CartesianWord order) :
    smoothScalarDerivativeExtension (coordinateLinearMap coordinate)
        (coordinateLinearMap coordinate).contDiff field order word =
      ∑ selected : Finset (Fin order), coordinateLeibnizTerm coordinate field word selected := by
  apply ContinuousMap.ext
  intro point
  rw [ContinuousMap.sum_apply]
  rfl

theorem coordinateLeibnizTerm_L2_le {dimension : ℕ} (coordinate : Fin 2)
    (field : ClosedJet dimension) {order : ℕ} (word : CartesianWord order)
    (selected : Finset (Fin order)) :
    ‖closedContinuousToDiskL2 (coordinateLeibnizTerm coordinate field word selected)‖ ≤
      ‖closedContinuousToDiskL2 (closedDerivative field selectedᶜ.card
        (Grad.AnalyticWeights.Higher.subword word selectedᶜ))‖ := by
  apply closedContinuousToDiskL2_norm_le_of_pointwise
  intro point
  change ‖smoothScalarDerivativeFactor (coordinateLinearMap coordinate)
      (coordinateLinearMap coordinate).contDiff order word selected point •
    closedDerivative field selectedᶜ.card
      (Grad.AnalyticWeights.Higher.subword word selectedᶜ) point‖ ≤ _
  rw [norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (coordinate_derivative_bound coordinate
      (Grad.AnalyticWeights.Higher.subword word selected) point)

end Grad.Constraints.Gauges
