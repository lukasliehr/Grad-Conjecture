import BL39Reality

noncomputable section

open Set MeasureTheory
open scoped BigOperators Interval Topology

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints
open Grad.GaugeCoefficients.Radial

theorem angularContinuousIntegrand_continuous {dimension : ℕ} (mode : ℤ) (point : ClosedDisk)
    (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    Continuous (fun angle : ℝ => angularCharacter mode angle • field (rotatedPoint angle point)) := by
  have rotatedContinuous : Continuous (fun angle : ℝ => rotatedPoint angle point) := by
    apply continuous_induced_rng.mpr
    change Continuous (fun angle : ℝ => planeRotation angle point.val)
    unfold planeRotation
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    fun_prop
  exact (angularCharacter_smooth mode).continuous.smul (field.continuous.comp rotatedContinuous)

/-- The literal N1 angular evaluation at one disk point, as a continuous
linear functional on continuous fields, with norm at most one. -/
def angularValueLinear (dimension : ℕ) (mode : ℤ) (point : ClosedDisk) :
    C(ClosedDisk, ComplexEuclidean dimension) →ₗ[ℂ] ComplexEuclidean dimension where
  toFun field := (2 * Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi,
    angularCharacter mode angle • field (rotatedPoint angle point)
  map_add' first second := by
    simp only [ContinuousMap.add_apply, smul_add]
    rw [intervalIntegral.integral_add
      ((angularContinuousIntegrand_continuous mode point first).intervalIntegrable _ _)
      ((angularContinuousIntegrand_continuous mode point second).intervalIntegrable _ _), smul_add]
  map_smul' scalar field := by
    simp only [ContinuousMap.smul_apply, RingHom.id_apply]
    have commuted : ∀ angle : ℝ,
        angularCharacter mode angle • (scalar • field (rotatedPoint angle point)) =
          scalar • (angularCharacter mode angle • field (rotatedPoint angle point)) :=
      fun angle => smul_comm _ _ _
    simp_rw [commuted]
    rw [intervalIntegral.integral_smul]
    exact smul_comm _ _ _

theorem angularValueLinear_norm_le {dimension : ℕ} (mode : ℤ) (point : ClosedDisk)
    (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    ‖angularValueLinear dimension mode point field‖ ≤ ‖field‖ := by
  have twoPiPos : (0 : ℝ) < 2 * Real.pi := by positivity
  have integralBound : ‖∫ angle in (0 : ℝ)..2 * Real.pi,
      angularCharacter mode angle • field (rotatedPoint angle point)‖ ≤
        ‖field‖ * |2 * Real.pi - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro angle _
    rw [norm_smul, angularCharacter_norm, one_mul]
    exact field.norm_coe_le_norm _
  change ‖(2 * Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi,
    angularCharacter mode angle • field (rotatedPoint angle point)‖ ≤ ‖field‖
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < (2 * Real.pi)⁻¹)]
  calc (2 * Real.pi)⁻¹ * ‖∫ angle in (0 : ℝ)..2 * Real.pi,
      angularCharacter mode angle • field (rotatedPoint angle point)‖
      ≤ (2 * Real.pi)⁻¹ * (‖field‖ * |2 * Real.pi - 0|) :=
        mul_le_mul_of_nonneg_left integralBound (by positivity)
    _ = ‖field‖ := by
        rw [sub_zero, abs_of_pos twoPiPos, mul_comm ‖field‖, ← mul_assoc,
          inv_mul_cancel₀ twoPiPos.ne', one_mul]

def angularValueFunctional (dimension : ℕ) (mode : ℤ) (point : ClosedDisk) :
    C(ClosedDisk, ComplexEuclidean dimension) →L[ℂ] ComplexEuclidean dimension :=
  LinearMap.mkContinuous (angularValueLinear dimension mode point) 1 (fun field => by
    rw [one_mul]
    exact angularValueLinear_norm_le mode point field)

theorem angularValueFunctional_jet {dimension : ℕ} (mode : ℤ) (point : ClosedDisk)
    (field : ClosedJet dimension) :
    angularValueFunctional dimension mode point field.value =
      (angularClosedJet mode field).value point := by
  rw [angularClosedJet_value]
  rfl

/-- The single boundary mode is an exact rotation character: its angular
projection survives only at the matching angular frequency. -/
theorem angularClosedJet_boundaryModeJet_value {dimension : ℕ} (mode angular cell : ℤ)
    (value : ComplexEuclidean dimension) (point : ClosedDisk) :
    (angularClosedJet mode (boundaryModeJet (angular, cell) value)).value point =
      if mode = angular then boundaryKernel (angular, cell) point.val • value else 0 := by
  rw [angularClosedJet_value]
  have integrandLaw : ∀ angle : ℝ,
      angularCharacter mode angle • (boundaryModeJet (angular, cell) value).value (rotatedPoint angle point) =
        angularCharacter (mode - angular) angle • (boundaryKernel (angular, cell) point.val • value) := by
    intro angle
    rw [boundaryModeJet_value, boundaryKernel_rotated, smul_smul, smul_smul]
    congr 1
    have cellAsCharacter : cellExponential angular angle = angularCharacter (-angular) angle := by
      unfold angularCharacter
      rw [neg_neg]
    rw [← mul_assoc, cellAsCharacter, angularCharacter_mul, ← sub_eq_add_neg]
  simp_rw [integrandLaw]
  rw [angularCharacter_normalized_integral]
  by_cases equal : mode = angular
  · rw [if_pos (sub_eq_zero.mpr equal), if_pos equal]
  · rw [if_neg (fun h => equal (sub_eq_zero.mp h)), if_neg equal]

/-- High-angular boundary data produce a lift with no low angular modes:
every angular projection of absolute frequency at most two vanishes. -/
theorem boundaryLift_high_support {dimension : ℕ} (parameters : PhaseParameters)
    (values : BoundaryCore parameters dimension) (highSupport : HighBoundarySupport parameters values)
    (mode : ℤ) (modeSmall : |mode| ≤ 2) (cell : ℤ) :
    angularClosedJet mode ((boundaryLift parameters values).1 cell) = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have valueSeries : HasSum
      (fun angular : ℤ => (boundaryModeJet (angular, cell) (values.1 (angular, cell))).value)
      (((boundaryLift parameters values).1 cell).value) := by
    simpa only [closedDerivative_zero_order] using
      boundaryLift_angular_derivative_hasSum parameters values 0 emptyCartesianWord cell
  have termZero : ∀ angular : ℤ, angularValueFunctional dimension mode point
      ((boundaryModeJet (angular, cell) (values.1 (angular, cell))).value) = 0 := by
    intro angular
    rw [angularValueFunctional_jet, angularClosedJet_boundaryModeJet_value]
    by_cases equal : mode = angular
    · have valueZero : values.1 (angular, cell) = 0 :=
        highSupport (angular, cell) (by rw [← equal]; exact modeSmall)
      rw [if_pos equal, valueZero, smul_zero]
    · rw [if_neg equal]
  have projectionValue : (angularClosedJet mode ((boundaryLift parameters values).1 cell)).value point = 0 := by
    rw [← angularValueFunctional_jet]
    have functionalSeries := (angularValueFunctional dimension mode point).hasSum valueSeries
    have zeroSeries : HasSum (fun _ : ℤ => (0 : ComplexEuclidean dimension))
        (angularValueFunctional dimension mode point (((boundaryLift parameters values).1 cell).value)) := by
      simpa only [termZero] using functionalSeries
    exact zeroSeries.unique hasSum_zero
  rw [projectionValue]
  simp

end Grad.BoundaryLift
