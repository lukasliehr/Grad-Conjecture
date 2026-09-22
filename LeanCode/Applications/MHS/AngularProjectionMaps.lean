import AngularProjectionL2

noncomputable section

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace Grad.Constraints

open Grad.ClosedJets Grad.CartesianState Grad.PhysicalFamily Grad.GaugeCoefficients.Radial

theorem angularValueIntegrand_continuous {dimension : ℕ} (mode : ℤ)
    (field : ClosedJet dimension) (point : ClosedDisk) :
    Continuous (fun angle => angularCharacter mode angle • field.value (rotatedPoint angle point)) := by
  have rotatedContinuous : Continuous (fun angle : ℝ => rotatedPoint angle point) := by
    apply continuous_induced_rng.mpr
    change Continuous (fun angle : ℝ => planeRotation angle point.val)
    unfold planeRotation
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp
    fun_prop
  have fieldContinuous : Continuous (fun angle : ℝ => field.value (rotatedPoint angle point)) :=
    field.value.continuous.comp rotatedContinuous
  exact (angularCharacter_smooth mode).continuous.smul fieldContinuous

theorem angularClosedJet_add {dimension : ℕ} (mode : ℤ) (first second : ClosedJet dimension) :
    angularClosedJet mode (first + second) = angularClosedJet mode first + angularClosedJet mode second := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change (angularClosedJet mode (first + second)).value point =
    (angularClosedJet mode first).value point + (angularClosedJet mode second).value point
  simp_rw [angularClosedJet_value]
  change ((2 * Real.pi)⁻¹ : ℝ) •
    (∫ angle in (0 : ℝ)..2 * Real.pi,
      angularCharacter mode angle • (first.value (rotatedPoint angle point) +
        second.value (rotatedPoint angle point))) = _
  simp_rw [smul_add]
  rw [intervalIntegral.integral_add
    ((angularValueIntegrand_continuous mode first point).intervalIntegrable _ _)
    ((angularValueIntegrand_continuous mode second point).intervalIntegrable _ _), smul_add]

theorem angularClosedJet_smul {dimension : ℕ} (mode : ℤ) (scalar : ℂ) (field : ClosedJet dimension) :
    angularClosedJet mode (scalar • field) = scalar • angularClosedJet mode field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change (angularClosedJet mode (scalar • field)).value point =
    scalar • (angularClosedJet mode field).value point
  simp_rw [angularClosedJet_value]
  change ((2 * Real.pi)⁻¹ : ℝ) •
    (∫ angle in (0 : ℝ)..2 * Real.pi,
      angularCharacter mode angle • (scalar • field.value (rotatedPoint angle point))) = _
  simp_rw [smul_comm (angularCharacter mode _) scalar]
  rw [intervalIntegral.integral_smul]
  exact smul_comm _ _ _

def angularClosedJetLinear (dimension : ℕ) (mode : ℤ) :
    ClosedJet dimension →ₗ[ℂ] ClosedJet dimension where
  toFun := angularClosedJet mode
  map_add' := angularClosedJet_add mode
  map_smul' := angularClosedJet_smul mode

theorem angularClosedJet_phaseWeighted {dimension : ℕ} (parameters : PhaseParameters)
    (cell mode : ℤ) (field : ClosedJet dimension) :
    angularClosedJet mode (phaseWeightedJet parameters cell field) =
      phaseWeightedJet parameters cell (angularClosedJet mode field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [angularClosedJet_value, phaseWeightedJet_spec, angularClosedJet_value]
  have integrandEquality (angle : ℝ) :
      angularCharacter mode angle •
          (phaseWeightedJet parameters cell field).value (rotatedPoint angle point) =
        cartesianWeight parameters cell point.val •
          (angularCharacter mode angle • field.value (rotatedPoint angle point)) := by
    rw [phaseWeightedJet_spec]
    have weightEquality : cartesianWeight parameters cell (rotatedPoint angle point).val =
        cartesianWeight parameters cell point.val :=
      cartesianWeight_orthogonal parameters cell (planeRotationEquiv angle) point.val
    rw [weightEquality]
    exact smul_comm _ _ _
  simp_rw [integrandEquality]
  rw [intervalIntegral.integral_smul]
  exact smul_comm _ _ _

end Grad.Constraints
