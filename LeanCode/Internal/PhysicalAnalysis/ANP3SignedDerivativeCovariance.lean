import ANP2SmoothAngularModes
import ACE3PureModeEuler

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.RawCircularSectors
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ActualCenterVolterra
open Grad.GaugeCoefficients.Radial Grad.RepresentedKernel.SpatialProduct
open Grad.NonlinearQuotientBounds Grad.NonlinearRange

/-- Actual first Cartesian derivative under a rotation, with both coordinates. -/
theorem orthogonal_first_coordinates {dimension : ℕ} (angle : ℝ) (field : ClosedJet dimension)
    (coordinate : Fin 2) :
    orthogonalDerivative (planeRotationEquiv angle) field 1 (fun _ => coordinate) =
      (planeRotationEquiv angle (Grad.PDEBootstrap.spatialDirection coordinate) 0 : ℂ) •
        (closedDerivative field 1 (fun _ => 0)).comp (orthogonalClosedMap (planeRotationEquiv angle)) +
      (planeRotationEquiv angle (Grad.PDEBootstrap.spatialDirection coordinate) 1 : ℂ) •
        (closedDerivative field 1 (fun _ => 1)).comp (orthogonalClosedMap (planeRotationEquiv angle)) := by
  rw [orthogonalDerivative_eq_sum]
  have words : (Finset.univ : Finset (CartesianWord 1)) = {fun _ => 0, fun _ => 1} := by decide
  rw [words, Finset.sum_pair (by decide : (fun _ : Fin 1 => (0 : Fin 2)) ≠ (fun _ => 1))]
  simp [chainFactor_eq]

theorem signed_rotated_derivative {dimension : ℕ} (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (angle : ℝ) (field : ClosedJet dimension) (point : ClosedDisk) :
    orthogonalDerivative (planeRotationEquiv angle) field 1 (fun _ => 0) point -
      (Complex.I * (sign : ℂ)) • orthogonalDerivative (planeRotationEquiv angle) field 1 (fun _ => 1) point =
      angularCharacter (-sign) angle • (centerDifferential sign field).value (rotatedPoint angle point) := by
  rw [orthogonal_first_coordinates, orthogonal_first_coordinates]
  simp only [ContinuousMap.add_apply, ContinuousMap.smul_apply, ContinuousMap.comp_apply]
  have rotated : orthogonalClosedMap (planeRotationEquiv angle) point = rotatedPoint angle point := by
    apply Subtype.ext
    exact planeRotationEquiv_apply angle point.val
  rw [rotated]
  simp only [centerDifferential, sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    closedJet_value_smul, ContinuousMap.add_apply, ContinuousMap.neg_apply, ContinuousMap.smul_apply]
  change _ = angularCharacter (-sign) angle •
    (closedDerivative field 1 (fun _ => 0) (rotatedPoint angle point) +
      -((Complex.I * (sign : ℂ)) • closedDerivative field 1 (fun _ => 1) (rotatedPoint angle point)))
  apply PiLp.ext
  intro coordinate
  rcases signed with rfl | rfl <;>
    simp [angularCharacter_trig, planeRotationEquiv_apply, planeRotation, Grad.PDEBootstrap.spatialDirection] <;>
    ring_nf <;> simp [Complex.I_sq]

private theorem normalized_difference {E : Type*} [AddCommGroup E] [Module ℝ E]
    [Module ℂ E] [SMulCommClass ℝ ℂ E] (normalization : ℝ) (coefficient : ℂ) (first second : E) :
    normalization • first - coefficient • (normalization • second) =
      normalization • (first - coefficient • second) := by
  rw [smul_sub, smul_comm normalization coefficient]

/-- Twice the signed Wirtinger derivative lowers the angular mode by its sign.
This is an equality of genuine closed jets for arbitrary input, so it also
supplies every boundary and axis derivative and the source projection law. -/
theorem centerDifferential_angular {dimension : ℕ} (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (mode : ℤ) (field : ClosedJet dimension) :
    centerDifferential sign (angularClosedJet mode field) =
      angularClosedJet (mode - sign) (centerDifferential sign field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have integrable (coordinate : Fin 2) : IntegrableOn
      (fun angle => angularCharacter mode angle • orthogonalDerivative
        (planeRotationEquiv angle) field 1 (fun _ => coordinate) point)
      (Icc (0 : ℝ) (2 * Real.pi)) := ((ContinuousMap.evalCLM ℝ point).continuous.comp
        (angularDerivativeFamily_continuous mode field (fun _ : Fin 1 => coordinate))).continuousOn.integrableOn_Icc
  have secondIntegrable : IntegrableOn
      (fun angle => (Complex.I * (sign : ℂ)) • (angularCharacter mode angle • orthogonalDerivative
        (planeRotationEquiv angle) field 1 (fun _ => 1) point)) (Icc (0 : ℝ) (2 * Real.pi)) :=
    ((continuous_const : Continuous (fun _ : ℝ => Complex.I * (sign : ℂ))).smul ((ContinuousMap.evalCLM ℝ point).continuous.comp
      (angularDerivativeFamily_continuous mode field (fun _ : Fin 1 => 1)))).continuousOn.integrableOn_Icc
  simp only [centerDifferential, sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    closedJet_value_smul, ContinuousMap.add_apply, ContinuousMap.neg_apply, ContinuousMap.smul_apply]
  change closedDerivative (angularClosedJet mode field) 1 (fun _ => 0) point -
    (Complex.I * (sign : ℂ)) • closedDerivative (angularClosedJet mode field) 1 (fun _ => 1) point =
    (angularClosedJet (mode - sign) (centerDifferential sign field)).value point
  rw [angularClosedJet_derivative, angularClosedJet_derivative, normalized_difference,
    ← integral_smul, ← integral_sub (integrable 0) secondIntegrable,
    angularClosedJet_value, intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi),
    ← integral_Icc_eq_integral_Ioc]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro angle _
  dsimp only
  rw [smul_comm (Complex.I * (sign : ℂ)) (angularCharacter mode angle), ← smul_sub,
    signed_rotated_derivative sign signed, smul_smul, angularCharacter_mul]
  rfl

/-- Immediate exceptional-sector consumer, using the accepted literal ACE
operator and retaining arbitrary integer input mode. -/
theorem centerDifferential_pure {dimension : ℕ} (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (mode : ℤ) (field : ClosedJet dimension) (pure : angularClosedJet mode field = field) :
    angularClosedJet (mode - sign) (centerDifferential sign field) = centerDifferential sign field :=
  (centerDifferential_angular sign signed mode field).symm.trans (congrArg (centerDifferential sign) pure)

end Grad.RawCircularSectors
