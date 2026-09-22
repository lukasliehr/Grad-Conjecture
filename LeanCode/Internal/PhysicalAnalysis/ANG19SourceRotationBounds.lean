import ANG18UnweightedSourceRows

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace Grad.CircularHighWeak
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange
open Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Compensated (partialJetLinear weightedPartialDerivative_bound apProductJet_coordinate)

theorem unitPartial_bound (grade : ℕ) (coordinate : Fin 2) (field : ClosedJet 1) :
    ‖unitSobolevRow grade (partialJet coordinate field)‖ ≤
      Real.sqrt (Fintype.card (DerivativeIndex grade)) * ‖unitSobolevRow (grade + 1) field‖ := by
  apply apRow_norm_bound_of_coordinates _ _ (norm_nonneg _)
  intro index
  have bound := weightedPartialDerivative_bound (grade := grade) 1 0 0 1 0 coordinate field index
  rw [unweightedJet] at bound
  simp only [show scaledCellWeight 1 1 0 = 1 by norm_num [scaledCellWeight], one_pow, one_mul] at bound
  exact (congrArg norm (unitSobolevRow_coordinate grade (partialJet coordinate field) index)).le.trans bound

def unitCoordinateConstant (grade : ℕ) (coordinate : Fin 2) : ℝ :=
  unitProductConstant grade (coordinateOperatorJet coordinate (ContinuousLinearMap.id ℂ (ComplexEuclidean 1)))

theorem unitCoordinateConstant_nonnegative (grade : ℕ) (coordinate : Fin 2) : 0 ≤ unitCoordinateConstant grade coordinate :=
  unitProductConstant_nonnegative _ _

theorem unitCoordinate_bound (grade : ℕ) (coordinate : Fin 2) (field : ClosedJet 1) :
    ‖unitSobolevRow grade (coordinateJet coordinate field)‖ ≤ unitCoordinateConstant grade coordinate * ‖unitSobolevRow grade field‖ :=
  (congrArg (fun jet : ClosedJet 1 => ‖unitSobolevRow grade jet‖) (apProductJet_coordinate coordinate field)).symm.le.trans
    (unitProduct_bound grade _ field)

def unitRotationConstant (grade : ℕ) : ℝ :=
  (unitCoordinateConstant grade 0 + unitCoordinateConstant grade 1) * Real.sqrt (Fintype.card (DerivativeIndex grade))

theorem unitRotationConstant_nonnegative (grade : ℕ) : 0 ≤ unitRotationConstant grade :=
  mul_nonneg (add_nonneg (unitCoordinateConstant_nonnegative _ _) (unitCoordinateConstant_nonnegative _ _)) (Real.sqrt_nonneg _)

/-- Literal rotation loses exactly one ordinary Cartesian Sobolev grade. -/
theorem unitRotation_bound (grade : ℕ) (field : ClosedJet 1) :
    ‖unitSobolevRow grade (rotationJet field)‖ ≤ unitRotationConstant grade * ‖unitSobolevRow (grade + 1) field‖ := by
  have subtract := (unitSobolevRow grade).map_sub (coordinateJet 0 (partialJet 1 field)) (coordinateJet 1 (partialJet 0 field))
  have first := (unitCoordinate_bound grade 0 (partialJet 1 field)).trans
    (mul_le_mul_of_nonneg_left (unitPartial_bound grade 1 field) (unitCoordinateConstant_nonnegative grade 0))
  have second := (unitCoordinate_bound grade 1 (partialJet 0 field)).trans
    (mul_le_mul_of_nonneg_left (unitPartial_bound grade 0 field) (unitCoordinateConstant_nonnegative grade 1))
  exact (congrArg norm subtract).le.trans ((norm_sub_le _ _).trans ((add_le_add first second).trans_eq (by
    change _ = ((unitCoordinateConstant grade 0 + unitCoordinateConstant grade 1) * _) * _
    ring)))

def coordinateJetLinear (coordinate : Fin 2) : ClosedJet 1 →ₗ[ℂ] ClosedJet 1 where
  toFun := coordinateJet coordinate
  map_add' first second := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact smul_add (point.val coordinate) (first.value point) (second.value point)
  map_smul' scalar field := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact smul_comm (point.val coordinate) scalar (field.value point)

def rotationJetLinear : ClosedJet 1 →ₗ[ℂ] ClosedJet 1 :=
  (coordinateJetLinear 0).comp (partialJetLinear 1 1) - (coordinateJetLinear 1).comp (partialJetLinear 1 0)

theorem rotationJetLinear_apply (field : ClosedJet 1) : rotationJetLinear field = rotationJet field := rfl

def rotationJetPower : (order : ℕ) → ClosedJet 1 →ₗ[ℂ] ClosedJet 1
  | 0 => LinearMap.id
  | order + 1 => (rotationJetPower order).comp rotationJetLinear

def unitRotationPowerConstant : ℕ → ℝ
  | 0 => 1
  | order + 1 => unitRotationPowerConstant order * unitRotationConstant order

theorem unitRotationPowerConstant_nonnegative (order : ℕ) : 0 ≤ unitRotationPowerConstant order := by
  induction order with
  | zero => exact zero_le_one
  | succ order previous => exact mul_nonneg previous (unitRotationConstant_nonnegative order)

theorem unitRotationPower_bound (order : ℕ) (field : ClosedJet 1) :
    ‖unitSobolevRow 0 (rotationJetPower order field)‖ ≤ unitRotationPowerConstant order * ‖unitSobolevRow order field‖ := by
  induction order generalizing field with
  | zero => exact (one_mul _).symm.le
  | succ order previous =>
    have bound := (previous (rotationJet field)).trans
      (mul_le_mul_of_nonneg_left (unitRotation_bound order field) (unitRotationPowerConstant_nonnegative order))
    exact bound.trans_eq (mul_assoc _ _ _).symm

theorem rotationJetPower_L2_bound (order : ℕ) (field : ClosedJet 1) :
    ‖closedL2Core (rotationJetPower order field)‖ ≤ unitRotationPowerConstant order * ‖unitSobolevRow order field‖ := by
  have coordinate := unitSobolev_derivative_bound 0 (rotationJetPower order field) (zeroGradeIndex 0)
  change ‖closedContinuousToDiskL2 (closedMultiDerivative (rotationJetPower order field) (0, 0))‖ ≤ _ at coordinate
  rw [closedMultiDerivative_zero] at coordinate
  exact coordinate.trans (unitRotationPower_bound order field)

end Grad.CircularHighWeak
