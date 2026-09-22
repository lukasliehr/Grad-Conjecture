import ACE15ClosedCartesianAlgebra

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.NonlinearDivision (laplacianJet)

theorem centerPartial_neg {dimension : ℕ} (direction : Fin 2) (field : ClosedJet dimension) :
    partialJet direction (-field) = -partialJet direction field :=
  (Grad.GaugeCoefficients.Physical.Compensated.partialJetLinear dimension direction).map_neg field

theorem centerCoordinate_neg {dimension : ℕ} (coordinate : Fin 2) (field : ClosedJet dimension) :
    coordinateJet coordinate (-field) = -coordinateJet coordinate field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [coordinateJet_value, closedJet_value_neg, ContinuousMap.neg_apply,
    closedJet_value_neg, ContinuousMap.neg_apply, coordinateJet_value]
  exact smul_neg (point.val coordinate) (field.value point)

/-- Exact Cartesian identity before radiality is imposed. The only signed
coordinate hypothesis is m = 1 or m = -1. -/
theorem centerLaplacian_cartesian {dimension : ℕ} (mode : ℤ) (center : mode = 1 ∨ mode = -1)
    (field : ClosedJet dimension) :
    laplacianJet (coordinateMultiplyJet (mode : ℝ) (radiusPowerJet 1 field)) =
      coordinateMultiplyJet (mode : ℝ)
        (shiftedEulerJet 1 (shiftedEulerJet 3 field) + rotationJet (rotationJet field) +
          (2 * Complex.I * (mode : ℂ)) • rotationJet field) := by
  simp only [laplacianJet, centerCoordinate_decomposition, radiusPower_one_decomposition,
    shiftedEulerJet, eulerJet, rotationJet, sub_eq_add_neg,
    centerPartial_add, centerPartial_smul, centerPartial_neg, centerPartial_coordinate,
    centerCoordinate_add, centerCoordinate_smul, centerCoordinate_neg]
  simp only [centerPartial_commute 1 0]
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  rcases center with rfl | rfl <;>
    simp [closedJet_value_add, closedJet_value_smul, closedJet_value_neg,
      coordinateJet_value, PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply,
      Complex.real_smul, spatialBasis] <;> ring_nf <;> simp only [Complex.I_sq] <;> ring

end Grad.ActualCenterVolterra
