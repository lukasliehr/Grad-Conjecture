import AXJ9ProjectionGoal

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 400000

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.NonlinearQuotientBounds Grad.QuotientProjection Grad.ChartAxisLift
open Grad.RepresentedKernel.SpatialProduct

variable {parameters : PhaseParameters} {dimension : ℕ}

/-- A fixed radial M28 value lift, obtained by averaging the accepted bump.
The generic ContDiffBump API supplies symmetry, not rotation invariance.
This preserves the fixed support, normalization and scaled-profile bounds. -/
def radialValueInsertion : Grad.AxisCore.AxisSmoothCore parameters dimension →ₗ[ℂ]
    ACore parameters dimension :=
  (angularCore parameters 0).comp insertZero

/-- The same radial profile times the indicated Cartesian coordinate. -/
def radialFirstInsertion (coordinate : Fin 2) :
    Grad.AxisCore.AxisSmoothCore parameters dimension →ₗ[ℂ] ACore parameters dimension :=
  (Grad.NonlinearQuotientBounds.coordinateCore parameters coordinate).comp radialValueInsertion

theorem radialValueInsertion_mode (mode : ℤ)
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) :
    angularCore parameters mode (radialValueInsertion data) =
      if mode = 0 then radialValueInsertion data else 0 := by
  change angularCore parameters mode (angularCore parameters 0 (insertZero data)) = _
  rw [angularCore_projection]
  split_ifs with equal
  · subst mode
    rfl
  · rfl

theorem traceZero_radialValueInsertion
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) :
    traceZero (radialValueInsertion data) = data := by
  apply Subtype.ext
  funext cell
  change originValue (angularClosedJet 0 (profileJetZero cell (data.val cell))) = data.val cell
  rw [angularJet_zero_originValue, profileJetZero_originValue]

theorem traceFirst_radialValueInsertion (coordinate : Fin 2)
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) :
    traceFirst coordinate (radialValueInsertion data) = 0 := by
  apply Subtype.ext
  funext cell
  exact angularJet_zero_originPartial coordinate (profileJetZero cell (data.val cell))

theorem traceZero_radialFirstInsertion (coordinate : Fin 2)
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) :
    traceZero (radialFirstInsertion coordinate data) = 0 := by
  apply Subtype.ext
  funext cell
  exact coordinateJet_originValue coordinate ((radialValueInsertion data).val cell)

theorem traceFirst_radialFirstInsertion (direction coordinate : Fin 2)
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) :
    traceFirst direction (radialFirstInsertion coordinate data) =
      if direction = coordinate then data else 0 := by
  apply Subtype.ext
  funext cell
  change originPartial direction (coordinateJet coordinate ((radialValueInsertion data).val cell)) = _
  rw [coordinateJet_originPartial]
  have value := congrFun (congrArg Subtype.val (traceZero_radialValueInsertion data)) cell
  change originValue ((radialValueInsertion data).val cell) = data.val cell at value
  rw [value]
  split_ifs <;> rfl

theorem radialFirstInsertion_mean (coordinate : Fin 2)
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) :
    angularCore parameters 0 (radialFirstInsertion coordinate data) = 0 := by
  have positive := radialValueInsertion_mode (1 : ℤ) data
  have negative := radialValueInsertion_mode (-1 : ℤ) data
  norm_num only [show (1 : ℤ) ≠ 0 by decide, show (-1 : ℤ) ≠ 0 by decide, if_false] at positive negative
  apply Subtype.ext
  funext cell
  have plus := congrFun (congrArg Subtype.val positive) cell
  have minus := congrFun (congrArg Subtype.val negative) cell
  change angularClosedJet 1 ((radialValueInsertion data).val cell) = 0 at plus
  change angularClosedJet (-1) ((radialValueInsertion data).val cell) = 0 at minus
  change angularClosedJet 0 (coordinateJet coordinate ((radialValueInsertion data).val cell)) = 0
  fin_cases coordinate
  · change angularClosedJet 0 (coordinateJet 0 ((radialValueInsertion data).val cell)) = 0
    rw [angular_coordinateJet_zero]
    norm_num only [Int.zero_sub, neg_zero, zero_add] 
    rw [minus, plus, Grad.Cor18.coordinateMultiplyJet_zero_jet,
      Grad.Cor18.coordinateMultiplyJet_zero_jet, add_zero, smul_zero]
  · change angularClosedJet 0 (coordinateJet 1 ((radialValueInsertion data).val cell)) = 0
    rw [angular_coordinateJet_one]
    norm_num only [Int.zero_sub, neg_zero, zero_add]
    rw [minus, plus, Grad.Cor18.coordinateMultiplyJet_zero_jet,
      Grad.Cor18.coordinateMultiplyJet_zero_jet, smul_zero, smul_zero, add_zero]

end Grad.FlatSourceProjection
