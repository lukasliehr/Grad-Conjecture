import AXF1RadialProfiles

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 400000

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.NonlinearQuotientBounds Grad.QuotientProjection Grad.ChartAxisLift

variable {parameters : PhaseParameters} {dimension : ℕ}

theorem radialFirstInsertion_zero_formula
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) :
    radialFirstInsertion 0 data = (1 / 2 : ℂ) •
      (angularCore parameters 1 (insertOne 0 data + Complex.I • insertOne 1 data) +
        angularCore parameters (-1) (insertOne 0 data - Complex.I • insertOne 1 data)) := by
  apply Subtype.ext
  funext cell
  change coordinateJet 0 (angularClosedJet 0 (profileJetZero cell (data.val cell))) =
    (1 / 2 : ℂ) •
      (angularClosedJet 1 (profileJetOne 0 cell (data.val cell) + Complex.I • profileJetOne 1 cell (data.val cell)) +
        angularClosedJet (-1) (profileJetOne 0 cell (data.val cell) - Complex.I • profileJetOne 1 cell (data.val cell)))
  have plus := coordinate_profile cell (data.val cell) 1
  have minus := coordinate_profile cell (data.val cell) (-1)
  simp only [Complex.ofReal_one, mul_one] at plus
  simp only [Complex.ofReal_neg, Complex.ofReal_one, mul_neg, mul_one,
    neg_smul, ← sub_eq_add_neg] at minus
  rw [plus, minus, angularClosedJet_z, angularClosedJet_zbar]
  norm_num only [Int.sub_self, neg_add_cancel]
  rw [coordinateJet_eq_realCoordinateJet, Grad.Cor18.realCoordinateJet_zero_eq]

theorem radialFirstInsertion_one_formula
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) :
    radialFirstInsertion 1 data =
      (-(Complex.I / 2)) • angularCore parameters 1 (insertOne 0 data + Complex.I • insertOne 1 data) +
      (Complex.I / 2) • angularCore parameters (-1) (insertOne 0 data - Complex.I • insertOne 1 data) := by
  apply Subtype.ext
  funext cell
  change coordinateJet 1 (angularClosedJet 0 (profileJetZero cell (data.val cell))) =
    (-(Complex.I / 2)) •
      angularClosedJet 1 (profileJetOne 0 cell (data.val cell) + Complex.I • profileJetOne 1 cell (data.val cell)) +
    (Complex.I / 2) •
      angularClosedJet (-1) (profileJetOne 0 cell (data.val cell) - Complex.I • profileJetOne 1 cell (data.val cell))
  have plus := coordinate_profile cell (data.val cell) 1
  have minus := coordinate_profile cell (data.val cell) (-1)
  simp only [Complex.ofReal_one, mul_one] at plus
  simp only [Complex.ofReal_neg, Complex.ofReal_one, mul_neg, mul_one,
    neg_smul, ← sub_eq_add_neg] at minus
  rw [plus, minus, angularClosedJet_z, angularClosedJet_zbar]
  norm_num only [Int.sub_self, neg_add_cancel]
  rw [coordinateJet_eq_realCoordinateJet, Grad.Cor18.realCoordinateJet_one_eq]

end Grad.FlatSourceProjection
