import ANM2ActualMeanSource
import ANG13RotationSpectrum

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualMeanInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.NonlinearRange Grad.NonlinearDivision Grad.CircularHighWeak
open Grad.NonlinearQuotientBounds (coordinateJet coordinateJet_value partialJet_closedDerivative)

/-- Scalar zero rotation is actual angular mode zero, proved by the
accepted Fourier completeness on the full disk. -/
theorem scalarMean_of_rotation_zero (field : ClosedJet 1) (zero : rotationJet field = 0) :
    angularClosedJet 0 field = field := by
  apply closedL2Core_injective
  apply diskFourierIsometry.injective
  apply lp.ext
  funext mode
  change diskMode mode (closedL2Core (angularClosedJet 0 field)) = diskMode mode (closedL2Core field)
  rw [diskMode_core, diskMode_core, angularClosedJet_projection]
  by_cases same : mode = 0
  · subst mode
    rw [if_pos rfl]
  · rw [if_neg same]
    have coefficient := angular_rotationJet mode field
    rw [zero] at coefficient
    change angularClosedJetLinear 1 mode 0 = _ at coefficient
    rw [map_zero] at coefficient
    have absent : angularClosedJet mode field = 0 :=
      (smul_eq_zero.mp coefficient.symm).resolve_left
        (mul_ne_zero Complex.I_ne_zero (by exact_mod_cast same))
    rw [absent]

/-- The genuine mixed Cartesian derivative jets commute; the accepted derivative
word-to-multiindex identity pays for this Cartesian symmetry. -/
theorem partialJets_commute {dimension : ℕ} (first second : Fin 2) (field : ClosedJet dimension) :
    partialJet first (partialJet second field) = partialJet second (partialJet first field) := by
  apply closedJet_eq_of_value_eq
  change closedDerivative (Grad.NonlinearQuotientBounds.partialJet second field) 1 (fun _ => first) =
    closedDerivative (Grad.NonlinearQuotientBounds.partialJet first field) 1 (fun _ => second)
  rw [partialJet_closedDerivative, partialJet_closedDerivative,
    closedDerivative_eq_closedMultiDerivative_wordIndex, closedDerivative_eq_closedMultiDerivative_wordIndex]
  congr 1
  fin_cases first <;> fin_cases second <;> decide

theorem partial_rotation_value {dimension : ℕ} (field : ClosedJet dimension)
    (direction : Fin 2) (point : ClosedDisk) :
    (partialJet direction (rotationJet field)).value point =
      spatialBasis direction 0 • (partialJet 1 field).value point +
        point.val 0 • (partialJet direction (partialJet 1 field)).value point -
      (spatialBasis direction 1 • (partialJet 0 field).value point +
        point.val 1 • (partialJet direction (partialJet 0 field)).value point) := by
  change (partialJetLinear dimension direction
    (coordinateJet 0 (partialJet 1 field) - coordinateJet 1 (partialJet 0 field))).value point = _
  rw [map_sub, partialJetLinear_apply, partialJetLinear_apply]
  simp only [sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    ContinuousMap.add_apply, ContinuousMap.neg_apply]
  rw [partialJet_coordinate_value, partialJet_coordinate_value]

theorem rotation_partial_zero {dimension : ℕ} (field : ClosedJet dimension) :
    rotationJet (partialJet 0 field) = partialJet 0 (rotationJet field) - partialJet 1 field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    ContinuousMap.add_apply, ContinuousMap.neg_apply]
  rw [partial_rotation_value]
  rw [partialJets_commute 0 1]
  simp only [rotationJet, sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    ContinuousMap.add_apply, ContinuousMap.neg_apply, coordinateJet_value]
  simp [spatialBasis, Grad.NonlinearQuotientBounds.partialJet, partialJet]
  module

theorem rotation_partial_one {dimension : ℕ} (field : ClosedJet dimension) :
    rotationJet (partialJet 1 field) = partialJet 1 (rotationJet field) + partialJet 0 field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [closedJet_value_add, ContinuousMap.add_apply, partial_rotation_value]
  rw [partialJets_commute 1 0]
  simp only [rotationJet, sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    ContinuousMap.add_apply, ContinuousMap.neg_apply, coordinateJet_value]
  simp [spatialBasis, Grad.NonlinearQuotientBounds.partialJet, partialJet]
  module

end Grad.ActualMeanInverse
