import ANM3ExplicitMeanState
import ANM4ScalarRotation

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualMeanInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope Grad.NonlinearRange

/-- The ordinary Cartesian divergence of an equivariant stored vector is radial. -/
theorem rotation_planarDiv_zero (field : ClosedJet 3)
    (rotates : rotationJet field = valueMapJet storedQuarterMap field) :
    rotationJet (planarDivJet field) = 0 := by
  rw [planarDivJet, rotationJet_add, rotationJet_valueMap, rotationJet_valueMap,
    rotation_partial_zero, rotation_partial_one, rotates, partialJet_valueMap, partialJet_valueMap]
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simp [sub_eq_add_neg, closedJet_value_add, closedJet_value_neg, valueMapJet_value,
    storedQuarterMap, planarInclusionMap, planarPartMap, quarterValueMap, quarterValueLinear,
    matrixUnit_apply, operatorBasis]

/-- The radial contraction of the same equivariant vector is radial. -/
theorem rotation_radialRow_zero (field : ClosedJet 3)
    (rotates : rotationJet field = valueMapJet storedQuarterMap field) :
    rotationJet (apProductJet radialRowJet field) = 0 := by
  rw [rotationJet_radialRow, rotates]
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simp [closedJet_value_add, apProductJet_value, radialRowJet_value, tangentRowJet_value,
    storedTangentDot, valueMapJet_value, storedQuarterMap, planarInclusionMap, planarPartMap,
    quarterValueMap, quarterValueLinear]

variable {L sigma gamma ell : ℝ}

theorem meanVector_rotation_quarter (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (raw : IsRawMeanSource admissible source) :
    apSmoothRotation admissible 2 (meanVector source.1) =
      apSmoothQuarter L sigma gamma ell (meanVector source.1) :=
  (meanVector_rotation admissible source.1 (meanSource_tangential admissible source compatible raw)).trans
    (meanVector_quarter admissible source.1).symm

theorem meanState_closed_rotation (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (raw : IsRawMeanSource admissible source) (cell : ℤ) :
    rotationJet (apSmoothJet admissible 3 cell (compensatedReconstruct admissible (meanState source))) =
      valueMapJet storedQuarterMap (apSmoothJet admissible 3 cell (compensatedReconstruct admissible (meanState source))) := by
  have planar := (apSmoothRotation_jet admissible (meanVector source.1) cell).symm.trans
    ((congrArg (apSmoothJet admissible 2 cell) (meanVector_rotation_quarter admissible source compatible raw)).trans
      (apSmoothValueMap_jet admissible quarterValueMap (meanVector source.1) cell))
  have included := (congrArg (apSmoothJet admissible 3 cell) (meanState_reconstruct admissible source)).trans
    (apSmoothValueMap_jet admissible planarInclusionMap (meanVector source.1) cell)
  rw [included, rotationJet_valueMap, planar]
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [valueMapJet_value, storedQuarterMap_planar]

theorem meanState_closed_scalar_zero (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (cell : ℤ) :
    valueMapJet toroidalPartMap (apSmoothJet admissible 3 cell (compensatedReconstruct admissible (meanState source))) = 0 := by
  have scalar := (congrArg (apSmoothScalar L sigma gamma ell) (meanState_reconstruct admissible source)).trans
    (apScalar_inclusion admissible (meanVector source.1))
  exact (apSmoothValueMap_jet admissible toroidalPartMap _ cell).symm.trans
    ((congrArg (apSmoothJet admissible 1 cell) scalar).trans (map_zero _))

theorem meanState_divergence_mean (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (raw : IsRawMeanSource admissible source) (cell : ℤ) :
    angularClosedJet 0 (apSmoothJet admissible 1 cell
      (apSmoothDiv admissible (compensatedReconstruct admissible (meanState source)))) =
      apSmoothJet admissible 1 cell (apSmoothDiv admissible (compensatedReconstruct admissible (meanState source))) := by
  have law := (apSmoothDiv_jet admissible (compensatedReconstruct admissible (meanState source)) cell).trans
    ((congrArg (fun scalar : ClosedJet 1 => planarDivJet
      (apSmoothJet admissible 3 cell (compensatedReconstruct admissible (meanState source))) +
        seedScaledFrequency L ell cell • scalar)
      (meanState_closed_scalar_zero admissible source cell)).trans (by rw [smul_zero, add_zero]))
  exact (congrArg (fun jet : ClosedJet 1 => angularClosedJet 0 jet = jet) law).mpr
    (scalarMean_of_rotation_zero _
      (rotation_planarDiv_zero _ (meanState_closed_rotation admissible source compatible raw cell)))

theorem meanState_radial_mean (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (raw : IsRawMeanSource admissible source) (cell : ℤ) :
    angularClosedJet 0 (apSmoothJet admissible 1 cell
      (apSmoothRadial admissible (compensatedReconstruct admissible (meanState source)))) =
      apSmoothJet admissible 1 cell (apSmoothRadial admissible (compensatedReconstruct admissible (meanState source))) := by
  have law := apSmoothFixedJet_jet admissible radialRowJet
    (compensatedReconstruct admissible (meanState source)) cell
  exact (congrArg (fun jet : ClosedJet 1 => angularClosedJet 0 jet = jet) law).mpr
    (scalarMean_of_rotation_zero _
      (rotation_radialRow_zero _ (meanState_closed_rotation admissible source compatible raw cell)))

theorem meanState_determinant (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (raw : IsRawMeanSource admissible source) : circularDeterminant admissible (meanState source) = 0 := by
  have projected : apSmoothRemoveMean L sigma gamma ell 1
      (apSmoothDiv admissible (compensatedReconstruct admissible (meanState source))) = 0 := by
    apply apSmoothJet_ext admissible
    intro cell
    have mean := meanState_divergence_mean admissible source compatible raw cell
    exact (apSmoothRemoveMean_jet admissible _ cell).trans
      ((congrArg (fun jet : ClosedJet 1 =>
        apSmoothJet admissible 1 cell (apSmoothDiv admissible (compensatedReconstruct admissible (meanState source))) - jet)
        mean).trans ((sub_self _).trans (map_zero (apSmoothJet admissible 1 cell)).symm))
  exact (congrArg (fun value : APSmooth L sigma gamma ell 1 => -value) projected).trans neg_zero

/-- All three literal interior rows equal the actual compatible raw-zero source. -/
theorem meanState_rows (admissible : Admissible L sigma gamma ell)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (raw : IsRawMeanSource admissible source) : circularRows admissible (meanState source) = source := by
  apply Prod.ext
  · exact meanState_force admissible source compatible raw
  · apply Prod.ext
    · exact (meanState_determinant admissible source compatible raw).trans
        (meanSource_scalars_zero admissible source compatible raw).1.symm
    · exact (meanState_third admissible source).trans
        (meanSource_scalars_zero admissible source compatible raw).2.symm

end Grad.ActualMeanInverse
