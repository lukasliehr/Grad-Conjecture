import ANR43CompletedGradientPairing

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace Grad.BoundaryLift
open Grad.GaugeCoefficients.Radial

private theorem character_coefficient_zero (mode frequency : ℤ) (different : frequency ≠ mode)
    (vector : ComplexEuclidean 1) :
    angularCoefficient (fun angle => cellExponential mode angle • vector) frequency = 0 := by
  have functions : (fun angle => cellExponential mode angle • vector) =
      (fun angle : ℝ => fourier mode (angle : CellCircle) • vector) := by
    funext angle
    rw [show fourier mode (angle : CellCircle) = cellExponential mode angle from cellCharacter_coe _ _]
  have circle := angularCoefficient_circle (fun angle : CellCircle => fourier mode angle • vector) frequency
  have zero : fourierCoeff (fun angle : CellCircle => fourier mode angle • vector) frequency = 0 := by
    rw [fourierCoeff_scalar_smul_const, fourierCoeff_fourier]
    simp [different]
  exact (congrArg (fun field : ℝ → ComplexEuclidean 1 => angularCoefficient field frequency) functions).trans
    (circle.trans zero)

private theorem character_radial_other (mode frequency : ℤ) (different : frequency ≠ mode)
    (vector : ComplexEuclidean 1) (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test)
    (away : (0 : ℝ) ∉ tsupport test) (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1) :
    radialCoefficientJet (originalPolarValue (boundaryCharacterJet mode vector test smooth away)) frequency 0 radius = 0 := by
  let jet := boundaryCharacterJet mode vector test smooth away
  have functions : (fun angle => originalPolarValue jet (radius, angle)) =
      (fun angle => cellExponential mode angle • (test radius • vector)) := by
    funext angle
    rw [originalPolarValue_closed jet radius angle positive.le bounded]
    change radialTestLift mode vector test (polarPlane (radius, angle)) = _
    rw [radialTestLift_model mode vector test radius positive angle]
    exact smul_comm (test radius) (cellExponential mode angle) vector
  exact (congrArg (fun field : ℝ → ComplexEuclidean 1 => angularCoefficient field frequency) functions).trans
    (character_coefficient_zero mode frequency different (test radius • vector))

private theorem character_polar_rotation (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    rotatedPoint angle (polarClosedPoint radius 0 nonnegative bounded) =
      polarClosedPoint radius angle nonnegative bounded := by
  apply Subtype.ext
  change planeRotation angle (polarPlane (radius, 0)) = polarPlane (radius, angle)
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [planeRotation, polarPlane, collarPlane, mul_comm]

theorem boundaryCharacter_other_zero (mode frequency : ℤ) (different : frequency ≠ mode)
    (vector : ComplexEuclidean 1) (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test)
    (away : (0 : ℝ) ∉ tsupport test) :
    angularClosedJet frequency (boundaryCharacterJet mode vector test smooth away) = 0 := by
  let jet := boundaryCharacterJet mode vector test smooth away
  apply closedL2Core_injective
  apply closedL2_eq_of_polar
  intro radius inside angle
  have initial := (radialCoefficient_projection_value jet frequency radius inside.1.le inside.2.le).symm.trans
    (character_radial_other mode frequency different vector test smooth away radius inside.1 inside.2.le)
  have rotated := angularClosedJet_rotation_value frequency jet angle (polarClosedPoint radius 0 inside.1.le inside.2.le)
  rw [character_polar_rotation, initial, smul_zero] at rotated
  exact rotated

theorem boundaryCharacter_high (mode : ℤ) (high : mode ∉ lowAngularModes)
    (vector : ComplexEuclidean 1) (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test)
    (away : (0 : ℝ) ∉ tsupport test) :
    excludedAngularJet lowAngularModes (boundaryCharacterJet mode vector test smooth away) =
      boundaryCharacterJet mode vector test smooth away := by
  let jet := boundaryCharacterJet mode vector test smooth away
  have selected : selectedAngularJet lowAngularModes jet = 0 := by
    rw [selectedAngularJet_eq]
    apply Finset.sum_eq_zero
    intro frequency member
    exact boundaryCharacter_other_zero mode frequency
      (fun equal => high (equal ▸ member)) vector test smooth away
  change jet - selectedAngularJet lowAngularModes jet = jet
  rw [selected, sub_zero]

theorem boundaryCharacter_highCore (mode : ℤ) (high : mode ∉ lowAngularModes)
    (vector : ComplexEuclidean 1) (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test)
    (away : (0 : ℝ) ∉ tsupport test) :
    (highDiskCoreInto (boundaryCharacterJet mode vector test smooth away)).val =
      diskCoreInto (boundaryCharacterJet mode vector test smooth away) :=
  congrArg diskCoreInto (boundaryCharacter_high mode high vector test smooth away)

end Grad.CircularHighRegularity
