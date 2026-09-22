import ASL4OutsideAlgebra

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

namespace Grad.AxisSourceLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.AxisSplit Grad.RawForward

variable {parameters : PhaseParameters} {radius : ℝ} {dimension : ℕ}

def FirstOutsideEqual (radius : ℝ) (first second : ACore parameters dimension) : Prop :=
  OutsideEqual radius first second ∧
    ∀ direction, OutsideEqual radius (partialCore parameters direction first) (partialCore parameters direction second)

theorem FirstOutsideEqual.euler {first second : ACore parameters dimension}
    (equal : FirstOutsideEqual radius first second) :
    OutsideEqual radius (eulerCore parameters first) (eulerCore parameters second) := by
  intro cell point outside
  change ((eulerCore parameters first).val cell).value point = ((eulerCore parameters second).val cell).value point
  rw [eulerCore_actual, eulerCore_actual]
  have partialLaw (direction : Fin 2) : partialCoefficient direction (first.val cell) point =
      partialCoefficient direction (second.val cell) point := equal.2 direction cell point outside
  rw [partialLaw 0, partialLaw 1]

theorem FirstOutsideEqual.rotation {first second : ACore parameters dimension}
    (equal : FirstOutsideEqual radius first second) :
    OutsideEqual radius (rotationCore parameters first) (rotationCore parameters second) := by
  intro cell point outside
  change ((rotationCore parameters first).val cell).value point = ((rotationCore parameters second).val cell).value point
  rw [rotationCore_actual, rotationCore_actual]
  have partialLaw (direction : Fin 2) : partialCoefficient direction (first.val cell) point =
      partialCoefficient direction (second.val cell) point := equal.2 direction cell point outside
  rw [partialLaw 0, partialLaw 1]

theorem FirstOutsideEqual.add_smul_zero (base direction : ACore parameters dimension)
    (zeroJets : FirstOutsideEqual radius direction 0) (scalar : ℂ) :
    FirstOutsideEqual radius (base + scalar • direction) base := by
  constructor
  · have equal := (OutsideEqual.refl base).add (zeroJets.1.smul scalar)
    simpa only [smul_zero, add_zero] using equal
  · intro coordinate
    rw [map_add, map_smul]
    have equal := (OutsideEqual.refl (partialCore parameters coordinate base)).add
      ((zeroJets.2 coordinate).smul scalar)
    simpa only [map_zero, smul_zero, add_zero] using equal

theorem affineStateCore_outside {first second : QuotientState parameters}
    (scalar : stateScalar first = stateScalar second)
    (field : OutsideEqual radius (stateField first) (stateField second)) (cellLength : ℝ) :
    OutsideEqual radius (affineStateCore parameters cellLength first) (affineStateCore parameters cellLength second) := by
  unfold affineStateCore
  rw [scalar]
  exact (field.time.add ((field.valueMap tangentGeneratorMap).smul (stateScalar second))).add
    (OutsideEqual.refl _)

/-- Locality of all four literal Cartesian raw equations. Angular means
sample the same circle; all spatial derivatives are the genuine closed jets. -/
theorem originalRawRowsCore_outside (cellLength : ℝ) (first second : QuotientState parameters)
    (scalar : stateScalar first = stateScalar second)
    (field : FirstOutsideEqual radius (stateField first) (stateField second))
    (potential : FirstOutsideEqual radius (statePotential first) (statePotential second)) :
    ∀ row, OutsideEqual radius (originalRawRowsCore parameters cellLength first row)
      (originalRawRowsCore parameters cellLength second row) := by
  have affine := affineStateCore_outside scalar field.1 cellLength
  intro row
  fin_cases row
  · exact (potential.rotation.sub (field.rotation.dot field.rotation)).add (OutsideEqual.refl _)
  · exact (potential.euler.sub (field.euler.dot field.rotation)).removeAngular
  · exact ((field.rotation.dot affine).sub potential.1.time).removeAngular
  · exact ((field.euler.determinant field.rotation) affine).removeAngular

theorem originalRawRowsCore_cap_line (cellLength : ℝ) (base direction : QuotientState parameters)
    (scalarZero : stateScalar direction = 0)
    (fieldZero : FirstOutsideEqual radius (stateField direction) 0)
    (potentialZero : FirstOutsideEqual radius (statePotential direction) 0)
    (scalar : ℂ) :
    ∀ row, OutsideEqual radius
      (originalRawRowsCore parameters cellLength (base + scalar • direction) row)
      (originalRawRowsCore parameters cellLength base row) := by
  apply originalRawRowsCore_outside
  · rw [map_add, map_smul, scalarZero, smul_zero, add_zero]
  · rw [map_add, map_smul]
    exact FirstOutsideEqual.add_smul_zero _ _ fieldZero scalar
  · rw [map_add, map_smul]
    exact FirstOutsideEqual.add_smul_zero _ _ potentialZero scalar

end Grad.AxisSourceLift
