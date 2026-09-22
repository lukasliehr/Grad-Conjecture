import GC14ReferenceCoefficient

noncomputable section

set_option maxHeartbeats 800000

open Set
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Envelope

theorem shiftedClosedJet_empty {dimension : ℕ} (field : ClosedJet dimension) :
    shiftedClosedJet field emptyCartesianWord = field := by
  apply closedJet_eq_of_value_eq
  rw [shiftedClosedJet_value, closedDerivative_zero_order]

/-- Actual Cartesian frame deviation. Only literal derivatives of the original
state, the fixed rotation generator, and the reference linear state enter. -/
def actualFrameDeviationCoefficient {grade : ℕ} (parameters : PhaseParameters) (L ell epsilon : ℝ)
    (field : GradeCore parameters 3 (grade + 4)) :
    Coefficient L parameters.sigma0 parameters.gamma ell grade 3 3 :=
  shiftedStateCoefficient parameters L ell grade (columnEmbedding 3 3 0) field.toCore
      (fun _ : Fin 1 => 0) 0 +
    shiftedStateCoefficient parameters L ell grade (columnEmbedding 3 3 1) field.toCore
      (fun _ : Fin 1 => 1) 0 +
    (L : ℂ)⁻¹ • shiftedStateCoefficient parameters L ell grade (columnEmbedding 3 3 2) field.toCore
      emptyCartesianWord 1 +
    ((epsilon : ℂ) * (L : ℂ)⁻¹) •
      (shiftedStateCoefficient parameters L ell grade referenceCurvatureMapping field.toCore
        emptyCartesianWord 0 + referenceCurvatureCoefficient parameters L ell grade)

theorem actualFrameDeviationCoefficient_derivative {L ell : ℝ} {grade : ℕ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : GradeCore parameters 3 (grade + 4))
    (cell : ℤ) (index : DerivativeIndex grade) (point : ClosedDisk) :
    coefficientDerivative (actualFrameDeviationCoefficient parameters L ell epsilon field) cell index point =
      (ell ^ derivativeOrder index : ℂ) •
        frameDeviationMultiDerivative parameters L epsilon field cell (derivativeMultiIndex index)
          (physicalScaledPoint ell admissible.2.2.2.1.le
            (admissible.2.2.2.2.trans (min_le_left _ _)) point) := by
  unfold actualFrameDeviationCoefficient
  simp only [coefficientDerivative_add_apply, coefficientDerivative_smul_apply,
    shiftedStateCoefficient_derivative parameters admissible,
    referenceCurvatureCoefficient_derivative parameters admissible,
    pow_zero, pow_one, one_smul, shiftedClosedJet_empty]
  unfold frameDeviationMultiDerivative referenceCurvatureMapping
  apply ContinuousLinearMap.ext
  intro vector
  apply PiLp.ext
  intro coordinate
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    columnEmbedding_apply, map_add, map_smul, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

theorem referenceStateMultiDerivative_zero (cell : ℤ) (point : ClosedDisk) :
    referenceStateMultiDerivative cell (0, 0) point = referenceStateCell cell point := by
  simp [referenceStateMultiDerivative, referenceStateCell]

theorem frameDeviationMultiDerivative_zero {grade : ℕ} (parameters : PhaseParameters)
    (L epsilon : ℝ) (field : GradeCore parameters 3 grade) (cell : ℤ) (point : ClosedDisk) :
    frameDeviationMultiDerivative parameters L epsilon field cell (0, 0) point =
      frameDeviationCell parameters L epsilon field cell point := by
  unfold frameDeviationMultiDerivative frameDeviationCell
  simp only [closedMultiDerivative_zero, shiftedClosedJet_value, referenceStateMultiDerivative_zero]

theorem actualFrameDeviationCoefficient_value {L ell : ℝ} {grade : ℕ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : GradeCore parameters 3 (grade + 4)) (cell : ℤ) (point : ClosedDisk) :
    coefficientDerivative (actualFrameDeviationCoefficient parameters L ell epsilon field)
        cell (zeroDerivativeIndexAt grade) point =
      frameDeviationCell parameters L epsilon field cell
        (physicalScaledPoint ell admissible.2.2.2.1.le
          (admissible.2.2.2.2.trans (min_le_left _ _)) point) := by
  rw [actualFrameDeviationCoefficient_derivative parameters admissible]
  change (ell ^ 0 : ℂ) • frameDeviationMultiDerivative parameters L epsilon field cell (0, 0) _ = _
  rw [pow_zero, one_smul, frameDeviationMultiDerivative_zero]

end Grad.GaugeCoefficients.Physical.Frame
