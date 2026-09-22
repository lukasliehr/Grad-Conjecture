import GC17FrameInverse

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.InverseAllocation

theorem identityFamily_physicalValue (L sigma gamma ell : ℝ) (dimension grade : ℕ)
    (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (gradedIdentityCoefficient L sigma gamma ell grade dimension) angle point =
      ContinuousLinearMap.id ℂ (PhysicalValue dimension) := by
  rw [coherent_physicalValue _ (identityFamily_coherent L sigma gamma ell dimension)]
  exact identityCoefficient_fourier L sigma gamma ell dimension angle point

theorem frameInverseInput_fourier {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3) (angle : ℝ) (point : ClosedDisk) :
    fourierEvaluation (frameInverseInput parameters admissible epsilon field 0) angle point =
      -referenceFrame.comp (fourierEvaluation (actualFrameFamily parameters L ell epsilon field 0) angle point) := by
  change seedFourierCLM admissible 3 3 angle point (-coefficientComposition admissible 0 _ _) = _
  rw [map_neg]
  change -fourierEvaluation (coefficientComposition admissible 0 _ _) angle point = _
  rw [fourierComposition]
  unfold constantFamily
  rw [seedConstantCell_fourier]
  simp only [fourierPhase, Int.cast_zero, mul_zero, zero_mul, Complex.exp_zero, one_smul]

theorem actualFrameInverse_physicalValue {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3)
    (baseBound : ‖frameInverseInput parameters admissible epsilon field 0‖ ≤ 1 / 4)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (actualFrameInverse parameters admissible epsilon field grade) angle point =
      (fourierEvaluation (analyticCapCoefficientNeumannInverse admissible
        (frameInverseInput parameters admissible epsilon field 0)) angle point).comp referenceFrame := by
  have fixedCoherent := constantFamily_coherent L parameters.sigma0 parameters.gamma ell referenceFrame
  have inverseCoherent := inverseFamily_coherent admissible (by norm_num : 0 < 3)
    (frameInverseInput parameters admissible epsilon field)
    (frameInverseInput_coherent parameters admissible epsilon field) (1 / 4) baseBound (by norm_num)
  have identityCoherent := identityFamily_coherent L parameters.sigma0 parameters.gamma ell 3
  change coefficientPhysicalValue
    (constantFamily L parameters.sigma0 parameters.gamma ell referenceFrame grade +
      actualFrameInverseDeviation parameters admissible epsilon field grade) angle point = _
  rw [family_physicalValue_add admissible _ _ fixedCoherent
    (actualFrameInverseDeviation_coherent parameters admissible epsilon field baseBound)]
  unfold actualFrameInverseDeviation normalizedFrameInverse
  rw [family_physicalValue_comp admissible _ _ (inverseCoherent.sub identityCoherent) fixedCoherent]
  rw [family_physicalValue_sub admissible _ _ inverseCoherent identityCoherent]
  rw [constantFamily_physicalValue admissible, identityFamily_physicalValue]
  change referenceFrame +
    (coefficientPhysicalValue (inverseFamily admissible (frameInverseInput parameters admissible epsilon field) grade)
      angle point - ContinuousLinearMap.id ℂ (PhysicalValue 3)).comp referenceFrame = _
  rw [inverseFamily_physicalValue admissible (by norm_num : 0 < 3) _
    (frameInverseInput_coherent parameters admissible epsilon field) (1 / 4) baseBound (by norm_num)]
  change referenceFrame + (_ - 1) * referenceFrame = _ * referenceFrame
  rw [sub_mul, one_mul]
  abel

/-- The constructed coefficient is the two-sided inverse of the literal
physical frame, not merely the resolvent of a formal supplied perturbation. -/
theorem actualFrameInverse_two_sided {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (field : ACore parameters 3)
    (baseBound : ‖frameInverseInput parameters admissible epsilon field 0‖ ≤ 1 / 4)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    let frame := referenceFrame + fourierEvaluation (actualFrameFamily parameters L ell epsilon field 0) angle point
    let inverse := coefficientPhysicalValue (actualFrameInverse parameters admissible epsilon field grade) angle point
    frame.comp inverse = ContinuousLinearMap.id ℂ (PhysicalValue 3) ∧
      inverse.comp frame = ContinuousLinearMap.id ℂ (PhysicalValue 3) := by
  dsimp only
  rw [actualFrameInverse_physicalValue parameters admissible epsilon field baseBound]
  let frame := referenceFrame + fourierEvaluation (actualFrameFamily parameters L ell epsilon field 0) angle point
  let inverse := fourierEvaluation (analyticCapCoefficientNeumannInverse admissible
    (frameInverseInput parameters admissible epsilon field 0)) angle point
  have identities := analyticCapCoefficientNeumannInverse_pointwiseIdentification admissible
    (by norm_num : 0 < 3) (frameInverseInput parameters admissible epsilon field 0)
    (1 / 4) baseBound (by norm_num) angle point
  have normalized : ContinuousLinearMap.id ℂ (PhysicalValue 3) -
      fourierEvaluation (frameInverseInput parameters admissible epsilon field 0) angle point =
        referenceFrame.comp frame := by
    rw [frameInverseInput_fourier]
    change (1 : OperatorValue 3 3) - (-(referenceFrame * _)) = referenceFrame * (referenceFrame + _)
    have square : referenceFrame * referenceFrame = 1 := referenceFrame_square
    rw [mul_add, square]
    simp only [sub_neg_eq_add]
  rw [normalized] at identities
  change (referenceFrame * frame) * inverse = 1 ∧ inverse * (referenceFrame * frame) = 1 at identities
  change frame * (inverse * referenceFrame) = 1 ∧ (inverse * referenceFrame) * frame = 1
  have square : referenceFrame * referenceFrame = 1 := referenceFrame_square
  constructor
  · calc
      _ = referenceFrame * ((referenceFrame * frame) * inverse) * referenceFrame := by
        simp only [← mul_assoc, square, one_mul]
      _ = 1 := by rw [identities.1, mul_one, square]
  · simpa only [mul_assoc] using identities.2

end Grad.GaugeCoefficients.Physical.Ledger
