import SCC4OriginalFrameRealization

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState Grad.SourceCollar
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Neumann Grad.GaugeCoefficients.Neumann.Regularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.InverseAllocation Grad.GaugeCoefficients.Physical.Ledger

theorem originalInverseInput_fourier (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3) (angle : ℝ) (point : ClosedDisk) :
    fourierEvaluation (originalInverseInput parameters L epsilon field 0) angle point =
      -referenceFrame.comp (originalPhysicalFrameDeviation parameters L epsilon field angle point) := by
  change seedFourierCLM (unitDiskAdmissible parameters) 3 3 angle point
    (-coefficientComposition (unitDiskAdmissible parameters) 0 _ _) = _
  rw [map_neg]
  change -fourierEvaluation (coefficientComposition (unitDiskAdmissible parameters) 0 _ _) angle point = _
  rw [fourierComposition]
  have fixed := constantFamily_physicalValue (unitDiskAdmissible parameters) referenceFrame 0 angle point
  have actual := originalFrameFamily_physicalValue parameters L epsilon field 0 angle point
  change fourierEvaluation _ angle point = referenceFrame at fixed
  change fourierEvaluation _ angle point = originalPhysicalFrameDeviation parameters L epsilon field angle point at actual
  rw [fixed, actual]

theorem originalInverseFamily_physicalValue (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3)
    (baseBound : ‖originalInverseInput parameters L epsilon field 0‖ ≤ 1 / 4)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    coefficientPhysicalValue (originalInverseFamily parameters L epsilon field grade) angle point =
      (fourierEvaluation (analyticCapCoefficientNeumannInverse (unitDiskAdmissible parameters)
        (originalInverseInput parameters L epsilon field 0)) angle point).comp referenceFrame := by
  have fixedCoherent := constantFamily_coherent 1 parameters.sigma0 parameters.gamma 1 referenceFrame
  have inverseCoherent := inverseFamily_coherent (unitDiskAdmissible parameters) (by norm_num : 0 < 3)
    (originalInverseInput parameters L epsilon field)
    (originalInverseInput_coherent parameters L epsilon field) (1 / 4) baseBound (by norm_num)
  have identityCoherent := identityFamily_coherent 1 parameters.sigma0 parameters.gamma 1 3
  change coefficientPhysicalValue
    (constantFamily 1 parameters.sigma0 parameters.gamma 1 referenceFrame grade +
      originalInverseDeviation parameters L epsilon field grade) angle point = _
  rw [family_physicalValue_add (unitDiskAdmissible parameters) _ _ fixedCoherent
    (originalInverseDeviation_coherent parameters L epsilon field baseBound)]
  unfold originalInverseDeviation
  rw [family_physicalValue_comp (unitDiskAdmissible parameters) _ _ (inverseCoherent.sub identityCoherent) fixedCoherent,
    family_physicalValue_sub (unitDiskAdmissible parameters) _ _ inverseCoherent identityCoherent,
    constantFamily_physicalValue (unitDiskAdmissible parameters), identityFamily_physicalValue]
  rw [inverseFamily_physicalValue (unitDiskAdmissible parameters) (by norm_num : 0 < 3) _
    (originalInverseInput_coherent parameters L epsilon field) (1 / 4) baseBound (by norm_num)]
  change referenceFrame + (_ - 1) * referenceFrame = _ * referenceFrame
  rw [sub_mul, one_mul]
  abel

/-- The constructed all-grade coefficient is the actual two-sided inverse
at every point of the original disk, for all physical lengths L>0. -/
theorem originalInverseFamily_two_sided (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3)
    (baseBound : ‖originalInverseInput parameters L epsilon field 0‖ ≤ 1 / 4)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    let frame := referenceFrame + originalPhysicalFrameDeviation parameters L epsilon field angle point
    let inverse := coefficientPhysicalValue (originalInverseFamily parameters L epsilon field grade) angle point
    frame.comp inverse = ContinuousLinearMap.id ℂ (PhysicalValue 3) ∧
      inverse.comp frame = ContinuousLinearMap.id ℂ (PhysicalValue 3) := by
  dsimp only
  rw [originalInverseFamily_physicalValue parameters L epsilon field baseBound]
  let frame := referenceFrame + originalPhysicalFrameDeviation parameters L epsilon field angle point
  let inverse := fourierEvaluation (analyticCapCoefficientNeumannInverse (unitDiskAdmissible parameters)
    (originalInverseInput parameters L epsilon field 0)) angle point
  have identities := analyticCapCoefficientNeumannInverse_pointwiseIdentification (unitDiskAdmissible parameters)
    (by norm_num : 0 < 3) (originalInverseInput parameters L epsilon field 0)
    (1 / 4) baseBound (by norm_num) angle point
  have normalized : ContinuousLinearMap.id ℂ (PhysicalValue 3) -
      fourierEvaluation (originalInverseInput parameters L epsilon field 0) angle point = referenceFrame.comp frame := by
    rw [originalInverseInput_fourier]
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

theorem originalInverseFamily_matrix_identity (parameters : PhaseParameters) (L epsilon : ℝ)
    (field : ACore parameters 3)
    (baseBound : ‖originalInverseInput parameters L epsilon field 0‖ ≤ 1 / 4)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    let frame := originalPhysicalFrameMatrix parameters L epsilon field angle point
    let inverse := familyMatrix (originalInverseFamily parameters L epsilon field) grade angle point
    frame * inverse = 1 ∧ inverse * frame = 1 := by
  have identities := originalInverseFamily_two_sided parameters L epsilon field baseBound grade angle point
  exact ⟨(operatorMatrix_comp _ _).symm.trans ((congrArg operatorMatrix identities.1).trans (operatorMatrix_one 3)),
    (operatorMatrix_comp _ _).symm.trans ((congrArg operatorMatrix identities.2).trans (operatorMatrix_one 3))⟩

end Grad.SourceCollarCoefficients
