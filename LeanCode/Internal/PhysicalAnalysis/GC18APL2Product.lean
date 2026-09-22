import GC18APL2Fourier

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.NonlinearQuotientBounds

theorem apOperatorJet_L2 {input output : ℕ} (coefficient : SmoothOperatorJet input output) (field : ClosedJet input) :
    closedOperatorL2 coefficient.value (closedContinuousToDiskL2 field.value) =
      closedContinuousToDiskL2 (apProductJet coefficient field).value := by
  rw [closedOperatorL2_closed]
  apply congrArg closedContinuousToDiskL2
  apply ContinuousMap.ext
  intro point
  exact (apProductJet_value coefficient field point).symm

theorem apMultiplier_single_L2 {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output grade : ℕ} (angle : ℝ) (inputCell shift : ℤ)
    (coefficient : SmoothOperatorJet input output) (field : ClosedJet input) :
    apL2PhysicalValue admissible angle
      (apMultiplier admissible (singleJetCoefficient L sigma gamma ell grade shift coefficient)
        (apFiniteInto L sigma gamma ell (Finsupp.single inputCell field))) =
      closedOperatorL2 (cMapCoefficient admissible grade input output angle (singleJetCoefficient L sigma gamma ell grade shift coefficient))
        (apL2PhysicalValue (grade := grade) admissible angle (apFiniteInto L sigma gamma ell (Finsupp.single inputCell field))) := by
  rw [apMultiplier_single, apL2PhysicalValue_single, cMapCoefficient_single, apL2PhysicalValue_single,
    closedOperatorL2_smul, smul_apply, map_smul, apOperatorJet_L2, smul_smul, axialPhase_add, mul_comm]

theorem apMultiplier_singleCoefficient_L2 {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output grade : ℕ} (angle : ℝ) (shift : ℤ)
    (coefficient : SmoothOperatorJet input output) (field : apGrade L sigma gamma ell input grade) :
    apL2PhysicalValue admissible angle
      (apMultiplier admissible (singleJetCoefficient L sigma gamma ell grade shift coefficient) field) =
      closedOperatorL2 (cMapCoefficient admissible grade input output angle (singleJetCoefficient L sigma gamma ell grade shift coefficient))
        (apL2PhysicalValue admissible angle field) := by
  let first := (apL2PhysicalValue (dimension := output) admissible angle).comp
    (apMultiplier admissible (singleJetCoefficient L sigma gamma ell grade shift coefficient))
  let second := (closedOperatorL2
    (cMapCoefficient admissible grade input output angle (singleJetCoefficient L sigma gamma ell grade shift coefficient))).comp
      (apL2PhysicalValue (dimension := input) (grade := grade) admissible angle)
  have equality : first = second := apFiniteGenerator_ext L sigma gamma ell first second
    (fun inputCell core => apMultiplier_single_L2 admissible angle inputCell shift coefficient core)
  change first field = second field
  rw [equality]

/-- At every grade, including zero, this is multiplication by the literal
full Fourier coefficient on the original area L2 realization. -/
theorem apMultiplier_L2 {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output grade : ℕ} (angle : ℝ)
    (coefficient : Coefficient L sigma gamma ell grade input output) (field : apGrade L sigma gamma ell input grade) :
    apL2PhysicalValue admissible angle (apMultiplier admissible coefficient field) =
      closedOperatorL2 (cMapCoefficient admissible grade input output angle coefficient)
        (apL2PhysicalValue admissible angle field) := by
  let first : Coefficient L sigma gamma ell grade input output →L[ℂ] DiskL2 output :=
    (apL2PhysicalValue admissible angle).comp
      ((ContinuousLinearMap.apply ℂ (apGrade L sigma gamma ell output grade) field).comp
        (apCompletedBilinear admissible input output grade))
  let second : Coefficient L sigma gamma ell grade input output →L[ℂ] DiskL2 output :=
    (ContinuousLinearMap.apply ℂ (DiskL2 output) (apL2PhysicalValue admissible angle field)).comp
      ((closedOperatorAction input output).comp (cMapCoefficient admissible grade input output angle))
  have equality : first = second := apCoefficientGenerator_ext L sigma gamma ell first second
    (fun shift core => apMultiplier_singleCoefficient_L2 admissible angle shift core field)
  change first coefficient = second coefficient
  rw [equality]

end Grad.GaugeCoefficients.Physical.RadialLedger
