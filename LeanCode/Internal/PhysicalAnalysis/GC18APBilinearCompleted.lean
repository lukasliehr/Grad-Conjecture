import GC18APClosure

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

theorem apMultiplier_add {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output grade : ℕ} (first second : Coefficient L sigma gamma ell grade input output) :
    apMultiplier admissible (first + second) = apMultiplier admissible first + apMultiplier admissible second := by
  apply ContinuousLinearMap.ext
  intro field
  apply Subtype.ext
  change apAmbientMultiplier admissible (first.val + second.val) field.val = _
  rw [apAmbientMultiplier_add]
  rfl

theorem apMultiplier_smul {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output grade : ℕ} (scalar : ℂ) (coefficient : Coefficient L sigma gamma ell grade input output) :
    apMultiplier admissible (scalar • coefficient) = scalar • apMultiplier admissible coefficient := by
  apply ContinuousLinearMap.ext
  intro field
  apply Subtype.ext
  change apAmbientMultiplier admissible (scalar • coefficient.val) field.val = _
  rw [apAmbientMultiplier_smul]
  rfl

def apCompletedBilinear {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (input output grade : ℕ) :
    Coefficient L sigma gamma ell grade input output →L[ℂ]
      apGrade L sigma gamma ell input grade →L[ℂ] apGrade L sigma gamma ell output grade := by
  let mapping : Coefficient L sigma gamma ell grade input output →ₗ[ℂ]
      (apGrade L sigma gamma ell input grade →L[ℂ] apGrade L sigma gamma ell output grade) :=
    { toFun := apMultiplier admissible
      map_add' := apMultiplier_add admissible
      map_smul' := apMultiplier_smul admissible }
  exact @LinearMap.mkContinuous ℂ ℂ (Coefficient L sigma gamma ell grade input output)
    (apGrade L sigma gamma ell input grade →L[ℂ] apGrade L sigma gamma ell output grade)
    _ _ _ _ _ _ (RingHom.id ℂ) mapping (apMultiplierConstant L sigma gamma grade) (fun coefficient =>
      ContinuousLinearMap.opNorm_le_bound (apMultiplier admissible coefficient)
        (mul_nonneg (apMultiplierConstant_nonnegative admissible grade) (norm_nonneg coefficient))
        (apMultiplier_bound admissible coefficient))

theorem apCompletedBilinear_apply {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output grade : ℕ} (coefficient : Coefficient L sigma gamma ell grade input output)
    (field : apGrade L sigma gamma ell input grade) :
    apCompletedBilinear admissible input output grade coefficient field = apMultiplier admissible coefficient field := rfl

end Grad.GaugeCoefficients.Physical.RadialLedger
