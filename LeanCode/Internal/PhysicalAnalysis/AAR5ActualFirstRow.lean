import AAR4ActualHighFluxMultipliers

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.AnnularVariational

section Reconstruction
variable (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- The conjugated physical derivative e^Phi xi_r = w' - Phi' w. -/
def annularPhysicalDerivative :
    annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower :=
  annularEnergyDerivative lower length positive -
    annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength

theorem annularPhysicalDerivative_bound (field : annularEnergySpace lower length positive) :
    ‖annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field‖ ≤
      (3 / 2 : ℝ) * ‖field‖ := by
  have derivative := annularEnergyDerivative_bound lower length positive field
  have phase := annularEnergyPhase_bound parameters lower length positive lengthPositive widthHalf widthLength field
  have difference := norm_sub_le (annularEnergyDerivative lower length positive field)
    (annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field)
  change ‖annularEnergyDerivative lower length positive field -
    annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field‖ ≤ _
  linarith

/-- AG21 in the original sqrt(r)e^Phi storage, including the undifferentiated
source f. No radial derivative or endpoint value of f is required. -/
def annularRecoveredQ (field : annularEnergySpace lower length positive) (source : AnnularBulk lower) :
    AnnularBulk lower :=
  annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field +
    annularEnergyRadial lower length positive field - source

def annularRecoveredP (field : annularEnergySpace lower length positive) (source : AnnularBulk lower) :
    AnnularBulk lower :=
  annularPMap lower (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source)

def annularRecoveredAngularP (field : annularEnergySpace lower length positive) (source : AnnularBulk lower) :
    AnnularBulk lower :=
  annularAngularPMap lower (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source)

theorem annularRecoveredQ_bound (field : annularEnergySpace lower length positive) (source : AnnularBulk lower) :
    ‖annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source‖ ≤
      3 * ‖field‖ + ‖source‖ := by
  have derivative := annularPhysicalDerivative_bound parameters lower length positive lengthPositive widthHalf widthLength field
  have radial := annularEnergyRadial_bound lower length positive field
  have sum := norm_add_le
    (annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field)
    (annularEnergyRadial lower length positive field)
  have difference := norm_sub_le
    (annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field +
      annularEnergyRadial lower length positive field) source
  unfold annularRecoveredQ
  nlinarith [norm_nonneg field]

theorem annularRecoveredAngularP_bound (field : annularEnergySpace lower length positive) (source : AnnularBulk lower) :
    ‖annularRecoveredAngularP parameters lower length positive lengthPositive widthHalf widthLength field source‖ ≤
      (12 / 5 : ℝ) *
        ‖annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source‖ :=
  annularAngularPMap_bound lower _

theorem annularRecoveredP_exact_weight (field : annularEnergySpace lower length positive)
    (source : AnnularBulk lower) (mode : HighAnnularMode) :
    annularRecoveredAngularP parameters lower length positive lengthPositive widthHalf widthLength field source mode =
      (annularAngularWeight mode : ℂ) •
        annularRecoveredP parameters lower length positive lengthPositive widthHalf widthLength field source mode := rfl

/-- The first actual retained annular row holds modewise in L2. Every cell
is present, including cell zero; inversion uses only the nonzero high D_m. -/
theorem annularRecovered_first_row (field : annularEnergySpace lower length positive)
    (source : AnnularBulk lower) (mode : HighAnnularMode) :
    annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field mode +
      annularEnergyRadial lower length positive field mode +
      annularDSymbol mode •
        annularRecoveredP parameters lower length positive lengthPositive widthHalf widthLength field source mode =
      source mode := by
  change _ + _ + annularDSymbol mode • annularPMap lower
    (annularRecoveredQ parameters lower length positive lengthPositive widthHalf widthLength field source) mode = _
  rw [annularPMap_D]
  change _ + _ + -(annularPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field mode +
    annularEnergyRadial lower length positive field mode - source mode) = _
  abel

end Reconstruction
end Grad.AnnularReconstruction
