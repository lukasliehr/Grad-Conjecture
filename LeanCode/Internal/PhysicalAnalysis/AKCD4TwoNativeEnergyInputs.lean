import AKCD3ActualCovariantPureGrade

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.ActualSmoothPhysicalField Grad.ActualNativeCellMoments

/-- Squared L2 energy of the SAME two-input pointwise estimate. -/
theorem twoInput_squareEnergy {α E F G : Type*} [MeasurableSpace α]
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
    (measure : Measure α) (output : α → E) (high : α → F) (low : α → G)
    (highMeasurable : AEStronglyMeasurable high measure)
    (lowMeasurable : AEStronglyMeasurable low measure)
    (C B H L : ℝ) (Cnonnegative : 0≤C) (Bnonnegative : 0≤B)
    (Hnonnegative : 0≤H) (Lnonnegative : 0≤L)
    (bound : ∀ᵐ point ∂measure, ‖output point‖ ≤ C*(‖high point‖+B*‖low point‖))
    (highEnergy : (∫⁻ point, ENNReal.ofReal (‖high point‖^2) ∂measure) ≤ ENNReal.ofReal (H^2))
    (lowEnergy : (∫⁻ point, ENNReal.ofReal (‖low point‖^2) ∂measure) ≤ ENNReal.ofReal (L^2)) :
    (∫⁻ point, ENNReal.ofReal (‖output point‖^2) ∂measure) ≤ ENNReal.ofReal ((2*C*(H+B*L))^2) := by
  have first : AEMeasurable (fun point => ENNReal.ofReal (‖high point‖^2)) measure :=
    (highMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal
  have second : AEMeasurable (fun point => ENNReal.ofReal (‖low point‖^2)) measure :=
    (lowMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal
  have pointBound : ∀ᵐ point ∂measure, ENNReal.ofReal (‖output point‖^2) ≤
      ENNReal.ofReal (2*C^2) * ENNReal.ofReal (‖high point‖^2) +
      ENNReal.ofReal (2*C^2*B^2) * ENNReal.ofReal (‖low point‖^2) := by
    filter_upwards [bound] with point actual
    rw [← ENNReal.ofReal_mul (by positivity : 0≤2*C^2),
      ← ENNReal.ofReal_mul (by positivity : 0≤2*C^2*B^2),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have square := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg Cnonnegative (add_nonneg (norm_nonneg _) (mul_nonneg Bnonnegative (norm_nonneg _))))).mpr actual
    have positive := mul_nonneg (sq_nonneg C) (sq_nonneg (‖high point‖-B*‖low point‖))
    nlinarith only [square,positive]
  apply (lintegral_mono_ae pointBound).trans
  rw [lintegral_add_left' (first.const_mul (ENNReal.ofReal (2*C^2))),lintegral_const_mul'' _ first,lintegral_const_mul'' _ second]
  apply (add_le_add (mul_le_mul' (le_refl (ENNReal.ofReal (2*C^2))) highEnergy) (mul_le_mul' (le_refl (ENNReal.ofReal (2*C^2*B^2))) lowEnergy)).trans
  rw [← ENNReal.ofReal_mul (by positivity : 0≤2*C^2),
    ← ENNReal.ofReal_mul (by positivity : 0≤2*C^2*B^2),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have positive := mul_nonneg (sq_nonneg C) (mul_nonneg Hnonnegative (mul_nonneg Bnonnegative Lnonnegative))
  nlinarith [sq_nonneg (C*H),sq_nonneg (C*B*L)]

end Grad.OriginalCartesianTameEstimate
