import AKAG2SchwartzRealPairing

noncomputable section

set_option maxHeartbeats 1600000

open MeasureTheory LineDeriv
open scoped ContDiff SchwartzMap

namespace Grad.CartesianStartup

open Grad.PDEBootstrap Grad.WeightedJets.ZeroExtension
open Grad.WeakTesting Grad.WeakTesting.Commutation

/-- Complex Schwartz tests are the complex span of real Schwartz tests. -/
theorem startupSchwartz_decomposition (test : 𝓢(Spatial, ℂ)) :
    test = startupRealSchwartz (test.postcompCLM Complex.reCLM) +
      Complex.I • startupRealSchwartz (test.postcompCLM Complex.imCLM) := by
  apply SchwartzMap.ext
  intro point
  change test point = ((test point).re : ℂ) + Complex.I * ((test point).im : ℂ)
  simpa only [mul_comm] using (Complex.re_add_im (test point)).symm

theorem startupTempered_eq_of_real (first second : FieldDistribution)
    (same : ∀ test : 𝓢(Spatial, ℝ), first (startupRealSchwartz test) = second (startupRealSchwartz test)) :
    first = second := by
  apply UniformConvergenceCLM.ext
  intro test
  rw [startupSchwartz_decomposition test, map_add, map_add, map_smul, map_smul, same, same]

theorem startupRealSchwartz_distributionDerivative (field : FieldL2)
    (test : 𝓢(Spatial, ℝ)) (direction : Fin 2) :
    distributionDerivative direction (distributionEmbedding field) (startupRealSchwartz test) =
      -distributionEmbedding field (startupRealSchwartz (lineDerivOp (spatialDirection direction) test)) := by
  change (lineDerivOp (spatialDirection direction) (distributionEmbedding field)) (startupRealSchwartz test) = _
  rw [TemperedDistribution.lineDerivOp_apply_apply, map_neg, startupRealSchwartz_derivative]

theorem startupSchwartz_ordered_first (test : 𝓢(Spatial, ℝ)) (direction : Fin 2) :
    orderedTestDerivative 1 (startupFirstWord direction) test =
      (lineDerivOp (spatialDirection direction) test : Spatial → ℝ) := by
  funext point
  rw [orderedTestDerivative, iteratedFDeriv_one_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]

/-- The genuine compact weak derivative becomes the SAME whole-plane
 tempered derivative. No regularity of the L2 representatives is assumed. -/
theorem startupCompactWeak_tempered {support : Set Spatial}
    (localizer : TestLocalizer Set.univ support)
    (field derivative : Grad.GenericCarriers.FieldL2 3 Set.univ)
    (fieldSupported : SupportedField CellValues Set.univ support field)
    (derivativeSupported : SupportedField CellValues Set.univ support derivative)
    (direction : Fin 2)
    (weak : HasWeakOrderedDerivative 3 Set.univ 1 (startupFirstWord direction) field derivative) :
    distributionDerivative direction (distributionEmbedding (startupWholePlaneField field)) =
      distributionEmbedding (startupWholePlaneField derivative) := by
  apply startupTempered_eq_of_real
  intro test
  rw [startupRealSchwartz_distributionDerivative]
  apply lp.ext
  funext cell
  apply ext_inner_left ℂ
  intro vector
  simp only [lp.coeFn_neg, Pi.neg_apply, inner_neg_right]
  rw [startupRealSchwartz_pairing, startupRealSchwartz_pairing]
  have identity := startupCompactWeak_smoothTest localizer (startupFirstWord direction) field derivative
    fieldSupported derivativeSupported weak cell vector test test.smooth'
  rw [pow_one, neg_one_mul, startupSchwartz_ordered_first] at identity
  exact identity.symm

end Grad.CartesianStartup
