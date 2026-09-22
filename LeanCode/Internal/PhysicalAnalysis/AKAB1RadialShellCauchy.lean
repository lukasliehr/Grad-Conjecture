import AKZ13ActualCartesianPhysicalEnergyConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Grad.WeightedAxisRemoval

/-- Cauchy--Schwarz on the actual shrinking radial shell. Its measure is
exactly epsilon; the polar Jacobian is inserted by the next estimate. -/
theorem radialShell_integral_norm_le {E : Type*} [NormedAddCommGroup E]
    (epsilon : ℝ) (positive : 0 < epsilon) (field : ℝ → E)
    (squareIntegrable : MemLp field 2 (volume.restrict (Ioc epsilon (2 * epsilon)))) :
    (∫ radius in Ioc epsilon (2 * epsilon), ‖field radius‖) ≤
      Real.sqrt epsilon * Real.sqrt (∫ radius in Ioc epsilon (2 * epsilon), ‖field radius‖ ^ 2) := by
  have holder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Ioc epsilon (2 * epsilon))) (p := (2 : ℝ)) (q := (2 : ℝ))
    (by rw [Real.holderConjugate_iff]; norm_num : (2 : ℝ).HolderConjugate 2)
    (Eventually.of_forall (fun _ => show (0 : ℝ) ≤ 1 by norm_num))
    (Eventually.of_forall (fun radius => norm_nonneg (field radius)))
    (memLp_const (1 : ℝ)) (by simpa using squareIntegrable.norm)
  have measureShell : (volume.restrict (Ioc epsilon (2 * epsilon))).real univ = epsilon := by
    simp only [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc]
    rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ 2 * epsilon - epsilon)]
    ring
  simpa only [one_mul, Real.rpow_ofNat, one_pow, integral_const, smul_eq_mul,
    measureShell, mul_one, ← Real.sqrt_eq_rpow] using holder

end Grad.WeightedAxisRemoval
