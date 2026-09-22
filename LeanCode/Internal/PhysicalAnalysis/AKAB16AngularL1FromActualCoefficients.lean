import AKAB14PhysicalHilbertL1Consumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ENNReal BigOperators

namespace Grad.WeightedAxisRemoval
open Grad.ClosedJets Grad.SourceCollarCoefficients Grad.BoundaryTrace Grad.AnnularIncomingIntegrability

theorem angularPhysicalField_energy_bound {dimension : ℕ}
    (coefficients : CellL2 dimension) (cell : ℤ) (field : ℝ → ComplexEuclidean dimension)
    (continuousField : Continuous field)
    (same : ∀ mode, angularCoefficient field mode = coefficients (mode,cell)) :
    (∫ angle in -Real.pi..Real.pi, ‖field angle‖ ^ 2) ≤ (2 * Real.pi) * ‖coefficients‖ ^ 2 := by
  have summation := angular_hasSum_sq field continuousField
  simp_rw [same] at summation
  have wholeSum := lp_summable_sq coefficients
  have normSum : ‖coefficients‖ ^ 2 = ∑' mode : ℤ × ℤ, ‖coefficients mode‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat,Real.rpow_ofNat] using (lp.norm_rpow_eq_tsum (p := 2) (by norm_num) coefficients)
  have finiteBound (support : Finset ℤ) : (∑ mode ∈ support, ‖coefficients (mode,cell)‖ ^ 2) ≤ ‖coefficients‖ ^ 2 := by
    have bound := wholeSum.sum_le_tsum (support.image (fun mode => (mode,cell))) (fun _ _ => sq_nonneg _)
    rw [Finset.sum_image] at bound
    · exact bound.trans_eq normSum.symm
    · intro first _ second _ equality
      exact congrArg Prod.fst equality
  have bound : (2 * Real.pi)⁻¹ * (∫ angle in -Real.pi..Real.pi, ‖field angle‖ ^ 2) ≤ ‖coefficients‖ ^ 2 :=
    le_of_tendsto summation (Eventually.of_forall finiteBound)
  exact (inv_mul_le_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mp bound

theorem angularPhysicalField_integral_norm_bound {dimension : ℕ}
    (coefficients : CellL2 dimension) (cell : ℤ) (field : ℝ → ComplexEuclidean dimension)
    (continuousField : Continuous field)
    (same : ∀ mode, angularCoefficient field mode = coefficients (mode,cell)) :
    (∫ angle in Ioc (-Real.pi) Real.pi, ‖field angle‖) ≤ (2 * Real.pi) * ‖coefficients‖ := by
  have member : MemLp field 2 (volume.restrict (Ioc (-Real.pi) Real.pi)) :=
    (memLp_two_iff_integrable_sq_norm continuousField.aestronglyMeasurable).mpr
      (((continuousField.norm.pow 2).continuousOn.integrableOn_Icc).mono_set Ioc_subset_Icc_self)
  have holder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (μ := volume.restrict (Ioc (-Real.pi) Real.pi)) (p := (2 : ℝ)) (q := (2 : ℝ))
    (by rw [Real.holderConjugate_iff]; norm_num : (2 : ℝ).HolderConjugate 2)
    (Eventually.of_forall (fun _ => show (0 : ℝ) ≤ 1 by norm_num))
    (Eventually.of_forall (fun angle => norm_nonneg (field angle)))
    (memLp_const (1 : ℝ)) (by simpa using member.norm)
  have measureAngle : (volume.restrict (Ioc (-Real.pi) Real.pi)).real univ = 2 * Real.pi := by
    simp only [Measure.real,Measure.restrict_apply_univ,Real.volume_Ioc]
    rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : 0 ≤ Real.pi - -Real.pi)]
    ring
  have cauchy : (∫ angle in Ioc (-Real.pi) Real.pi, ‖field angle‖) ≤
      Real.sqrt (2 * Real.pi) * Real.sqrt (∫ angle in Ioc (-Real.pi) Real.pi, ‖field angle‖ ^ 2) := by
    simpa only [one_mul,Real.rpow_ofNat,one_pow,integral_const,smul_eq_mul,
      measureAngle,mul_one,← Real.sqrt_eq_rpow] using holder
  have energy := angularPhysicalField_energy_bound coefficients cell field continuousField same
  rw [intervalIntegral.integral_of_le (neg_lt_self Real.pi_pos).le] at energy
  apply cauchy.trans
  calc
    _ ≤ Real.sqrt (2 * Real.pi) * Real.sqrt ((2 * Real.pi) * ‖coefficients‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt energy) (Real.sqrt_nonneg _)
    _ = _ := by
      have product : Real.sqrt ((2 * Real.pi) * ‖coefficients‖ ^ 2) =
          Real.sqrt (2 * Real.pi) * ‖coefficients‖ := by
        rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * Real.pi),Real.sqrt_sq (norm_nonneg _)]
      rw [product,← mul_assoc,← pow_two,Real.sq_sqrt (by positivity)]

end Grad.WeightedAxisRemoval
