import AHP33ActualRadialReconstructionConsumer

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation
open Grad.PhaseAlgebra Grad.GaugeCoefficients.Physical.Ledger

theorem constantMatrixKernel_moment (parameters : PhaseParameters) (input output moment : ℕ)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output) :
    fullKernelMoment parameters moment (constantMatrixKernel parameters input output mapping) =
      Real.exp (parameters.sigma0 + parameters.gamma) * ‖mapping‖ := by
  have entryNorm (shift : ℤ × ℤ) :
      (constantMatrixKernel parameters input output mapping).entryNorm shift =
        if shift = (0, 0) then ‖mapping‖ else 0 := by
    apply le_antisymm
    · apply FullTwoFrequencyKernel.entryNorm_le
      intro mode
      rw [constantMatrixKernel_entry]
      split <;> simp_all
    · have lower := (constantMatrixKernel parameters input output mapping).entry_le shift (0, 0)
      by_cases zero : shift = (0, 0)
      · simpa [constantMatrixKernel_entry, zero] using lower
      · simpa [constantMatrixKernel_entry, zero] using lower
  unfold fullKernelMoment
  simp only [entryNorm]
  rw [tsum_eq_single (0, 0)]
  · simp [boundaryCoefficientPhaseCost, annularFrequency, phaseWeight]
  · intro shift nonzero
    simp [nonzero]

theorem radialSevenSlotNormalization_norm_le (radius : ℝ) :
    ‖radialSevenSlotNormalization radius‖ ≤ 5 + 2 * ‖(radius : ℂ)⁻¹‖ := by
  have unit (i : Fin 7) : ‖matrixUnit (input := 7) (output := 7) i i‖ ≤ (1 : ℝ) := matrixUnit_norm_le i i
  have scaled (i : Fin 7) : ‖(radius : ℂ)⁻¹ • matrixUnit (input := 7) (output := 7) i i‖ ≤ ‖(radius : ℂ)⁻¹‖ := by
    rw [norm_smul]
    exact (mul_le_mul_of_nonneg_left (unit i) (norm_nonneg _)).trans_eq (mul_one _)
  unfold radialSevenSlotNormalization
  calc
    _ ≤ ‖matrixUnit (input := 7) (output := 7) 0 0‖ + ‖(radius : ℂ)⁻¹ • matrixUnit (input := 7) (output := 7) 1 1‖ + ‖matrixUnit (input := 7) (output := 7) 2 2‖ +
      ‖(radius : ℂ)⁻¹ • matrixUnit (input := 7) (output := 7) 3 3‖ + ‖matrixUnit (input := 7) (output := 7) 4 4‖ + ‖matrixUnit (input := 7) (output := 7) 5 5‖ + ‖matrixUnit (input := 7) (output := 7) 6 6‖ := by
      exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)) le_rfl)) le_rfl)) le_rfl)
    _ ≤ _ := by linarith [unit 0, unit 2, unit 4, unit 5, unit 6, scaled 1, scaled 3]

theorem radialSevenSlotKernel_moment_on_annulus (parameters : PhaseParameters)
    (lower : ℝ) (lowerPositive : 0 < lower) (r : RadialPoint) (inside : lower ≤ r.val)
    (moment : ℕ) :
    fullKernelMoment (radialKernelParameters parameters r) moment (radialSevenSlotKernel parameters r) ≤
      Real.exp (parameters.sigma0 + 2 * parameters.gamma) * (5 + 2 * lower⁻¹) := by
  have positive : 0 < r.val := lowerPositive.trans_le inside
  have inverse : ‖(r.val : ℂ)⁻¹‖ ≤ lower⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos positive]
    exact inv_anti₀ lowerPositive inside
  rw [radialSevenSlotKernel, constantMatrixKernel_moment]
  apply mul_le_mul (radialKernelPhaseConstant_le parameters r)
    ((radialSevenSlotNormalization_norm_le r.val).trans (by linarith))
    (norm_nonneg _) (Real.exp_pos _).le

end Grad.AnnularReconstruction
