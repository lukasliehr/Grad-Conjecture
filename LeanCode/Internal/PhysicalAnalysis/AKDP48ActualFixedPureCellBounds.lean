import AKDP47OriginalPureCellNormAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.Constraints
open Grad.OriginalCartesianTameEstimate Grad.OriginalCoreRealization
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Radial

theorem startupOriginalCellNorm_of_rows {input output : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (core : ACore parameters input) (image : ACore parameters output)
    (constant : ℝ) (nonnegative : 0≤constant)
    (rows : ∀ cell,‖cellGradeRowLinear (grade := 0) parameters cell (image.val cell)‖≤
      constant*‖cellGradeRowLinear (grade := 0) parameters cell (core.val cell)‖) :
    originalCellNorm parameters grade image≤constant*originalCellNorm parameters grade core := by
  have pointwise (cell : ℤ) :
      (cellFrequency cell^grade*‖apMassRow (cellFrequency cell) 0 (phaseWeightedJet parameters cell (image.val cell))‖)^2≤
        constant^2*(cellFrequency cell^grade*‖apMassRow (cellFrequency cell) 0
          (phaseWeightedJet parameters cell (core.val cell))‖)^2 := by
    have bound := mul_le_mul_of_nonneg_left (rows cell) (pow_nonneg (cellFrequency_pos cell).le grade)
    rw [originalWeightedRow_mass,originalWeightedRow_mass] at bound
    have square := pow_le_pow_left₀
      (mul_nonneg (pow_nonneg (cellFrequency_pos cell).le grade) (norm_nonneg _)) bound 2
    nlinarith only [square]
  have total := (originalCellNorm_summable parameters grade image).tsum_le_tsum pointwise
    ((originalCellNorm_summable parameters grade core).mul_left (constant^2))
  rw [tsum_mul_left,←originalCellNorm_sq,←originalCellNorm_sq] at total
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg nonnegative (Real.sqrt_nonneg _))).mp
  change originalCellNorm parameters grade image^2≤(constant*originalCellNorm parameters grade core)^2
  simpa only [mul_pow] using total

theorem startupOriginalPointCore_cell_bound {input output : ℕ} (parameters : PhaseParameters)
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (core : ACore parameters input) (grade : ℕ) :
    originalCellNorm parameters grade (startupOriginalPointCore parameters mapping orthogonal core)≤
      (‖mapping‖*orthogonalGradeConstant 0)*originalCellNorm parameters grade core := by
  apply startupOriginalCellNorm_of_rows parameters grade core _ _
    (mul_nonneg (norm_nonneg _) (orthogonalGradeConstant_nonnegative 0))
  intro cell
  exact (valueMap_grade_row_bound (grade := 0) mapping parameters cell (orthogonalJet orthogonal (core.val cell))).trans
    ((mul_le_mul_of_nonneg_left (orthogonal_grade_row_bound (grade := 0) parameters cell orthogonal (core.val cell))
      (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm)

theorem startupOriginalAngularCore_cell_bound {dimension : ℕ} (parameters : PhaseParameters)
    (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight)
    (bound : ℝ) (nonnegative : 0≤bound)
    (bounded : ∀ angle∈Icc (0 : ℝ) (2*Real.pi),‖weight angle‖≤bound)
    (core : ACore parameters dimension) (grade : ℕ) :
    originalCellNorm parameters grade (originalAngularKernelCore parameters weight smooth bound nonnegative bounded core)≤
      (bound*orthogonalGradeConstant 0)*originalCellNorm parameters grade core := by
  apply startupOriginalCellNorm_of_rows parameters grade core _ _
    (mul_nonneg nonnegative (orthogonalGradeConstant_nonnegative 0))
  intro cell
  exact originalAngularKernel_row_bound (grade := 0) parameters cell weight smooth bound nonnegative bounded (core.val cell)

end Grad.CartesianStartup
