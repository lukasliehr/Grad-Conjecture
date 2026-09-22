import AKDP20OriginalPointCoreFidelity
import AKDP23ActualMatrixCoreRankControl

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.NonlinearProduct
open Grad.OriginalCoreRealization Grad.ActualOriginalSourceMoments Grad.NonlinearQuotientBounds
open Grad.Constraints Grad.Constraints.Gauges Grad.GaugeCoefficients.Physical.RadialLedger
namespace StartupCoreRankControl
variable {parameters : PhaseParameters} {budget : ℝ}

def identity (dimension rank : ℕ) (budgetNonnegative : 0≤budget) :
    StartupCoreRankControl parameters budget (StartupCoreRankProfile.fixed 1 1 zero_le_one zero_le_one)
      (ContinuousLinearMap.id ℂ _) (StartupRankOperator.identity rank dimension).coarse :=
  fixed _ _ id (fun _ => rfl) 1 1 zero_le_one zero_le_one budgetNonnegative
    (fun _ => (one_mul _).ge) (fun _ => (one_mul _).ge) (fun _ => rfl)

def scalar (dimension rank : ℕ) (scalar : ℂ) (budgetNonnegative : 0≤budget) :
    StartupCoreRankControl parameters budget (StartupCoreRankProfile.fixed ‖scalar‖ ‖scalar‖ (norm_nonneg _) (norm_nonneg _))
      (scalar • ContinuousLinearMap.id ℂ (StartupL2 dimension))
      ((StartupRankOperator.identity rank dimension).smul scalar).coarse :=
  fixed _ _ (fun core => scalar • core) (fun core => by rw [map_smul]; rfl)
    ‖scalar‖ ‖scalar‖ (norm_nonneg _) (norm_nonneg _) budgetNonnegative
    (fun core => (originalGradeNorm_smul 0 scalar core).le)
    (fun core => (originalGradeNorm_smul rank scalar core).le)
    (fun core => by rw [map_smul]; rfl)

def point (input output rank : ℕ) (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) (budgetNonnegative : 0≤budget) :
    StartupCoreRankControl parameters budget
      (StartupCoreRankProfile.fixed (‖mapping‖*orthogonalGradeConstant 0) (‖mapping‖*orthogonalGradeConstant rank)
        (mul_nonneg (norm_nonneg _) (orthogonalGradeConstant_nonnegative _))
        (mul_nonneg (norm_nonneg _) (orthogonalGradeConstant_nonnegative _)))
      (startupPointKernel mapping orthogonal) (StartupRankOperator.point rank mapping orthogonal).coarse :=
  fixed _ _ (startupOriginalPointCore parameters mapping orthogonal)
    (startupOriginalPointCore_sameField parameters mapping orthogonal)
    (‖mapping‖*orthogonalGradeConstant 0) (‖mapping‖*orthogonalGradeConstant rank)
    (mul_nonneg (norm_nonneg _) (orthogonalGradeConstant_nonnegative _))
    (mul_nonneg (norm_nonneg _) (orthogonalGradeConstant_nonnegative _)) budgetNonnegative
    (fun core => startupOriginalPointCore_bound parameters mapping orthogonal core 0)
    (fun core => startupOriginalPointCore_bound parameters mapping orthogonal core rank)
    (fun core => startupOriginalPoint_rank_exact parameters rank mapping orthogonal core _
      (startupOriginalPointCore_sameField parameters mapping orthogonal core))

def angular (dimension rank : ℕ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight)
    (bound : ℝ) (nonnegative : 0≤bound)
    (bounded : ∀ angle ∈ Icc (0 : ℝ) (2*Real.pi),‖weight angle‖≤bound) (budgetNonnegative : 0≤budget) :
    StartupCoreRankControl parameters budget
      (StartupCoreRankProfile.fixed (bound*orthogonalGradeConstant 0) (bound*orthogonalGradeConstant rank)
        (mul_nonneg nonnegative (orthogonalGradeConstant_nonnegative _))
        (mul_nonneg nonnegative (orthogonalGradeConstant_nonnegative _)))
      (startupAngularKernel dimension weight smooth) (StartupRankOperator.angular dimension rank weight smooth).coarse :=
  fixed _ _ (originalAngularKernelCore parameters weight smooth bound nonnegative bounded)
    (originalAngularKernelCore_sameField parameters weight smooth bound nonnegative bounded)
    (bound*orthogonalGradeConstant 0) (bound*orthogonalGradeConstant rank)
    (mul_nonneg nonnegative (orthogonalGradeConstant_nonnegative _))
    (mul_nonneg nonnegative (orthogonalGradeConstant_nonnegative _)) budgetNonnegative
    (fun core => originalAngularKernelCore_bound parameters weight smooth bound nonnegative bounded core 0)
    (fun core => originalAngularKernelCore_bound parameters weight smooth bound nonnegative bounded core rank)
    (fun core => startupOriginalAngular_rank_exact parameters rank weight smooth core _
      (originalAngularKernelCore_sameField parameters weight smooth bound nonnegative bounded core))

end StartupCoreRankControl
end Grad.CartesianStartup
