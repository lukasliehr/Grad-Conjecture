import AKDD5CompositionJointPhysicalAllocation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularRadialSmoothness

attribute [local irreducible] fullKernelAdd fullKernelNeg fullKernelSmul polynomialKernelAction

theorem kernelEulerTower_of_realization {source target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernels : ℕ → (radius : RadialPoint) → RadialKernel parameters radius source target)
    (jets : ℕ → ℝ → (CellL2 source →L[ℂ] CellL2 target))
    (same : ∀ rank point, radialPolynomialAction parameters lower positive bounded (kernels rank) 0 point = jets rank point)
    (derivative : ∀ rank radius, radius ∈ Icc lower 1 →
      HasDerivWithinAt (jets rank) (radius⁻¹ • jets (rank+1) radius) (Icc lower 1) radius) :
    KernelEulerDerivativeTower parameters lower positive bounded kernels := by
  intro rank radius inside
  have result := derivative rank radius inside
  rw [← same (rank+1) radius] at result
  apply result.congr_of_eventuallyEq
  · exact Filter.Eventually.of_forall (same rank)
  · exact same rank radius

theorem KernelEulerDerivativeTower.add {source target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (first second : ℕ → (radius : RadialPoint) → RadialKernel parameters radius source target)
    (one : KernelEulerDerivativeTower parameters lower positive bounded first)
    (two : KernelEulerDerivativeTower parameters lower positive bounded second) :
    KernelEulerDerivativeTower parameters lower positive bounded
      (fun rank radius => fullKernelAdd (first rank radius) (second rank radius)) := by
  apply kernelEulerTower_of_realization parameters lower positive bounded
    (fun rank radius => fullKernelAdd (first rank radius) (second rank radius))
    (fun rank point => radialPolynomialAction parameters lower positive bounded (first rank) 0 point+
      radialPolynomialAction parameters lower positive bounded (second rank) 0 point)
    (fun rank point => polynomialKernelAction_add
      (radialKernelParameters parameters (collarRadius lower positive bounded point)) 0
      (first rank (collarRadius lower positive bounded point))
      (second rank (collarRadius lower positive bounded point)))
  intro rank radius inside
  rw [smul_add]
  exact (one rank radius inside).add (two rank radius inside)

theorem KernelEulerDerivativeTower.neg {source target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernels : ℕ → (radius : RadialPoint) → RadialKernel parameters radius source target)
    (tower : KernelEulerDerivativeTower parameters lower positive bounded kernels) :
    KernelEulerDerivativeTower parameters lower positive bounded
      (fun rank radius => fullKernelNeg (kernels rank radius)) := by
  apply kernelEulerTower_of_realization parameters lower positive bounded
    (fun rank radius => fullKernelNeg (kernels rank radius))
    (fun rank point => -radialPolynomialAction parameters lower positive bounded (kernels rank) 0 point)
    (fun rank point => polynomialKernelAction_neg
      (radialKernelParameters parameters (collarRadius lower positive bounded point)) 0
      (kernels rank (collarRadius lower positive bounded point)))
  intro rank radius inside
  rw [smul_neg]
  exact (tower rank radius inside).neg

/-- Fixed Fourier kernels have only their literal rank-zero value. -/
def fixedEulerKernel {source target : ℕ} (parameters : PhaseParameters)
    (family : (phase : PhaseParameters) → FullTwoFrequencyKernel phase source target)
    (rank : ℕ) (radius : RadialPoint) : RadialKernel parameters radius source target :=
  Nat.casesOn rank (family (radialKernelParameters parameters radius))
    (fun _ => fullKernelSmul 0 (family (radialKernelParameters parameters radius)))

theorem fixedEulerKernel_derivativeTower {source target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (family : (phase : PhaseParameters) → FullTwoFrequencyKernel phase source target)
    (same : ∀ first second, SameKernelEntries (family first) (family second)) :
    KernelEulerDerivativeTower parameters lower positive bounded (fixedEulerKernel parameters family) := by
  let jets : ℕ → ℝ → (CellL2 source →L[ℂ] CellL2 target) :=
    fun rank (_ : ℝ) => Nat.casesOn rank (polynomialKernelAction parameters 0 (family parameters)) (fun _ => 0)
  apply kernelEulerTower_of_realization parameters lower positive bounded _ jets
  · intro rank point
    cases rank with
    | zero => exact polynomialKernelAction_congr _ parameters 0 _ _ (same _ _)
    | succ rank =>
        change polynomialKernelAction _ 0 (fullKernelSmul (0 : ℂ) _) = 0
        rw [polynomialKernelAction_smul,zero_smul ℂ]
  · intro rank radius _
    change HasDerivWithinAt (jets rank)
      (radius⁻¹ • (0 : CellL2 source →L[ℂ] CellL2 target)) (Icc lower 1) radius
    rw [smul_zero]
    exact hasDerivWithinAt_const radius (Icc lower 1) (jets rank radius)

theorem fixedEulerKernel_moment {source target : ℕ} (parameters : PhaseParameters)
    (family : (phase : PhaseParameters) → FullTwoFrequencyKernel phase source target)
    (same : ∀ first second, SameKernelEntries (family first) (family second))
    (rank moment : ℕ) (radius : RadialPoint) :
    fullKernelMoment (radialKernelParameters parameters radius) moment (fixedEulerKernel parameters family rank radius) ≤
      fullKernelMoment (maximalKernelParameters parameters) moment (family (maximalKernelParameters parameters)) := by
  cases rank with
  | zero => exact SameKernelEntries.radialMoment_le parameters radius moment (same _ _)
  | succ rank =>
      exact (fullKernelSmul_moment_le 0 _ moment).trans ((by simp : ‖(0 : ℂ)‖ *
        fullKernelMoment (radialKernelParameters parameters radius) moment (family (radialKernelParameters parameters radius)) = 0).le.trans
          (fullKernelMoment_nonnegative _ _ _))

end Grad.OriginalCartesianTameEstimate
