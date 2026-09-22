import AKDA14SameInverseOriginalPhaseSchur

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularRadialSmoothness

/-- Actual operator derivatives of a full-kernel Euler tower. The original
kernel and its analytic width remain explicit in every grade. -/
def KernelEulerDerivativeTower {source target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernels : ℕ → (radius : RadialPoint) → RadialKernel parameters radius source target) : Prop :=
  ∀ rank radius, radius ∈ Icc lower 1 →
    HasDerivWithinAt (radialPolynomialAction parameters lower positive bounded (kernels rank) 0)
      (radius⁻¹ • radialPolynomialAction parameters lower positive bounded (kernels (rank+1)) 0 radius)
      (Icc lower 1) radius

theorem KernelEulerDerivativeTower.entry {source target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernels : ℕ → (radius : RadialPoint) → RadialKernel parameters radius source target)
    (tower : KernelEulerDerivativeTower parameters lower positive bounded kernels)
    (rank : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (shift input : ℤ × ℤ) :
    HasDerivWithinAt (fun point => (kernels rank (collarRadius lower positive bounded point)).entry shift input)
      (radius⁻¹ • (kernels (rank+1) (collarRadius lower positive bounded radius)).entry shift input)
      (Icc lower 1) radius := by
  let observe := (fourierEntryObservation (source := source) (target := target)
    ((twoFrequencyTranslation shift).symm input) input).restrictScalars ℝ
  have result := observe.hasFDerivAt.comp_hasDerivWithinAt radius (tower rank radius inside)
  change HasDerivWithinAt (fun point => fourierEntryObservation ((twoFrequencyTranslation shift).symm input) input
      (radialPolynomialAction parameters lower positive bounded (kernels rank) 0 point))
    (observe (radius⁻¹ • radialPolynomialAction parameters lower positive bounded (kernels (rank+1)) 0 radius))
    (Icc lower 1) radius at result
  rw [map_smul] at result
  change HasDerivWithinAt (fun point => fourierEntryObservation ((twoFrequencyTranslation shift).symm input) input
      (radialPolynomialAction parameters lower positive bounded (kernels rank) 0 point))
    (radius⁻¹ • fourierEntryObservation ((twoFrequencyTranslation shift).symm input) input
      (radialPolynomialAction parameters lower positive bounded (kernels (rank+1)) 0 radius)) (Icc lower 1) radius at result
  simpa only [radialPolynomialAction,fourierEntryObservation_kernel] using result

theorem actualRawEulerKernel_derivativeTower {source target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernels : ℕ → (radius : RadialPoint) → RadialKernel parameters radius source target)
    (derivative : ∀ rank radius, radius ∈ Icc lower 1 →
      HasDerivWithinAt (radialPolynomialAction parameters lower positive bounded (kernels rank) 0)
        (radialPolynomialAction parameters lower positive bounded (kernels (rank+1)) 0 radius) (Icc lower 1) radius) :
    KernelEulerDerivativeTower parameters lower positive bounded
      (fun rank radius => actualRawEulerKernel radius (fun raw => kernels raw radius) rank) := by
  intro rank radius inside
  let raw := fun order => radialPolynomialAction parameters lower positive bounded (kernels order) 0
  have result := actualRawEulerJets_hasDerivWithinAt (Icc lower 1) raw radius (positive.trans_le inside.1).ne'
    (fun order => derivative order radius inside) rank
  have same (order : ℕ) (point : ℝ) (member : point ∈ Icc lower 1) :
      radialPolynomialAction parameters lower positive bounded
        (fun radius => actualRawEulerKernel radius (fun raw => kernels raw radius) order) 0 point =
      actualRawEulerJets raw order point :=
    actualRawEulerKernel_collar_action parameters lower positive bounded kernels order point member
  rw [← same (rank+1) radius inside] at result
  apply result.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with point member
    exact same rank point member
  · exact same rank radius inside

end Grad.OriginalCartesianTameEstimate
