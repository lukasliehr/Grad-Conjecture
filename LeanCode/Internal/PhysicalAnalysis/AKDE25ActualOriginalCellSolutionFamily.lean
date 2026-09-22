import AKDE23LiteralConstructedCellFamily
import AKDE24ConstructedWindowFromOpenness
import AKDI6OriginalSeedZeroSource

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
open scoped ContDiff
namespace Grad.OriginalCellFamily
open Grad.CartesianState Grad.Constraints Grad.PhysicalFamily Grad.NashMoser.OriginalIteration
open Grad.NashMoser.OriginalLimit Grad.OriginalZeroSeed

variable {parameters : PhaseParameters} {reference : Seed.Parameters}
    {inside : reference ∈ Seed.parameterDomain} {base loss : ℕ} {cellLength : ℝ}
    {neighborhood : OriginalNewtonNeighborhood parameters reference inside base}
    {inverse : OriginalNewtonInverse neighborhood cellLength loss}

/-- Actual literal family of the SAME constructed original Newton limit.
Zero seed, all four PDE rows, normalized first jets, reality, smoothness,
periodicity and the physical C2 estimate are proved. The remaining
analytic input is exactly the original quantitative inverse/neighborhood. -/
def actualOriginalCellFamily (scale : OriginalNewtonScale inverse) (window : ConstructedParameterWindow scale)
    (leftLaw : inverse.LeftLaw) : CellSolutionFamily cellLength :=
  window.cellFamily scale leftLaw (fun parameter member => by
    have zeroIn : (0 : ℝ)∈Ioo (-window.radius) window.radius := ⟨by linarith [window.positive],window.positive⟩
    have pointIn := window.included 0 zeroIn parameter member
    apply scale.parameterLimit_zero_branch _ pointIn
    exact originalNonlinearSource_seed_zero (parameters := parameters) cellLength reference inside
      (![window.rho,window.alpha,window.delta,parameter] : Seed.Parameters)
      (scale.parameterLimit_admissible _ pointIn).1)

/-- A good zero seed in the actual original parameter neighborhood yields
an actual CellSolutionFamily; no family or geometric window is assumed. -/
theorem actualOriginalCellFamily_exists (scale : OriginalNewtonScale inverse) (leftLaw : inverse.LeftLaw)
    (rho alpha delta parameter : ℝ) (rhoPositive : 0 < rho) (rhoSmall : rho < 1/4)
    (deltaNonzero : delta ≠ 0)
    (alphaNonresonant : ∀ multiple : ℤ, alpha ≠ (Real.pi/2)*(multiple:ℝ))
    (parameterPositive : 0 < parameter) (parameterSmall : parameter < 1/2)
    (member : cellFiniteParameter rho alpha delta 0 parameter ∈ interior neighborhood.parameterDomain) :
    Nonempty (CellSolutionFamily cellLength) := by
  have seedInside : (![rho,alpha,delta,parameter] : Seed.Parameters)∈Seed.parameterDomain := by
    change |rho| < 1
    rw [abs_of_pos rhoPositive]
    linarith
  have pointIn := scale.openParameterDomain_contains_zero (cellFiniteParameter rho alpha delta 0 parameter) member
    (originalNonlinearSource_seed_zero (parameters := parameters) cellLength reference inside _ seedInside)
  obtain ⟨window⟩ := exists_constructedParameterWindow scale rho alpha delta parameter rhoPositive rhoSmall deltaNonzero
    alphaNonresonant parameterPositive parameterSmall pointIn
  exact ⟨actualOriginalCellFamily scale window leftLaw⟩

end Grad.OriginalCellFamily
