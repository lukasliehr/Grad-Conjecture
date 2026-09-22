import AIX6CompletedActualUnitaryOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKernelOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction

/-- The exact mixed-jet Taylor residual at a two-dimensional angular/cell increment. -/
def orbitRemainderFactor (tau step : OrbitParameter) (angular cell : ℕ) (shift : ℤ × ℤ) : ℂ :=
  orbitJetFactor tau angular cell shift *
    (orbitCharacter step shift - 1 - Complex.I * (orbitAngle step shift : ℂ))

theorem orbitRemainderFactor_identity (tau step : OrbitParameter) (angular cell : ℕ) (shift : ℤ × ℤ) :
    orbitJetFactor (tau + step) angular cell shift - orbitJetFactor tau angular cell shift -
      (step.1 : ℂ) * orbitJetFactor tau (angular + 1) cell shift -
      (step.2 : ℂ) * orbitJetFactor tau angular (cell + 1) shift =
    orbitRemainderFactor tau step angular cell shift := by
  simp only [orbitRemainderFactor, orbitJetFactor, orbitCharacter_add, pow_succ, orbitAngle]
  push_cast
  ring

theorem orbitRemainderFactor_bound (tau step : OrbitParameter) (angular cell : ℕ) (shift : ℤ × ℤ) :
    ‖orbitRemainderFactor tau step angular cell shift‖ ≤
      (3 * orbitStepSize step ^ 2) * annularFrequency shift.1 shift.2 ^ (angular + cell + 2) := by
  have angleBound := orbitAngle_bound step shift
  have sizeNonnegative : 0 ≤ orbitStepSize step := add_nonneg (abs_nonneg _) (abs_nonneg _)
  have squareBound : |orbitAngle step shift| ^ 2 ≤
      (annularFrequency shift.1 shift.2 * orbitStepSize step) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) angleBound 2
  have factorBound := orbitJetFactor_bound tau angular cell shift
  rw [one_mul] at factorBound
  calc
    _ = ‖orbitJetFactor tau angular cell shift‖ *
        ‖orbitCharacter step shift - 1 - Complex.I * (orbitAngle step shift : ℂ)‖ := norm_mul _ _
    _ ≤ annularFrequency shift.1 shift.2 ^ (angular + cell) * (3 * |orbitAngle step shift| ^ 2) :=
      mul_le_mul factorBound (imaginaryExp_remainder_bound _) (norm_nonneg _)
        (pow_nonneg (annularFrequency_pos shift).le _)
    _ ≤ annularFrequency shift.1 shift.2 ^ (angular + cell) *
        (3 * (annularFrequency shift.1 shift.2 * orbitStepSize step) ^ 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left squareBound (by norm_num))
        (pow_nonneg (annularFrequency_pos shift).le _)
    _ = _ := by rw [pow_add]; ring

variable {src tgt : ℕ} {parameters : PhaseParameters}

def kernelOrbitRemainder (tau step : OrbitParameter) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters src tgt) : FullTwoFrequencyKernel parameters src tgt :=
  displacementKernel kernel (orbitRemainderFactor tau step angular cell) (angular + cell + 2)
    (3 * orbitStepSize step ^ 2) (by positivity) (orbitRemainderFactor_bound tau step angular cell)

theorem kernelOrbitRemainder_identity (tau step : OrbitParameter) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters src tgt) :
    kernelOrbitRemainder tau step angular cell kernel =
      fullKernelSub
        (fullKernelSub (fullKernelSub (kernelOrbitJet (tau + step) angular cell kernel)
          (kernelOrbitJet tau angular cell kernel))
          (fullKernelSmul (step.1 : ℂ) (kernelOrbitJet tau (angular + 1) cell kernel)))
        (fullKernelSmul (step.2 : ℂ) (kernelOrbitJet tau angular (cell + 1) kernel)) := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift input
  simp only [kernelOrbitRemainder, kernelOrbitJet, displacementKernel_entry,
    fullKernelSub_entry, fullKernelSmul_entry, smul_smul]
  rw [← orbitRemainderFactor_identity]
  module

theorem kernelOrbitRemainder_moment_le (tau step : OrbitParameter) (angular cell : ℕ)
    (kernel : FullTwoFrequencyKernel parameters src tgt) (moment : ℕ) :
    fullKernelMoment parameters moment (kernelOrbitRemainder tau step angular cell kernel) ≤
      (3 * orbitStepSize step ^ 2) * fullKernelMoment parameters (moment + (angular + cell + 2)) kernel :=
  displacementKernel_moment_le kernel _ _ _ _ _ _

end Grad.AnnularKernelOrbit
