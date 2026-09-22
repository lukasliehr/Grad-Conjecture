import AKCG9ActualDisplacementHigherGraph
import AKCB15ActualAxialMomentRealization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

theorem startupDisplacementKernel_zero {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {grade input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (index : DerivativeIndex grade) :
    startupDisplacementKernel admissible family coherent index 0 = startupDerivativeKernel admissible family coherent index := by
  unfold startupDisplacementKernel startupDerivativeKernel
  refine startupKernel_congr _ _ ?_ ?_
  · rfl
  · intro outer inner
    filter_upwards [] with pair
    simp only [startupDisplacementKernelData, startupDerivativeKernelData, startupDisplacementCoefficient, pow_zero, one_smul]

def startupPositiveAxialRemainder {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (power : ℕ) (moments : ℕ → StartupL2 input) : StartupL2 output :=
  ∑ j : Fin power, (power.choose (j.val+1) : ℂ) •
    startupDisplacementKernel admissible family coherent zeroDerivativeIndex (j.val+1) (moments (power-(j.val+1)))

/-- The highest input axial derivative stays under the original matrix.
Every positive displacement uses a strictly lower input axial derivative. -/
theorem startupKernelAxialMoment_leadingSplit {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (power : ℕ) (moments : ℕ → StartupL2 input) :
    startupKernelAxialMoment admissible family coherent zeroDerivativeIndex power moments =
      originalMatrixKernel admissible family coherent (moments power) +
        startupPositiveAxialRemainder admissible family coherent power moments := by
  unfold startupKernelAxialMoment startupPositiveAxialRemainder
  rw [← Fin.sum_univ_eq_sum_range, Fin.sum_univ_succ]
  simp only [Fin.val_zero, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero, one_smul,
    startupDisplacementKernel_zero, Fin.val_succ]
  rfl

theorem startupPositiveAxialRemainder_lower (power : ℕ) (j : Fin power) : power - (j.val+1) < power := by
  have := j.isLt
  omega

end Grad.CartesianStartup
