import GSP3PolarMatrixCoefficients

noncomputable section
open scoped BigOperators
set_option maxHeartbeats 1400000
namespace Grad.ActualGaugeSigmaPrimitives
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.SourceCollarCoefficients Grad.SourceCollarAngular
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

def polarEntryFourierTerm (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (slot : Fin 2 × Fin 2) (radial : ℕ) (radius : ℝ) : ℤ × ℤ → ComplexEuclidean 1 :=
  coefficientPolarFourier parameters (mappedMatrixFamily parameters family row slot.1)
    (mappedMatrixFamily_coherent parameters family coherent row slot.1) (kappaLaurentRight column slot.2) radial radius ∘
      angularModeTranslation (polarEntryFrequency row column slot)

def polarEntryFourier (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (radial : ℕ) (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  ∑ slot, polarEntryFourierTerm parameters family coherent row column slot radial radius mode

def polarEntryTermConstant (row column : Fin 3) (slot : Fin 2 × Fin 2) (tangential radial : ℕ) : ℝ :=
  (1 + |(polarEntryFrequency row column slot : ℝ)|) ^ tangential *
    (coefficientFourierConstant tangential radial * mappedMatrixConstant row slot.1 (tangential + radial + 1) *
      ‖kappaLaurentRight column slot.2‖)

def polarEntryConstant (row column : Fin 3) (tangential radial : ℕ) : ℝ :=
  1 + ∑ slot : Fin 2 × Fin 2, |polarEntryTermConstant row column slot tangential radial|

theorem polarEntryConstant_pos (row column : Fin 3) (tangential radial : ℕ) :
    0 < polarEntryConstant row column tangential radial := by
  unfold polarEntryConstant
  positivity

theorem polarEntryFourierTerm_summable (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (slot : Fin 2 × Fin 2) (tangential radial : ℕ)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (polarFourierMass parameters tangential radius
      (polarEntryFourierTerm parameters family coherent row column slot radial radius)) :=
  polarFourierMass_shift_summable parameters tangential radius _
    (coefficient_fourier_summable parameters _ (mappedMatrixFamily_coherent parameters family coherent row slot.1)
      (kappaLaurentRight column slot.2) tangential radial radius nonnegative bounded) _

theorem polarEntryFourierTerm_bound (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (slot : Fin 2 × Fin 2) (tangential radial : ℕ)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    ∑' mode, polarFourierMass parameters tangential radius
      (polarEntryFourierTerm parameters family coherent row column slot radial radius) mode ≤
        polarEntryTermConstant row column slot tangential radial * ‖family (tangential + radial + 1)‖ := by
  have summable := coefficient_fourier_summable parameters _
    (mappedMatrixFamily_coherent parameters family coherent row slot.1)
    (kappaLaurentRight column slot.2) tangential radial radius nonnegative bounded
  have base := coefficient_fourier_bound parameters _
    (mappedMatrixFamily_coherent parameters family coherent row slot.1)
    (kappaLaurentRight column slot.2) tangential radial radius nonnegative bounded
  have normBound := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mappedMatrixFamily_bound parameters family row slot.1 (tangential + radial + 1))
      (coefficientFourierConstant_nonnegative tangential radial)) (norm_nonneg (kappaLaurentRight column slot.2))
  have shift := polarFourierMass_shift_bound parameters tangential radius _ summable (polarEntryFrequency row column slot)
  have bound := mul_le_mul_of_nonneg_left (base.trans normBound)
    (by positivity : 0 ≤ (1 + |(polarEntryFrequency row column slot : ℝ)|) ^ tangential)
  exact shift.trans (bound.trans_eq (by unfold polarEntryTermConstant; ring))

theorem polarEntryFourier_summable (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (tangential radial : ℕ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (polarFourierMass parameters tangential radius (polarEntryFourier parameters family coherent row column radial radius)) :=
  polarFourierMass_sum_summable parameters tangential radius _
    (fun slot => polarEntryFourierTerm_summable parameters family coherent row column slot tangential radial radius nonnegative bounded)

theorem polarEntryFourier_bound (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 3 3) (coherent : FamilyCoherent family)
    (row column : Fin 3) (tangential radial : ℕ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    ∑' mode, polarFourierMass parameters tangential radius (polarEntryFourier parameters family coherent row column radial radius) mode ≤
      polarEntryConstant row column tangential radial * ‖family (tangential + radial + 1)‖ := by
  have total := polarFourierMass_sum_bound parameters tangential radius _
    (fun slot => polarEntryFourierTerm_summable parameters family coherent row column slot tangential radial radius nonnegative bounded)
  have bounds := Finset.sum_le_sum (s := Finset.univ) (fun slot _ =>
    polarEntryFourierTerm_bound parameters family coherent row column slot tangential radial radius nonnegative bounded)
  rw [← Finset.sum_mul] at bounds
  have constants : (∑ slot : Fin 2 × Fin 2, polarEntryTermConstant row column slot tangential radial) ≤
      polarEntryConstant row column tangential radial := by
    have absolute := Finset.sum_le_sum (s := Finset.univ) (fun slot _ =>
      le_abs_self (polarEntryTermConstant row column slot tangential radial))
    unfold polarEntryConstant
    linarith
  exact total.trans (bounds.trans (mul_le_mul_of_nonneg_right constants (norm_nonneg _)))

end Grad.ActualGaugeSigmaPrimitives
