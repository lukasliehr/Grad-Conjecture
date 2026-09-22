import SCC11PolarFourierBound

noncomputable section
open Set
open scoped BigOperators

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.SourceCollarDivision Grad.SourceCollarRestriction

def coefficientFourierWeightedNorm {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (column : PhysicalValue input)
    (tangential radial : ℕ) (radius : ℝ) (mode : ℤ × ℤ) : ℝ :=
  coefficientRadialEnvelope parameters mode.2 radius * annularFrequency mode.1 mode.2 ^ tangential *
    ‖coefficientPolarFourier parameters family coherent column radial radius mode‖

theorem coefficientFourierWeightedNorm_nonnegative {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (column : PhysicalValue input)
    (tangential radial : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    0 ≤ coefficientFourierWeightedNorm parameters family coherent column tangential radial radius mode :=
  mul_nonneg (mul_nonneg (coefficientRadialEnvelope_pos _ _ _).le
    (pow_nonneg (annularFrequency_nonnegative _ _) _)) (norm_nonneg _)

theorem coefficient_fourier_finite {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (column : PhysicalValue input)
    (tangential radial : ℕ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (modes : Finset (ℤ × ℤ)) :
    ∑ mode ∈ modes, coefficientFourierWeightedNorm parameters family coherent column tangential radial radius mode ≤
      coefficientFourierConstant tangential radial * ‖family (tangential + radial + 1)‖ * ‖column‖ := by
  classical
  have rectangular : modes ⊆ modes.image Prod.fst ×ˢ modes.image Prod.snd := by
    intro mode member
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨mode, member, rfl⟩,
      Finset.mem_image.mpr ⟨mode, member, rfl⟩⟩
  calc
    _ ≤ ∑ mode ∈ modes.image Prod.fst ×ˢ modes.image Prod.snd,
        coefficientFourierWeightedNorm parameters family coherent column tangential radial radius mode :=
      Finset.sum_le_sum_of_subset_of_nonneg rectangular (fun mode _ _ =>
        coefficientFourierWeightedNorm_nonnegative parameters family coherent column tangential radial radius mode)
    _ = ∑ cell ∈ modes.image Prod.snd, ∑ mode ∈ modes.image Prod.fst,
        coefficientFourierWeightedNorm parameters family coherent column tangential radial radius (mode, cell) := by
      rw [Finset.sum_product, Finset.sum_comm]
    _ ≤ ∑ cell ∈ modes.image Prod.snd, coefficientFourierConstant tangential radial *
        (coefficientCellBudget (family (tangential + radial + 1)) cell * ‖column‖) :=
      Finset.sum_le_sum (fun cell _ => coefficient_fourier_cell_finite parameters family coherent column
        tangential radial cell radius nonnegative bounded _)
    _ = coefficientFourierConstant tangential radial *
        (∑ cell ∈ modes.image Prod.snd, coefficientCellBudget (family (tangential + radial + 1)) cell) * ‖column‖ := by
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro cell _
      ring
    _ ≤ coefficientFourierConstant tangential radial *
        (∑' cell, coefficientCellBudget (family (tangential + radial + 1)) cell) * ‖column‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        ((coefficientCellBudget_summable _).sum_le_tsum _
          (fun cell _ => coefficientCellBudget_nonnegative _ cell))
        (coefficientFourierConstant_nonnegative _ _)) (norm_nonneg _)
    _ = _ := by rw [coefficientCellBudget_tsum]

theorem coefficient_fourier_summable {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (column : PhysicalValue input)
    (tangential radial : ℕ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (coefficientFourierWeightedNorm parameters family coherent column tangential radial radius) :=
  summable_of_sum_le (coefficientFourierWeightedNorm_nonnegative parameters family coherent column tangential radial radius)
    (coefficient_fourier_finite parameters family coherent column tangential radial radius nonnegative bounded)

/-- The literal full (m,n) AP8-to-angular-l1 conversion costs precisely one
additional Cartesian grade, uniformly throughout the original closed disk. -/
theorem coefficient_fourier_bound {input output : ℕ} (parameters : PhaseParameters)
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (column : PhysicalValue input)
    (tangential radial : ℕ) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    ∑' mode, coefficientFourierWeightedNorm parameters family coherent column tangential radial radius mode ≤
      coefficientFourierConstant tangential radial * ‖family (tangential + radial + 1)‖ * ‖column‖ :=
  Real.tsum_le_of_sum_le
    (coefficientFourierWeightedNorm_nonnegative parameters family coherent column tangential radial radius)
    (coefficient_fourier_finite parameters family coherent column tangential radial radius nonnegative bounded)

end Grad.SourceCollarCoefficients
