import GQC22WeightedPartialIdentity

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope

theorem weightedPartialDerivative_bound {dimension grade : ℕ} (L sigma gamma ell : ℝ)
    (cell : ℤ) (coordinate : Fin 2) (field : ClosedJet dimension) (index : DerivativeIndex grade) :
    scaledCellWeight L ell cell ^ (grade - derivativeOrder index) *
      ‖closedDerivativeL2 (derivativeMultiIndex index) (partialJet coordinate (apWeightedJet sigma gamma ell cell field))‖ ≤
      ‖apRowLinear (grade := grade + 1) L sigma gamma ell cell field‖ := by
  change scaledCellWeight L ell cell ^ (grade - derivativeOrder index) *
    ‖closedContinuousToDiskL2 (closedDerivative (shiftedClosedJet (apWeightedJet sigma gamma ell cell field)
      (fun _ : Fin 1 => coordinate)) (cartesianOrder (derivativeMultiIndex index))
        (cartesianMultiIndexWord (derivativeMultiIndex index)))‖ ≤ _
  rw [shiftedClosedJet_closedDerivative]
  have bound := apWeighted_word_bound L sigma gamma ell cell field
    (Nat.add_le_add_right index.property 1)
    (Fin.append (cartesianMultiIndexWord (derivativeMultiIndex index)) (fun _ : Fin 1 => coordinate))
  simpa only [Nat.add_sub_add_right, derivativeOrder, cartesianOrder, derivativeMultiIndex] using bound

theorem partialRow_coordinate_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (cell : ℤ) (coordinate : Fin 2) (field : ClosedJet dimension) (index : DerivativeIndex grade) :
    ‖apRowLinear (grade := grade) L sigma gamma ell cell (partialJet coordinate field) index‖ ≤
      (1 + phaseProductIndexConstant L gamma index) * ‖apRowLinear (grade := grade + 1) L sigma gamma ell cell field‖ := by
  rw [apRowLinear_apply, norm_smul, Complex.norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (scaledCellWeight_nonnegative L ell cell), apWeightedJet_partial, map_sub]
  apply (mul_le_mul_of_nonneg_left (norm_sub_le _ _) (pow_nonneg (scaledCellWeight_nonnegative L ell cell) _)).trans
  rw [mul_add, add_mul, one_mul]
  exact add_le_add (weightedPartialDerivative_bound L sigma gamma ell cell coordinate field index)
    (phaseProduct_derivative_bound admissible cell coordinate field index)

def partialRowConstant (L gamma : ℝ) (grade : ℕ) : ℝ :=
  Real.sqrt (Fintype.card (DerivativeIndex grade)) *
    (1 + ∑ index : DerivativeIndex grade, phaseProductIndexConstant L gamma index)

theorem partialRowConstant_nonnegative {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    0 ≤ partialRowConstant L gamma grade :=
  mul_nonneg (Real.sqrt_nonneg _) (add_nonneg zero_le_one
    (Finset.sum_nonneg (fun index _ => phaseProductIndexConstant_nonnegative admissible index)))

/-- The literal unweighted Cartesian derivative costs one original AP2
grade. The constant is independent of ell, Fourier cell and field. -/
theorem partialRow_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (cell : ℤ) (coordinate : Fin 2) (field : ClosedJet dimension) :
    ‖apRowLinear (grade := grade) L sigma gamma ell cell (partialJet coordinate field)‖ ≤
      partialRowConstant L gamma grade * ‖apRowLinear (grade := grade + 1) L sigma gamma ell cell field‖ := by
  have constantsNonnegative : 0 ≤ 1 + ∑ index : DerivativeIndex grade, phaseProductIndexConstant L gamma index :=
    add_nonneg zero_le_one (Finset.sum_nonneg (fun index _ => phaseProductIndexConstant_nonnegative admissible index))
  have bound := apRow_norm_bound_of_coordinates
    (apRowLinear (grade := grade) L sigma gamma ell cell (partialJet coordinate field))
    ((1 + ∑ index : DerivativeIndex grade, phaseProductIndexConstant L gamma index) *
      ‖apRowLinear (grade := grade + 1) L sigma gamma ell cell field‖)
    (mul_nonneg constantsNonnegative (norm_nonneg _)) (fun index =>
      (partialRow_coordinate_bound admissible cell coordinate field index).trans
        (mul_le_mul_of_nonneg_right (add_le_add le_rfl (Finset.single_le_sum
          (fun candidate _ => phaseProductIndexConstant_nonnegative admissible candidate) (Finset.mem_univ index))) (norm_nonneg _)))
  exact bound.trans_eq (mul_assoc _ _ _).symm

def partialJetLinear (dimension : ℕ) (coordinate : Fin 2) : ClosedJet dimension →ₗ[ℂ] ClosedJet dimension where
  toFun := partialJet coordinate
  map_add' first second := by
    apply closedJet_eq_of_value_eq
    exact closedJetAdd_derivative first second 1 (fun _ => coordinate)
  map_smul' scalar field := by
    apply closedJet_eq_of_value_eq
    exact closedJetSmul_derivative scalar field 1 (fun _ => coordinate)

end Grad.GaugeCoefficients.Physical.Compensated
