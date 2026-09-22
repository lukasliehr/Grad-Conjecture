import ANG13RotationSpectrum
import GQC20ProductDerivativeL2

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open scoped BigOperators
namespace Grad.CircularHighWeak
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated

abbrev unitSobolevRow (grade : ℕ) : ClosedJet 1 →ₗ[ℂ] APRow 1 grade := apRowLinear 1 0 0 1 0

theorem unitSobolevRow_coordinate (grade : ℕ) (field : ClosedJet 1) (index : DerivativeIndex grade) :
    unitSobolevRow grade field index = closedDerivativeL2 (derivativeMultiIndex index) field := by
  rw [apRowLinear_apply, unweightedJet]
  simp only [show scaledCellWeight 1 1 0 = 1 by norm_num [scaledCellWeight], Complex.ofReal_one, one_pow, one_smul]

theorem unitSobolev_derivative_bound (grade : ℕ) (field : ClosedJet 1) (index : DerivativeIndex grade) :
    ‖closedDerivativeL2 (derivativeMultiIndex index) field‖ ≤ ‖unitSobolevRow grade field‖ :=
  (congrArg norm (unitSobolevRow_coordinate grade field index)).symm.le.trans (PiLp.norm_apply_le _ index)

def unitProductIndexConstant {grade : ℕ} (coefficient : SmoothOperatorJet 1 1) (index : DerivativeIndex grade) : ℝ :=
  ∑ split : DerivativeSplit index, (splitMultiplicity index split : ℝ) *
    ‖smoothOperatorDerivative coefficient (derivativeMultiIndex (lowerDerivativeIndex index split))‖

theorem unitProductIndexConstant_nonnegative {grade : ℕ} (coefficient : SmoothOperatorJet 1 1) (index : DerivativeIndex grade) :
    0 ≤ unitProductIndexConstant coefficient index :=
  Finset.sum_nonneg (fun split _ => mul_nonneg (Nat.cast_nonneg _)
    (norm_nonneg (smoothOperatorDerivative coefficient (derivativeMultiIndex (lowerDerivativeIndex index split)))))

theorem unitProduct_index_bound {grade : ℕ} (coefficient : SmoothOperatorJet 1 1) (field : ClosedJet 1)
    (index : DerivativeIndex grade) :
    ‖closedDerivativeL2 (derivativeMultiIndex index) (apProductJet coefficient field)‖ ≤
      unitProductIndexConstant coefficient index * ‖unitSobolevRow grade field‖ := by
  refine (apProductJet_derivativeL2_bound coefficient field index).trans ?_
  rw [unitProductIndexConstant, Finset.sum_mul]
  exact Finset.sum_le_sum (fun split _ => mul_le_mul_of_nonneg_left
    (unitSobolev_derivative_bound grade field (upperDerivativeIndex index split))
    (mul_nonneg (Nat.cast_nonneg _)
      (norm_nonneg (smoothOperatorDerivative coefficient (derivativeMultiIndex (lowerDerivativeIndex index split))))))

def unitProductConstant (grade : ℕ) (coefficient : SmoothOperatorJet 1 1) : ℝ :=
  Real.sqrt (Fintype.card (DerivativeIndex grade)) * ∑ index : DerivativeIndex grade, unitProductIndexConstant coefficient index

theorem unitProductConstant_nonnegative (grade : ℕ) (coefficient : SmoothOperatorJet 1 1) :
    0 ≤ unitProductConstant grade coefficient :=
  mul_nonneg (Real.sqrt_nonneg _) (Finset.sum_nonneg (fun index _ => unitProductIndexConstant_nonnegative coefficient index))

/-- Raw Leibniz estimates at the ordinary disk norm require no analytically
weighted admissibility hypothesis, which would be false at sigma=gamma=0. -/
theorem unitProduct_bound (grade : ℕ) (coefficient : SmoothOperatorJet 1 1) (field : ClosedJet 1) :
    ‖unitSobolevRow grade (apProductJet coefficient field)‖ ≤ unitProductConstant grade coefficient * ‖unitSobolevRow grade field‖ := by
  have positive : 0 ≤ ∑ index : DerivativeIndex grade, unitProductIndexConstant coefficient index :=
    Finset.sum_nonneg (fun index _ => unitProductIndexConstant_nonnegative coefficient index)
  have bound := apRow_norm_bound_of_coordinates (unitSobolevRow grade (apProductJet coefficient field))
    ((∑ index : DerivativeIndex grade, unitProductIndexConstant coefficient index) * ‖unitSobolevRow grade field‖)
    (mul_nonneg positive (norm_nonneg _)) (fun index => by
      rw [unitSobolevRow_coordinate]
      exact (unitProduct_index_bound coefficient field index).trans (mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (fun other _ => unitProductIndexConstant_nonnegative coefficient other) (Finset.mem_univ index))
        (norm_nonneg _)))
  exact bound.trans_eq (mul_assoc _ _ _).symm

end Grad.CircularHighWeak
