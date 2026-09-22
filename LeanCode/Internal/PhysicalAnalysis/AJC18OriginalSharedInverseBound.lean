import AJC17OriginalCoupledGraph
import AIY14OriginalStrongDataIsomorphism

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
namespace Grad.AnnularStrongSolution
open Grad.CartesianState Grad.AnnularVariational Grad.AnnularCoupledInverse Grad.AnnularCrossMaps
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow Grad.AnnularHighTilt Grad.AnnularLowEnergy
open Grad.AnnularStrongData Grad.AnnularFullSource Grad.AnnularReconstruction
open Grad.AnnularCurrentSource Grad.GaugeCoefficients.Physical.Allocation

private theorem composeThreeBounds {E F G H : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedAddCommGroup H]
    (weight : E → F) (solve : F → G) (unweight : G → H) (a b c : ℝ)
    (aNonnegative : 0 ≤ a) (bNonnegative : 0 ≤ b)
    (weightBound : ∀ x, ‖weight x‖ ≤ c * ‖x‖)
    (solveBound : ∀ x, ‖solve x‖ ≤ b * ‖x‖)
    (unweightBound : ∀ x, ‖unweight x‖ ≤ a * ‖x‖) (data : E) :
    ‖unweight (solve (weight data))‖ ≤ a * b * c * ‖data‖ := by
  exact (unweightBound _).trans
    ((mul_le_mul_of_nonneg_left (solveBound _) aNonnegative).trans
      ((mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (weightBound data) bNonnegative) aNonnegative).trans_eq (by ring)))

private theorem radialBoundProduct (A B C N lower : ℝ) (positive : 0 < lower) :
    (A * lower⁻¹) * B * (C * lower ^ (-9 / 4 : ℝ)) * N =
      (A * B * C) * lower ^ (-13 / 4 : ℝ) * N := by
  have powers : lower⁻¹ * lower ^ (-9 / 4 : ℝ) = lower ^ (-13 / 4 : ℝ) := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add positive]
    norm_num
  calc
    _ = (A * B * C) * (lower⁻¹ * lower ^ (-9 / 4 : ℝ)) * N := by ring
    _ = _ := by rw [powers]

private theorem composeRadialBounds {E F G H : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [NormedAddCommGroup H]
    (weight : E → F) (solve : F → G) (unweight : G → H) (A B C lower : ℝ)
    (positive : 0 < lower) (aNonnegative : 0 ≤ A) (bNonnegative : 0 ≤ B)
    (weightBound : ∀ x, ‖weight x‖ ≤ (C * lower ^ (-9 / 4 : ℝ)) * ‖x‖)
    (solveBound : ∀ x, ‖solve x‖ ≤ B * ‖x‖)
    (unweightBound : ∀ x, ‖unweight x‖ ≤ (A * lower⁻¹) * ‖x‖) (data : E) :
    ‖unweight (solve (weight data))‖ ≤ (A * B * C) * lower ^ (-13 / 4 : ℝ) * ‖data‖ := by
  exact (composeThreeBounds weight solve unweight (A * lower⁻¹) B (C * lower ^ (-9 / 4 : ℝ))
    (mul_nonneg aNonnegative (inv_nonneg.mpr positive.le)) bNonnegative weightBound solveBound unweightBound data).trans_eq
      (radialBoundProduct A B C ‖data‖ lower positive)

def originalSharedInverseConstant (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  originalCoupledUnweightConstant parameters L * (2 * independentCoupledDataConstant parameters L compact) *
    (10 + originalLowIncomingConstant parameters L)

theorem originalSharedInverseConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ)
    (lengthPositive : 0 < L) : 0 ≤ originalSharedInverseConstant parameters L compact := by
  have first := originalCoupledUnweightConstant_nonnegative parameters L lengthPositive
  have second := independentCoupledDataConstant_nonnegative parameters L compact
  have third := lowOuterFrequencyConstant_two_le L lengthPositive
  have fourth : 1 ≤ lowBalanceConstant L parameters.gamma := le_max_left _ _
  unfold originalSharedInverseConstant originalLowIncomingConstant
  positivity

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters L compact)

/-- SAME shared-source inverse in the original AK high and AJ low coordinates. -/
def originalSharedResponse (data : OriginalStrongCarrier parameters lower 0 0) : OriginalCoupledSpace lower L positive :=
  (originalCoupledEquivalence parameters lower L positive (lowerHalf.trans (by norm_num)) lengthPositive).symm
    (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
      (originalStrongWeightEquivalence parameters lower L positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data))

/-- Base BF25 in the literal original source and solution graph norms. The
single B8 ball is unchanged, and C precedes lower and the physical state. -/
theorem originalSharedResponse_bound (data : OriginalStrongCarrier parameters lower 0 0) :
    ‖originalSharedResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data‖ ≤
      originalSharedInverseConstant parameters L compact * lower ^ (-13 / 4 : ℝ) * ‖data‖ := by
  exact composeRadialBounds
    (E := OriginalStrongCarrier parameters lower 0 0)
    (F := StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (G := CoupledSpace lower L positive lengthPositive)
    (H := OriginalCoupledSpace lower L positive)
    (fun x => originalStrongWeightEquivalence parameters lower L positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 x)
    (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (fun x => (originalCoupledEquivalence parameters lower L positive (lowerHalf.trans (by norm_num)) lengthPositive).symm x)
    (originalCoupledUnweightConstant parameters L)
    (2 * independentCoupledDataConstant parameters L compact)
    (10 + originalLowIncomingConstant parameters L) lower positive
    (originalCoupledUnweightConstant_nonnegative parameters L lengthPositive)
    (mul_nonneg (by norm_num) (independentCoupledDataConstant_nonnegative parameters L compact))
    (originalStrongWeightEquivalence_bound parameters lower L positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0)
    (sharedStrongResponse_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (originalCoupledEquivalence_inverse_bound parameters lower L positive (lowerHalf.trans (by norm_num)) lengthPositive) data

end Grad.AnnularStrongSolution
