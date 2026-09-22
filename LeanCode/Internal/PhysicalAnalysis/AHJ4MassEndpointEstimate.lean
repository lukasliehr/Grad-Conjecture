import AHJ3MassInterpolationAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.NonlinearProduct Grad.FourierInterpolation

def apMassEndpointBase (low high : ℕ) : ℝ :=
  1 + ∑ order : Fin (high + 1), originalInterpolationConstant low order.val high

theorem apMassEndpointBase_one_le (low high : ℕ) : 1 ≤ apMassEndpointBase low high :=
  le_add_of_nonneg_right (Finset.sum_nonneg (fun _ _ => originalInterpolationConstant_nonnegative _ _ _))

theorem apMassEndpointBase_dominates (low high order : ℕ) (ordered : order ≤ high) :
    originalInterpolationConstant low order high ≤ apMassEndpointBase low high := by
  have selected := Finset.single_le_sum
    (f := fun index : Fin (high + 1) => originalInterpolationConstant low index.val high)
    (s := Finset.univ) (fun _ _ => originalInterpolationConstant_nonnegative _ _ _)
    (Finset.mem_univ (⟨order, Nat.lt_succ_of_le ordered⟩ : Fin (high + 1)))
  exact selected.trans (le_add_of_nonneg_left zero_le_one)

def apMassEndpointCoefficient (low high : ℕ) : ℝ :=
  apMassEndpointBase low high * max 1 (apLoweringConstant low)

def apMassEndpointConstant (low high : ℕ) : ℝ :=
  apLoweringConstant high * apMassEndpointCoefficient low high

theorem apMassEndpointCoefficient_one_le (low high : ℕ) : 1 ≤ apMassEndpointCoefficient low high :=
  (by norm_num : (1 : ℝ) ≤ 1 * 1).trans
    (mul_le_mul (apMassEndpointBase_one_le low high) (le_max_left _ _) zero_le_one
      (zero_le_one.trans (apMassEndpointBase_one_le low high)))

theorem apMassEndpointConstant_nonnegative (low high : ℕ) : 0 ≤ apMassEndpointConstant low high :=
  mul_nonneg (apLoweringConstant_nonnegative _) (zero_le_one.trans (apMassEndpointCoefficient_one_le _ _))

theorem apDerivative_norm_le_ordinary {dimension grade : ℕ} (field : ClosedJet dimension)
    (index : DerivativeIndex grade) :
    ‖closedDerivativeL2 (derivativeMultiIndex index) field‖ ≤ ‖apMassRow 1 (derivativeOrder index) field‖ := by
  let target := apDerivativeAtGrade index (derivativeOrder index) (le_refl _)
  have bound := PiLp.norm_apply_le (apMassRow 1 (derivativeOrder index) field) target
  change ‖(1 : ℂ) ^ (derivativeOrder index - derivativeOrder index) •
    closedDerivativeL2 (derivativeMultiIndex index) field‖ ≤ _ at bound
  simpa only [one_pow, one_smul] using bound

/-- A weighted derivative row is controlled by its lower weighted row and
its higher ordinary disk row. The intermediate derivatives are supplied by
accepted P17 and weighted arithmetic-geometric mean. -/
theorem apMassRow_endpoints {dimension low high : ℕ} (mass : ℝ) (oneLe : 1 ≤ mass)
    (ordered : low < high) (field : ClosedJet dimension) :
    ‖apMassRow mass high field‖ ≤ apMassEndpointConstant low high *
      (mass ^ (high - low) * ‖apMassRow mass low field‖ + ‖apMassRow 1 high field‖) := by
  let budget := mass ^ (high - low) * ‖apMassRow mass low field‖ + ‖apMassRow 1 high field‖
  have massPositive : 0 < mass := zero_lt_one.trans_le oneLe
  have powerNonnegative : 0 ≤ mass ^ (high - low) := pow_nonneg massPositive.le _
  have budgetNonnegative : 0 ≤ budget := add_nonneg (mul_nonneg powerNonnegative (norm_nonneg _)) (norm_nonneg _)
  have coefficientNonnegative : 0 ≤ apMassEndpointCoefficient low high := zero_le_one.trans (apMassEndpointCoefficient_one_le _ _)
  have ordinaryBound :
      mass ^ (high - low) * ‖apMassRow 1 low field‖ + ‖apMassRow 1 high field‖ ≤
        max 1 (apLoweringConstant low) * budget := by
    have lowBound := (apMassRow_ordinary_le mass oneLe field).trans
      (mul_le_mul_of_nonneg_right (le_max_right 1 (apLoweringConstant low)) (norm_nonneg _))
    have first := mul_le_mul_of_nonneg_left lowBound powerNonnegative
    have second := le_mul_of_one_le_left (norm_nonneg (apMassRow 1 high field)) (le_max_left 1 (apLoweringConstant low))
    calc
      _ ≤ mass ^ (high - low) * (max 1 (apLoweringConstant low) * ‖apMassRow mass low field‖) +
          max 1 (apLoweringConstant low) * ‖apMassRow 1 high field‖ := add_le_add first second
      _ = _ := by dsimp only [budget]; ring
  have coordinateBound (index : DerivativeIndex high) :
      ‖apMassRow mass high field index‖ ≤ apMassEndpointCoefficient low high * budget := by
    by_cases below : derivativeOrder index ≤ low
    · have bound := (apMassRow_coordinate_low mass oneLe ordered.le field index below).trans
        (le_add_of_nonneg_right (norm_nonneg (apMassRow 1 high field)))
      exact bound.trans (le_mul_of_one_le_left budgetNonnegative (apMassEndpointCoefficient_one_le _ _))
    · have above : low < derivativeOrder index := Nat.lt_of_not_ge below
      by_cases top : derivativeOrder index = high
      · rw [apMassRow_coordinate_norm mass massPositive.le, top, Nat.sub_self, pow_zero, one_mul]
        have bound := apDerivative_norm_le_ordinary field index
        rw [top] at bound
        exact (bound.trans (le_add_of_nonneg_left (mul_nonneg powerNonnegative (norm_nonneg _)))).trans
          (le_mul_of_one_le_left budgetNonnegative (apMassEndpointCoefficient_one_le _ _))
      · have interior : derivativeOrder index < high := lt_of_le_of_ne index.property top
        have derivativeBound := (apDerivative_norm_le_ordinary field index).trans
          (apOrdinaryRow_interpolation above interior field)
        rw [apMassRow_coordinate_norm mass massPositive.le]
        have multiplied := mul_le_mul_of_nonneg_left derivativeBound (pow_nonneg massPositive.le (high - derivativeOrder index))
        have mixed := apMassPower_mixed_le_endpoints mass ‖apMassRow 1 low field‖ ‖apMassRow 1 high field‖
          massPositive (norm_nonneg _) (norm_nonneg _) above interior
        calc
          _ ≤ mass ^ (high - derivativeOrder index) *
              (originalInterpolationConstant low (derivativeOrder index) high *
                (‖apMassRow 1 low field‖ ^ (1 - interpolationTheta low (derivativeOrder index) high) *
                  ‖apMassRow 1 high field‖ ^ interpolationTheta low (derivativeOrder index) high)) := multiplied
          _ = originalInterpolationConstant low (derivativeOrder index) high *
              (mass ^ (high - derivativeOrder index) *
                (‖apMassRow 1 low field‖ ^ (1 - interpolationTheta low (derivativeOrder index) high) *
                  ‖apMassRow 1 high field‖ ^ interpolationTheta low (derivativeOrder index) high)) := by ring
          _ ≤ originalInterpolationConstant low (derivativeOrder index) high *
              (mass ^ (high - low) * ‖apMassRow 1 low field‖ + ‖apMassRow 1 high field‖) :=
            mul_le_mul_of_nonneg_left mixed (originalInterpolationConstant_nonnegative _ _ _)
          _ ≤ apMassEndpointBase low high * (max 1 (apLoweringConstant low) * budget) :=
            mul_le_mul (apMassEndpointBase_dominates low high (derivativeOrder index) index.property)
              ordinaryBound (add_nonneg (mul_nonneg powerNonnegative (norm_nonneg _)) (norm_nonneg _))
              (zero_le_one.trans (apMassEndpointBase_one_le _ _))
          _ = _ := by unfold apMassEndpointCoefficient; ring
  have result := apRow_norm_bound_of_coordinates (apMassRow mass high field)
    (apMassEndpointCoefficient low high * budget) (mul_nonneg coefficientNonnegative budgetNonnegative) coordinateBound
  exact result.trans_eq (by unfold apMassEndpointConstant apLoweringConstant; dsimp only [budget]; ring)

end Grad.GaugeCoefficients.Physical.RadialLedger
