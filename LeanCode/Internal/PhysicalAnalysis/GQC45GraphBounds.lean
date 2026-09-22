import GQC44CompensatedNorm

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem compensatedNorm_eq_zero_iff {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (data : CompensatedData L sigma gamma ell) :
    compensatedNorm admissible grade data = 0 ↔ data = 0 := by
  constructor
  · intro zero
    have graphZero := norm_eq_zero.mp zero
    have entryZero (index : Fin 5) : compensatedGraphEntry admissible grade index data = 0 :=
      congrArg (fun graph : CompensatedGraphAmbient L sigma gamma ell grade => graph index) graphZero
    have thetaZero : data.1 = 0 := by
      apply apSmoothGrade_injective admissible 1 (grade + 2)
      exact entryZero 0
    have planarZero : apSmoothValueMap L sigma gamma ell planarPartMap data.2 = 0 := by
      apply apSmoothGrade_injective admissible 2 (grade + 1)
      exact entryZero 1
    have scalarZero : apSmoothValueMap L sigma gamma ell toroidalPartMap data.2 = 0 := by
      apply apSmoothGrade_injective admissible 1 (grade + 1)
      exact entryZero 3
    apply Prod.ext thetaZero
    have reconstruction := (apSmooth_splitting admissible data.2).symm
    exact reconstruction.trans ((congrArg₂ (fun first second : APSmooth L sigma gamma ell 3 => first + second)
      ((congrArg (apSmoothValueMap L sigma gamma ell planarInclusionMap) planarZero).trans (map_zero _))
      ((congrArg (apSmoothValueMap L sigma gamma ell toroidalInclusionMap) scalarZero).trans (map_zero _))).trans (zero_add _))
  · rintro rfl
    simp only [compensatedNorm, map_zero, norm_zero]

theorem compensatedGraph_bound_of_entries {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (data : CompensatedData L sigma gamma ell) (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ index, ‖compensatedGraphEntry admissible grade index data‖ ≤ bound) :
    compensatedNorm admissible grade data ≤ Real.sqrt 5 * bound := by
  have square : compensatedNorm admissible grade data ^ 2 ≤ 5 * bound ^ 2 := by
    rw [compensatedNorm, PiLp.norm_sq_eq_of_L2]
    calc
      _ ≤ ∑ _index : Fin 5, bound ^ 2 := Finset.sum_le_sum (fun index _ =>
        pow_le_pow_left₀ (norm_nonneg _) (bounded index) 2)
      _ = _ := by simp
  have rootSquare := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 5)
  have rootNonnegative := Real.sqrt_nonneg (5 : ℝ)
  have valueNonnegative := compensatedNorm_nonnegative admissible grade data
  nlinarith [mul_nonneg rootNonnegative nonnegative,
    sq_nonneg (compensatedNorm admissible grade data - Real.sqrt 5 * bound)]

def remainderBoundConstant : ℝ := ‖planarInclusionMap‖ + ‖toroidalInclusionMap‖

theorem remainderBoundConstant_nonnegative : 0 ≤ remainderBoundConstant := add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem compensatedRemainder_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (data : CompensatedData L sigma gamma ell) :
    ‖apSmoothGrade L sigma gamma ell 3 (grade + 1) data.2‖ ≤
      remainderBoundConstant * compensatedNorm admissible grade data := by
  have first := compensatedGraphEntry_bound admissible grade data 1
  have second := compensatedGraphEntry_bound admissible grade data 3
  exact (apSmooth_splitting_bound admissible data.2 (grade + 1)).trans
    ((add_le_add (mul_le_mul_of_nonneg_left first (norm_nonneg _))
      (mul_le_mul_of_nonneg_left second (norm_nonneg _))).trans_eq (add_mul _ _ _).symm)

theorem covariantBoundConstant_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) : 0 ≤ covariantBoundConstant L gamma grade :=
  add_nonneg (mul_nonneg (norm_nonneg _) (gradientBoundConstant_nonnegative admissible grade))
    (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))

def reconstructionBoundConstant (L gamma : ℝ) (grade : ℕ) : ℝ :=
  covariantBoundConstant L gamma (grade + 1) + remainderBoundConstant

theorem reconstructionBoundConstant_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) : 0 ≤ reconstructionBoundConstant L gamma grade :=
  add_nonneg (covariantBoundConstant_nonnegative admissible (grade + 1)) remainderBoundConstant_nonnegative

theorem compensatedReconstruct_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (data : CompensatedData L sigma gamma ell) :
    ‖apSmoothGrade L sigma gamma ell 3 (grade + 1) (compensatedReconstruct admissible data)‖ ≤
      reconstructionBoundConstant L gamma grade * compensatedNorm admissible grade data := by
  change ‖apSmoothGrade L sigma gamma ell 3 (grade + 1) (apSmoothCovariant admissible data.1 + data.2)‖ ≤ _
  rw [map_add]
  exact (norm_add_le _ _).trans ((add_le_add
    ((apSmoothCovariant_bound admissible data.1 (grade + 1)).trans
      (mul_le_mul_of_nonneg_left (compensatedGraphEntry_bound admissible grade data 0)
        (covariantBoundConstant_nonnegative admissible (grade + 1))))
    (compensatedRemainder_bound admissible grade data)).trans_eq (add_mul _ _ _).symm)

end Grad.GaugeCoefficients.Physical.Compensated
