import GQF25CompletedError

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryTrace

variable {L sigma gamma ell : ℝ}

theorem norm_negative_two_sub_add {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (first second third : E) :
    ‖(-2 : ℂ) • first - (second + third)‖ ≤ 2 * ‖first‖ + ‖second‖ + ‖third‖ := by
  have bound := (norm_sub_le ((-2 : ℂ) • first) (second + third)).trans
    (add_le_add le_rfl (norm_add_le second third))
  rw [norm_smul] at bound
  norm_num only [norm_neg, Complex.norm_ofNat] at bound
  exact bound.trans_eq (add_assoc _ _ _).symm

def circularInnerConstant (L gamma : ℝ) (grade : ℕ) : ℝ :=
  2 * ‖quarterValueMap‖ * gradientBoundConstant L gamma (grade + 1) + 1 + ‖quarterValueMap‖

theorem circularInnerConstant_nonnegative (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    0 ≤ circularInnerConstant L gamma grade := by
  have gradient := gradientBoundConstant_nonnegative admissible (grade + 1)
  unfold circularInnerConstant
  positivity

def circularForwardConstant (L sigma gamma : ℝ) (grade : ℕ) : ℝ :=
  radialForwardConstant (grade + 1) * circularInnerConstant L gamma grade +
    (1 + orthogonalGradeConstant grade) * divergenceForwardConstant L gamma grade *
      reconstructionBoundConstant L gamma grade + 1 +
    Real.sqrt (traceCellConstant (grade + 1)) *
      fixedRowBoundConstant L sigma gamma (grade + 1) radialRowJet * reconstructionBoundConstant L gamma grade

theorem circularForwardConstant_nonnegative (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    0 ≤ circularForwardConstant L sigma gamma grade := by
  have radial := radialForwardConstant_nonnegative (grade + 1)
  have inner := circularInnerConstant_nonnegative admissible grade
  have mean := orthogonalGradeConstant_nonnegative grade
  have divergence := divergenceForwardConstant_nonnegative admissible grade
  have reconstruct := reconstructionBoundConstant_nonnegative admissible grade
  have row := fixedRowBoundConstant_nonnegative admissible (grade + 1) radialRowJet
  unfold circularForwardConstant
  positivity

theorem circularForceInner_bound (admissible : Admissible L sigma gamma ell)
    (data : CompensatedData L sigma gamma ell) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) (circularForceInner admissible data)‖ ≤
      circularInnerConstant L gamma grade * compensatedNorm admissible grade data := by
  have theta := compensatedGraphEntry_bound admissible grade data 0
  have remainder := compensatedGraphEntry_bound admissible grade data 1
  have rotation := compensatedGraphEntry_bound admissible grade data 2
  have first := (apSmoothValueMap_bound quarterValueMap (apSmoothGradient admissible data.1) (grade + 1)).trans
    (mul_le_mul_of_nonneg_left ((apSmoothGradient_bound admissible data.1 (grade + 1)).trans
      (mul_le_mul_of_nonneg_left theta (gradientBoundConstant_nonnegative admissible (grade + 1)))) (norm_nonneg _))
  have second := (apSmoothValueMap_bound quarterValueMap (apSmoothPlanar L sigma gamma ell data.2) (grade + 1)).trans
    (mul_le_mul_of_nonneg_left remainder (norm_nonneg _))
  let firstValue := (apSmoothQuarter L sigma gamma ell (apSmoothGradient admissible data.1)).val (grade + 1)
  let secondValue := (apSmoothRotation admissible 2 (apSmoothPlanar L sigma gamma ell data.2)).val (grade + 1)
  let thirdValue := (apSmoothQuarter L sigma gamma ell (apSmoothPlanar L sigma gamma ell data.2)).val (grade + 1)
  have literal : apSmoothGrade L sigma gamma ell 2 (grade + 1) (circularForceInner admissible data) =
      (-2 : ℂ) • firstValue - (secondValue + thirdValue) := rfl
  exact (congrArg norm literal).le.trans ((norm_negative_two_sub_add firstValue secondValue thirdValue).trans
    ((add_le_add (add_le_add (mul_le_mul_of_nonneg_left first (by norm_num)) rotation) second).trans_eq
      (by unfold circularInnerConstant; ring)))

theorem circularDeterminant_bound (admissible : Admissible L sigma gamma ell)
    (data : CompensatedData L sigma gamma ell) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 1 grade (circularDeterminant admissible data)‖ ≤
      (1 + orthogonalGradeConstant grade) * divergenceForwardConstant L gamma grade *
        reconstructionBoundConstant L gamma grade * compensatedNorm admissible grade data := by
  have mean := apSmoothRemoveMean_bound (apSmoothDiv admissible (compensatedReconstruct admissible data)) grade
  have divergence := apSmoothDiv_bound admissible (compensatedReconstruct admissible data) grade
  change ‖apSmoothGrade L sigma gamma ell 1 grade
    (-(apSmoothRemoveMean L sigma gamma ell 1 (apSmoothDiv admissible (compensatedReconstruct admissible data))))‖ ≤ _
  rw [map_neg, norm_neg]
  exact mean.trans ((mul_le_mul_of_nonneg_left (divergence.trans
    (mul_le_mul_of_nonneg_left (compensatedReconstruct_bound admissible grade data)
      (divergenceForwardConstant_nonnegative admissible grade)))
    (add_nonneg zero_le_one (orthogonalGradeConstant_nonnegative grade))).trans_eq (by ring))

theorem circularCoreTrace_bound (admissible : Admissible L sigma gamma ell)
    (data : CompensatedData L sigma gamma ell) (grade : ℕ) :
    ‖circularCoreTrace admissible grade data‖ ≤
      Real.sqrt (traceCellConstant (grade + 1)) * fixedRowBoundConstant L sigma gamma (grade + 1) radialRowJet *
        reconstructionBoundConstant L gamma grade * compensatedNorm admissible grade data := by
  have trace := apHighTrace_bound L sigma gamma ell (grade + 1) (by omega)
    (apSmoothGrade L sigma gamma ell 1 (grade + 1) (apSmoothRadial admissible (compensatedReconstruct admissible data)))
  have radial := apFixedRow_bound admissible (grade + 1) radialRowJet
    (apSmoothGrade L sigma gamma ell 3 (grade + 1) (compensatedReconstruct admissible data))
  exact trace.trans ((mul_le_mul_of_nonneg_left (radial.trans
    (mul_le_mul_of_nonneg_left (compensatedReconstruct_bound admissible grade data)
      (fixedRowBoundConstant_nonnegative admissible (grade + 1) radialRowJet)))
    (Real.sqrt_nonneg _)).trans_eq (by ring))

theorem circularAugmentedCore_bound (admissible : Admissible L sigma gamma ell)
    (data : CompensatedData L sigma gamma ell) (grade : ℕ) :
    ‖circularAugmentedCore admissible grade data‖ ≤
      circularForwardConstant L sigma gamma grade * compensatedNorm admissible grade data := by
  have pair := hilbertPairLinear_norm_le ((capSourceGrade grade).comp (circularRows admissible))
    (circularCoreTrace admissible grade) data
  have bulk := capSourceGrade_norm_le grade (circularRows admissible data)
  have force := (apSmoothQrad_bound (circularForceInner admissible data) (grade + 1)).trans
    (mul_le_mul_of_nonneg_left (circularForceInner_bound admissible data grade)
      (radialForwardConstant_nonnegative (grade + 1)))
  have determinant := circularDeterminant_bound admissible data grade
  have third := compensatedGraphEntry_bound admissible grade data 4
  have trace := circularCoreTrace_bound admissible data grade
  exact pair.trans ((add_le_add bulk le_rfl).trans ((add_le_add
    (add_le_add (add_le_add force determinant) third) trace).trans_eq
      (by unfold circularForwardConstant; ring)))

end Grad.GaugeCoefficients.Physical.Compensated
