import GQF22SourceNorm

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.BoundaryTrace

variable {L sigma gamma ell : ℝ}

def errorCoefficientSize (data : LedgerData L sigma gamma ell) (grade : ℕ) : ℝ :=
  ‖data.rotatedPlanarProduct grade‖ + ‖data.fluxDeviation grade‖ +
    ‖data.rotatedThirdProduct grade‖ + ‖data.traceDeviation grade‖

theorem errorCoefficientSize_nonnegative (data : LedgerData L sigma gamma ell) (grade : ℕ) :
    0 ≤ errorCoefficientSize data grade := by
  unfold errorCoefficientSize
  positivity

def errorForwardConstant (L sigma gamma : ℝ) (grade : ℕ) : ℝ :=
  (2 * radialForwardConstant (grade + 1) +
    (1 + orthogonalGradeConstant grade) * divergenceForwardConstant L gamma grade +
    2 * (1 + orthogonalGradeConstant (grade + 1)) + Real.sqrt (traceCellConstant (grade + 1))) *
      apMultiplierConstant L sigma gamma (grade + 1)

theorem errorForwardConstant_nonnegative (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    0 ≤ errorForwardConstant L sigma gamma grade := by
  have radial := radialForwardConstant_nonnegative (grade + 1)
  have divergence := divergenceForwardConstant_nonnegative admissible grade
  have mean := orthogonalGradeConstant_nonnegative grade
  have higherMean := orthogonalGradeConstant_nonnegative (grade + 1)
  have multiplier := apMultiplierConstant_nonnegative admissible (grade + 1)
  unfold errorForwardConstant
  positivity

theorem errorForce_bound (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (field : APSmooth L sigma gamma ell 3) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 2 grade (errorForce admissible data coherent field)‖ ≤
      2 * radialForwardConstant grade * apMultiplierConstant L sigma gamma grade *
        ‖data.rotatedPlanarProduct grade‖ * ‖field.val grade‖ := by
  have radial := apSmoothQrad_bound
    (apSmoothMultiplier admissible data.rotatedPlanarProduct coherent.2.2.2.2.2.2.2.1 field) grade
  have multiplier := apMultiplier_bound admissible (data.rotatedPlanarProduct grade) (field.val grade)
  change ‖apSmoothGrade L sigma gamma ell 2 grade ((2 : ℂ) •
    apSmoothQrad L sigma gamma ell
      (apSmoothMultiplier admissible data.rotatedPlanarProduct coherent.2.2.2.2.2.2.2.1 field))‖ ≤ _
  rw [map_smul, norm_smul]
  norm_num only [Complex.norm_ofNat]
  exact (mul_le_mul_of_nonneg_left (radial.trans
    (mul_le_mul_of_nonneg_left multiplier (radialForwardConstant_nonnegative grade))) (by norm_num)).trans_eq (by ring)

theorem errorDeterminant_bound (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (field : APSmooth L sigma gamma ell 3) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 1 grade (errorDeterminant admissible data coherent field)‖ ≤
      (1 + orthogonalGradeConstant grade) * divergenceForwardConstant L gamma grade *
        apMultiplierConstant L sigma gamma (grade + 1) * ‖data.fluxDeviation (grade + 1)‖ *
          ‖field.val (grade + 1)‖ := by
  have mean := apSmoothRemoveMean_bound
    (apSmoothDiv admissible (apSmoothMultiplier admissible data.fluxDeviation coherent.2.2.2.2.1 field)) grade
  have divergence := apSmoothDiv_bound admissible
    (apSmoothMultiplier admissible data.fluxDeviation coherent.2.2.2.2.1 field) grade
  have multiplier := apMultiplier_bound admissible (data.fluxDeviation (grade + 1)) (field.val (grade + 1))
  exact mean.trans ((mul_le_mul_of_nonneg_left (divergence.trans
    (mul_le_mul_of_nonneg_left multiplier (divergenceForwardConstant_nonnegative admissible grade)))
      (add_nonneg zero_le_one (orthogonalGradeConstant_nonnegative grade))).trans_eq (by ring))

theorem errorThird_bound (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (field : APSmooth L sigma gamma ell 3) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 1 grade (errorThird admissible data coherent field)‖ ≤
      2 * (1 + orthogonalGradeConstant grade) * apMultiplierConstant L sigma gamma grade *
        ‖data.rotatedThirdProduct grade‖ * ‖field.val grade‖ := by
  have mean := apSmoothRemoveMean_bound
    (apSmoothMultiplier admissible data.rotatedThirdProduct coherent.2.2.2.2.2.2.2.2 field) grade
  have multiplier := apMultiplier_bound admissible (data.rotatedThirdProduct grade) (field.val grade)
  change ‖apSmoothGrade L sigma gamma ell 1 grade ((-2 : ℂ) •
    apSmoothRemoveMean L sigma gamma ell 1
      (apSmoothMultiplier admissible data.rotatedThirdProduct coherent.2.2.2.2.2.2.2.2 field))‖ ≤ _
  rw [map_smul, norm_smul]
  norm_num only [norm_neg, Complex.norm_ofNat]
  exact (mul_le_mul_of_nonneg_left (mean.trans
    (mul_le_mul_of_nonneg_left multiplier (add_nonneg zero_le_one
      (orthogonalGradeConstant_nonnegative grade)))) (by norm_num)).trans_eq (by ring)

theorem errorCoreTrace_bound (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (field : APSmooth L sigma gamma ell 3) (grade : ℕ) :
    ‖errorCoreTrace admissible data grade field‖ ≤
      Real.sqrt (traceCellConstant (grade + 1)) * apMultiplierConstant L sigma gamma (grade + 1) *
        ‖data.traceDeviation (grade + 1)‖ * ‖field.val (grade + 1)‖ := by
  have trace := apHighTrace_bound L sigma gamma ell (grade + 1) (by omega)
    (apMultiplier admissible (data.traceDeviation (grade + 1)) (field.val (grade + 1)))
  exact trace.trans ((mul_le_mul_of_nonneg_left
    (apMultiplier_bound admissible (data.traceDeviation (grade + 1)) (field.val (grade + 1)))
      (Real.sqrt_nonneg _)).trans_eq (by ring))

theorem errorAugmentedCore_bound (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (field : APSmooth L sigma gamma ell 3) (grade : ℕ) :
    ‖errorAugmentedCore admissible data coherent grade field‖ ≤
      errorForwardConstant L sigma gamma grade * errorCoefficientSize data (grade + 1) *
        ‖field.val (grade + 1)‖ := by
  have pair := hilbertPairLinear_norm_le
    ((capSourceGrade grade).comp (errorRows admissible data coherent)) (errorCoreTrace admissible data grade) field
  have bulk := capSourceGrade_norm_le grade (errorRows admissible data coherent field)
  have component := add_le_add (add_le_add (add_le_add
    (errorForce_bound admissible data coherent field (grade + 1))
    (errorDeterminant_bound admissible data coherent field grade))
    (errorThird_bound admissible data coherent field (grade + 1)))
    (errorCoreTrace_bound admissible data field grade)
  refine pair.trans ((add_le_add bulk le_rfl).trans (component.trans ?_))
  have first : ‖data.rotatedPlanarProduct (grade + 1)‖ ≤ errorCoefficientSize data (grade + 1) := by
    unfold errorCoefficientSize
    linarith [norm_nonneg (data.fluxDeviation (grade + 1)), norm_nonneg (data.rotatedThirdProduct (grade + 1)),
      norm_nonneg (data.traceDeviation (grade + 1))]
  have second : ‖data.fluxDeviation (grade + 1)‖ ≤ errorCoefficientSize data (grade + 1) := by
    unfold errorCoefficientSize
    linarith [norm_nonneg (data.rotatedPlanarProduct (grade + 1)), norm_nonneg (data.rotatedThirdProduct (grade + 1)),
      norm_nonneg (data.traceDeviation (grade + 1))]
  have third : ‖data.rotatedThirdProduct (grade + 1)‖ ≤ errorCoefficientSize data (grade + 1) := by
    unfold errorCoefficientSize
    linarith [norm_nonneg (data.rotatedPlanarProduct (grade + 1)), norm_nonneg (data.fluxDeviation (grade + 1)),
      norm_nonneg (data.traceDeviation (grade + 1))]
  have fourth : ‖data.traceDeviation (grade + 1)‖ ≤ errorCoefficientSize data (grade + 1) := by
    unfold errorCoefficientSize
    linarith [norm_nonneg (data.rotatedPlanarProduct (grade + 1)), norm_nonneg (data.fluxDeviation (grade + 1)),
      norm_nonneg (data.rotatedThirdProduct (grade + 1))]
  have radial := radialForwardConstant_nonnegative (grade + 1)
  have divergence := divergenceForwardConstant_nonnegative admissible grade
  have mean := orthogonalGradeConstant_nonnegative grade
  have higherMean := orthogonalGradeConstant_nonnegative (grade + 1)
  have multiplier := apMultiplierConstant_nonnegative admissible (grade + 1)
  calc
    _ ≤ 2 * radialForwardConstant (grade + 1) * apMultiplierConstant L sigma gamma (grade + 1) *
          errorCoefficientSize data (grade + 1) * ‖field.val (grade + 1)‖ +
        (1 + orthogonalGradeConstant grade) * divergenceForwardConstant L gamma grade *
          apMultiplierConstant L sigma gamma (grade + 1) * errorCoefficientSize data (grade + 1) * ‖field.val (grade + 1)‖ +
        2 * (1 + orthogonalGradeConstant (grade + 1)) * apMultiplierConstant L sigma gamma (grade + 1) *
          errorCoefficientSize data (grade + 1) * ‖field.val (grade + 1)‖ +
        Real.sqrt (traceCellConstant (grade + 1)) * apMultiplierConstant L sigma gamma (grade + 1) *
          errorCoefficientSize data (grade + 1) * ‖field.val (grade + 1)‖ := by gcongr
    _ = _ := by unfold errorForwardConstant; ring

end Grad.GaugeCoefficients.Physical.Compensated
