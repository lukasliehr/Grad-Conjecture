import GQF14CircularDomain

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

variable {L sigma gamma ell : ℝ}

def tangentialForwardConstant (grade : ℕ) : ℝ :=
  ‖planarPartMap‖ * (apComplementConstant grade * ‖planarInclusionMap‖)

def radialForwardConstant (grade : ℕ) : ℝ :=
  1 + ‖quarterValueMap‖ * (tangentialForwardConstant grade * ‖quarterValueMap‖)

theorem tangentialForwardConstant_nonnegative (grade : ℕ) : 0 ≤ tangentialForwardConstant grade :=
  mul_nonneg (norm_nonneg _) (mul_nonneg (apComplementConstant_nonnegative grade) (norm_nonneg _))

theorem radialForwardConstant_nonnegative (grade : ℕ) : 0 ≤ radialForwardConstant grade :=
  add_nonneg zero_le_one (mul_nonneg (norm_nonneg _)
    (mul_nonneg (tangentialForwardConstant_nonnegative grade) (norm_nonneg _)))

theorem apSmoothTangential_bound (field : APSmooth L sigma gamma ell 2) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 2 grade (apSmoothTangential L sigma gamma ell field)‖ ≤
      tangentialForwardConstant grade * ‖apSmoothGrade L sigma gamma ell 2 grade field‖ := by
  have inclusion := apSmoothValueMap_bound planarInclusionMap field grade
  have complement := apComplement_bound L sigma gamma ell grade
    (apSmoothGrade L sigma gamma ell 3 grade (apSmoothValueMap L sigma gamma ell planarInclusionMap field))
  have projection := apSmoothValueMap_bound planarPartMap
    (apSmoothComplement L sigma gamma ell (apSmoothValueMap L sigma gamma ell planarInclusionMap field)) grade
  exact projection.trans ((mul_le_mul_of_nonneg_left
    (complement.trans (mul_le_mul_of_nonneg_left inclusion (apComplementConstant_nonnegative grade)))
      (norm_nonneg planarPartMap)).trans_eq (by unfold tangentialForwardConstant; ring))

theorem apSmoothQrad_bound (field : APSmooth L sigma gamma ell 2) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 2 grade (apSmoothQrad L sigma gamma ell field)‖ ≤
      radialForwardConstant grade * ‖apSmoothGrade L sigma gamma ell 2 grade field‖ := by
  let J := apValueMap L sigma gamma ell grade quarterValueMap
  let P := apValueMap L sigma gamma ell grade planarPartMap
  let I := apValueMap L sigma gamma ell grade planarInclusionMap
  let C := apComplement L sigma gamma ell grade
  let x := field.val grade
  have inclusion := apValueMap_bound L sigma gamma ell grade planarInclusionMap (J x)
  have complement := apComplement_bound L sigma gamma ell grade (I (J x))
  have projection := apValueMap_bound L sigma gamma ell grade planarPartMap (C (I (J x)))
  have first := apValueMap_bound L sigma gamma ell grade quarterValueMap x
  have last := apValueMap_bound L sigma gamma ell grade quarterValueMap (P (C (I (J x))))
  have bound : ‖J (P (C (I (J x))))‖ ≤
      ‖quarterValueMap‖ * (‖planarPartMap‖ * (apComplementConstant grade *
        (‖planarInclusionMap‖ * (‖quarterValueMap‖ * ‖x‖)))) :=
    last.trans (mul_le_mul_of_nonneg_left
      (projection.trans (mul_le_mul_of_nonneg_left
        (complement.trans (mul_le_mul_of_nonneg_left
          (inclusion.trans (mul_le_mul_of_nonneg_left first (norm_nonneg _)))
            (apComplementConstant_nonnegative grade))) (norm_nonneg _))) (norm_nonneg _))
  have literal : apSmoothGrade L sigma gamma ell 2 grade (apSmoothQrad L sigma gamma ell field) =
      x + J (P (C (I (J x)))) := rfl
  rw [literal]
  exact (norm_add_le _ _).trans ((add_le_add le_rfl bound).trans_eq
    (by change _ = radialForwardConstant grade * ‖x‖
        unfold radialForwardConstant tangentialForwardConstant
        ring))

theorem apSmoothRemoveMean_bound {dimension : ℕ}
    (field : APSmooth L sigma gamma ell dimension) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell dimension grade (apSmoothRemoveMean L sigma gamma ell dimension field)‖ ≤
      (1 + orthogonalGradeConstant grade) * ‖apSmoothGrade L sigma gamma ell dimension grade field‖ :=
  apMeanFree_bound L sigma gamma ell dimension grade (field.val grade)

def divergenceForwardConstant (L gamma : ℝ) (grade : ℕ) : ℝ :=
  (‖matrixUnit (input := 3) (output := 1) 0 0‖ +
    ‖matrixUnit (input := 3) (output := 1) 0 1‖) * partialRowConstant L gamma grade +
      ‖toroidalPartMap‖ * apLoweringConstant grade

theorem divergenceForwardConstant_nonnegative (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    0 ≤ divergenceForwardConstant L gamma grade := by
  unfold divergenceForwardConstant
  exact add_nonneg (mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))
    (partialRowConstant_nonnegative admissible grade))
      (mul_nonneg (norm_nonneg _) (apLoweringConstant_nonnegative grade))

theorem apSmoothDiv_bound (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 1 grade (apSmoothDiv admissible field)‖ ≤
      divergenceForwardConstant L gamma grade * ‖apSmoothGrade L sigma gamma ell 3 (grade + 1) field‖ := by
  let first := apSmoothValueMap L sigma gamma ell (matrixUnit (input := 3) (output := 1) 0 0)
    (apSmoothPartial admissible 3 0 field)
  let second := apSmoothValueMap L sigma gamma ell (matrixUnit (input := 3) (output := 1) 0 1)
    (apSmoothPartial admissible 3 1 field)
  let third := apSmoothValueMap L sigma gamma ell toroidalPartMap (apSmoothAxial L sigma gamma ell 3 field)
  have firstBound := (apSmoothValueMap_bound (matrixUnit (input := 3) (output := 1) 0 0)
    (apSmoothPartial admissible 3 0 field) grade).trans
      (mul_le_mul_of_nonneg_left (apPartial_bound admissible 3 grade 0 (field.val (grade + 1))) (norm_nonneg _))
  have secondBound := (apSmoothValueMap_bound (matrixUnit (input := 3) (output := 1) 0 1)
    (apSmoothPartial admissible 3 1 field) grade).trans
      (mul_le_mul_of_nonneg_left (apPartial_bound admissible 3 grade 1 (field.val (grade + 1))) (norm_nonneg _))
  have thirdBound := (apSmoothValueMap_bound toroidalPartMap (apSmoothAxial L sigma gamma ell 3 field) grade).trans
    (mul_le_mul_of_nonneg_left (apAxial_bound L sigma gamma ell 3 grade (field.val (grade + 1))) (norm_nonneg _))
  change ‖apSmoothGrade L sigma gamma ell 1 grade ((first + second) + third)‖ ≤ _
  rw [map_add, map_add]
  exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
    ((add_le_add (add_le_add firstBound secondBound) thirdBound).trans_eq
      (by change _ = divergenceForwardConstant L gamma grade * ‖field.val (grade + 1)‖
          unfold divergenceForwardConstant
          ring)))

end Grad.GaugeCoefficients.Physical.Compensated
