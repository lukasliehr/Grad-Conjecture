import GQC32SmoothComplement
import GQC33CovariantJet

noncomputable section

set_option maxHeartbeats 1600000

open Set
open scoped Topology

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

def apSmoothGradient {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) :
    APSmooth L sigma gamma ell 1 →ₗ[ℂ] APSmooth L sigma gamma ell 2 :=
  (apSmoothValueMap L sigma gamma ell (matrixUnit (input := 1) (output := 2) 0 0)).comp (apSmoothPartial admissible 1 0) +
    (apSmoothValueMap L sigma gamma ell (matrixUnit (input := 1) (output := 2) 1 0)).comp (apSmoothPartial admissible 1 1)

def apSmoothCovariant {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) :
    APSmooth L sigma gamma ell 1 →ₗ[ℂ] APSmooth L sigma gamma ell 3 :=
  (apSmoothValueMap L sigma gamma ell planarInclusionMap).comp (apSmoothGradient admissible) +
    (apSmoothValueMap L sigma gamma ell toroidalInclusionMap).comp (apSmoothAxial L sigma gamma ell 1)

theorem apSmoothGradient_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 1) (cell : ℤ) :
    apSmoothJet admissible 2 cell (apSmoothGradient admissible field) =
      gradientJet (apSmoothJet admissible 1 cell field) := by
  simp only [apSmoothGradient, LinearMap.add_apply, LinearMap.comp_apply]
  exact (map_add (apSmoothJet admissible 2 cell) _ _).trans
    (congrArg₂ (fun first second : ClosedJet 2 => first + second)
      ((apSmoothValueMap_jet admissible (matrixUnit (input := 1) (output := 2) 0 0) (apSmoothPartial admissible 1 0 field) cell).trans
        (congrArg (valueMapJet (matrixUnit (input := 1) (output := 2) 0 0)) (apSmoothPartial_jet admissible field 0 cell)))
      ((apSmoothValueMap_jet admissible (matrixUnit (input := 1) (output := 2) 1 0) (apSmoothPartial admissible 1 1 field) cell).trans
        (congrArg (valueMapJet (matrixUnit (input := 1) (output := 2) 1 0)) (apSmoothPartial_jet admissible field 1 cell))))

theorem apSmoothCovariant_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 1) (cell : ℤ) :
    apSmoothJet admissible 3 cell (apSmoothCovariant admissible field) =
      covariantJet (Grad.GaugeCoefficients.Physical.Frame.seedScaledFrequency L ell cell)
        (apSmoothJet admissible 1 cell field) := by
  simp only [apSmoothCovariant, LinearMap.add_apply, LinearMap.comp_apply, map_add]
  have first := (apSmoothValueMap_jet (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
    admissible (input := 2) (output := 3) planarInclusionMap (apSmoothGradient admissible field) cell).trans
    (congrArg (valueMapJet planarInclusionMap) (apSmoothGradient_jet admissible field cell))
  have second := (apSmoothValueMap_jet (L := L) (sigma := sigma) (gamma := gamma) (ell := ell)
    admissible (input := 1) (output := 3) toroidalInclusionMap (apSmoothAxial L sigma gamma ell 1 field) cell).trans
    (congrArg (valueMapJet toroidalInclusionMap) (apSmoothAxial_jet admissible field cell))
  exact congrArg₂ (fun left right : ClosedJet 3 => left + right) first
    (second.trans (valueMapJet_smul_field toroidalInclusionMap
      (Grad.GaugeCoefficients.Physical.Frame.seedScaledFrequency L ell cell)
      (apSmoothJet admissible 1 cell field)))

def gradientBoundConstant (L gamma : ℝ) (grade : ℕ) : ℝ :=
  (‖matrixUnit (input := 1) (output := 2) 0 0‖ + ‖matrixUnit (input := 1) (output := 2) 1 0‖) *
    partialRowConstant L gamma grade

theorem gradientBoundConstant_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    0 ≤ gradientBoundConstant L gamma grade :=
  mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (partialRowConstant_nonnegative admissible grade)

theorem apSmoothGradient_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 1) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 2 grade (apSmoothGradient admissible field)‖ ≤
      gradientBoundConstant L gamma grade * ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) field‖ := by
  change ‖apValueMap L sigma gamma ell grade (matrixUnit 0 0) (apPartial admissible 1 grade 0 (field.val (grade + 1))) +
    apValueMap L sigma gamma ell grade (matrixUnit 1 0) (apPartial admissible 1 grade 1 (field.val (grade + 1)))‖ ≤ _
  calc
    _ ≤ ‖matrixUnit (input := 1) (output := 2) 0 0‖ *
          (partialRowConstant L gamma grade * ‖field.val (grade + 1)‖) +
        ‖matrixUnit (input := 1) (output := 2) 1 0‖ *
          (partialRowConstant L gamma grade * ‖field.val (grade + 1)‖) := by
      apply (norm_add_le _ _).trans
      apply add_le_add
      · exact (apValueMap_bound L sigma gamma ell grade _ _).trans
          (mul_le_mul_of_nonneg_left (apPartial_bound admissible 1 grade 0 _) (norm_nonneg _))
      · exact (apValueMap_bound L sigma gamma ell grade _ _).trans
          (mul_le_mul_of_nonneg_left (apPartial_bound admissible 1 grade 1 _) (norm_nonneg _))
    _ = _ := by dsimp [gradientBoundConstant, apSmoothGrade]; ring

def covariantBoundConstant (L gamma : ℝ) (grade : ℕ) : ℝ :=
  ‖planarInclusionMap‖ * gradientBoundConstant L gamma grade +
    ‖toroidalInclusionMap‖ * apLoweringConstant grade

theorem apSmoothCovariant_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 1) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 3 grade (apSmoothCovariant admissible field)‖ ≤
      covariantBoundConstant L gamma grade * ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) field‖ := by
  change ‖apValueMap L sigma gamma ell grade planarInclusionMap ((apSmoothGradient admissible field).val grade) +
    apValueMap L sigma gamma ell grade toroidalInclusionMap (apAxial L sigma gamma ell 1 grade (field.val (grade + 1)))‖ ≤ _
  calc
    _ ≤ ‖planarInclusionMap‖ *
          (gradientBoundConstant L gamma grade * ‖field.val (grade + 1)‖) +
        ‖toroidalInclusionMap‖ * (apLoweringConstant grade * ‖field.val (grade + 1)‖) := by
      apply (norm_add_le _ _).trans
      apply add_le_add
      · exact (apValueMap_bound L sigma gamma ell grade _ _).trans
          (mul_le_mul_of_nonneg_left (apSmoothGradient_bound admissible field grade) (norm_nonneg _))
      · exact (apValueMap_bound L sigma gamma ell grade _ _).trans
          (mul_le_mul_of_nonneg_left (apAxial_bound L sigma gamma ell 1 grade _) (norm_nonneg _))
    _ = _ := by dsimp [covariantBoundConstant, apSmoothGrade]; ring

end Grad.GaugeCoefficients.Physical.Compensated
