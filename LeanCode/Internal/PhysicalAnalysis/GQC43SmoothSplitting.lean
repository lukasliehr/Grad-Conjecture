import GQC42CompensatedTransfer

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem apSmoothValueMap_value {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (field : APSmooth L sigma gamma ell input) (cell : ℤ) (point : ClosedDisk) :
    (apSmoothJet admissible output cell (apSmoothValueMap L sigma gamma ell mapping field)).value point =
      mapping ((apSmoothJet admissible input cell field).value point) :=
  (congrArg (fun jet : ClosedJet output => jet.value point)
    (apSmoothValueMap_jet admissible mapping field cell)).trans (valueMapJet_value mapping _ point)

theorem apSmoothValueMap_bound {L sigma gamma ell : ℝ} {input output : ℕ}
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (field : APSmooth L sigma gamma ell input) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell output grade (apSmoothValueMap L sigma gamma ell mapping field)‖ ≤
      ‖mapping‖ * ‖apSmoothGrade L sigma gamma ell input grade field‖ :=
  apValueMap_bound L sigma gamma ell grade mapping (field.val grade)

theorem apSmooth_splitting {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) :
    apSmoothValueMap L sigma gamma ell planarInclusionMap (apSmoothValueMap L sigma gamma ell planarPartMap field) +
      apSmoothValueMap L sigma gamma ell toroidalInclusionMap (apSmoothValueMap L sigma gamma ell toroidalPartMap field) = field := by
  apply apSmoothJet_ext admissible
  intro cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [map_add, closedJet_value_add, ContinuousMap.add_apply]
  have first := (apSmoothValueMap_value admissible planarInclusionMap
    (apSmoothValueMap L sigma gamma ell planarPartMap field) cell point).trans
      (congrArg planarInclusionMap (apSmoothValueMap_value admissible planarPartMap field cell point))
  have second := (apSmoothValueMap_value admissible toroidalInclusionMap
    (apSmoothValueMap L sigma gamma ell toroidalPartMap field) cell point).trans
      (congrArg toroidalInclusionMap (apSmoothValueMap_value admissible toroidalPartMap field cell point))
  exact (congrArg₂ (fun left right : ComplexEuclidean 3 => left + right) first second).trans
    (congrArg (fun mapping : ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 3 =>
      mapping ((apSmoothJet admissible 3 cell field).value point)) splitting_reconstruction)

theorem apSmooth_splitting_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 3 grade field‖ ≤
      ‖planarInclusionMap‖ * ‖apSmoothGrade L sigma gamma ell 2 grade (apSmoothValueMap L sigma gamma ell planarPartMap field)‖ +
        ‖toroidalInclusionMap‖ * ‖apSmoothGrade L sigma gamma ell 1 grade (apSmoothValueMap L sigma gamma ell toroidalPartMap field)‖ := by
  have equality := congrArg (apSmoothGrade L sigma gamma ell 3 grade) (apSmooth_splitting admissible field)
  rw [map_add] at equality
  exact equality ▸ (norm_add_le _ _).trans
    (add_le_add (apSmoothValueMap_bound planarInclusionMap _ grade) (apSmoothValueMap_bound toroidalInclusionMap _ grade))

end Grad.GaugeCoefficients.Physical.Compensated
