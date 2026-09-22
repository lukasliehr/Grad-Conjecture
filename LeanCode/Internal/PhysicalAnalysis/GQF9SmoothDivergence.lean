import GQF8CompletedDivergence

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.Frame

variable {L sigma gamma ell : ℝ}

theorem apSmoothRemoveMean_jet (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension) (cell : ℤ) :
    apSmoothJet admissible dimension cell (apSmoothRemoveMean L sigma gamma ell dimension field) =
      apSmoothJet admissible dimension cell field - angularClosedJet 0 (apSmoothJet admissible dimension cell field) := by
  exact (map_sub (apSmoothJet admissible dimension cell) field
    (apSmoothAngularMean L sigma gamma ell dimension field)).trans
      (congrArg (fun jet : ClosedJet dimension => apSmoothJet admissible dimension cell field - jet)
        (apSmoothAngularMean_jet admissible field cell))

theorem apSmoothDiv_jet (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) (cell : ℤ) :
    apSmoothJet admissible 1 cell (apSmoothDiv admissible field) =
      planarDivJet (apSmoothJet admissible 3 cell field) +
        seedScaledFrequency L ell cell • valueMapJet toroidalPartMap (apSmoothJet admissible 3 cell field) := by
  let first := apSmoothValueMap L sigma gamma ell (matrixUnit (input := 3) (output := 1) 0 0)
    (apSmoothPartial admissible 3 0 field)
  let second := apSmoothValueMap L sigma gamma ell (matrixUnit (input := 3) (output := 1) 0 1)
    (apSmoothPartial admissible 3 1 field)
  let third := apSmoothValueMap L sigma gamma ell toroidalPartMap (apSmoothAxial L sigma gamma ell 3 field)
  have firstLaw := (apSmoothValueMap_jet admissible (matrixUnit (input := 3) (output := 1) 0 0)
    (apSmoothPartial admissible 3 0 field) cell).trans
    (congrArg (valueMapJet (matrixUnit (input := 3) (output := 1) 0 0))
      (apSmoothPartial_jet admissible field 0 cell))
  have secondLaw := (apSmoothValueMap_jet admissible (matrixUnit (input := 3) (output := 1) 0 1)
    (apSmoothPartial admissible 3 1 field) cell).trans
    (congrArg (valueMapJet (matrixUnit (input := 3) (output := 1) 0 1))
      (apSmoothPartial_jet admissible field 1 cell))
  have thirdLaw := (apSmoothValueMap_jet admissible toroidalPartMap
    (apSmoothAxial L sigma gamma ell 3 field) cell).trans
    ((congrArg (valueMapJet toroidalPartMap) (apSmoothAxial_jet admissible field cell)).trans
      ((valueMapJetLinear 3 1 toroidalPartMap).map_smul (seedScaledFrequency L ell cell) _))
  change apSmoothJet admissible 1 cell ((first + second) + third) = _
  exact (map_add (apSmoothJet admissible 1 cell) (first + second) third).trans
    (congrArg₂ (fun a b : ClosedJet 1 => a + b)
      ((map_add (apSmoothJet admissible 1 cell) first second).trans
        (congrArg₂ (fun a b : ClosedJet 1 => a + b) firstLaw secondLaw)) thirdLaw)

theorem apSmoothDiv_complement_jet (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) (cell : ℤ) :
    apSmoothJet admissible 1 cell (apSmoothDiv admissible (apSmoothComplement L sigma gamma ell field)) =
      seedScaledFrequency L ell cell • angularClosedJet 0
        (valueMapJet toroidalPartMap (apSmoothJet admissible 3 cell field)) := by
  have image := apSmoothComplement_jet admissible field cell
  have first := congrArg planarDivJet image
  have second := congrArg (valueMapJet toroidalPartMap) image
  have zero := first.trans (planarDivJet_complement_zero _)
  have scalar := second.trans (scalarComplement_jet _)
  exact (apSmoothDiv_jet admissible (apSmoothComplement L sigma gamma ell field) cell).trans
    ((congrArg₂ (fun a b : ClosedJet 1 => a + seedScaledFrequency L ell cell • b) zero scalar).trans
      (zero_add _))

theorem apSmoothRemoveMean_div_complement (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) :
    apSmoothRemoveMean L sigma gamma ell 1 (apSmoothDiv admissible (apSmoothComplement L sigma gamma ell field)) = 0 := by
  apply apSmoothJet_ext admissible
  intro cell
  have law := apSmoothDiv_complement_jet admissible field cell
  have difference := congrArg (fun jet : ClosedJet 1 => jet - angularClosedJet 0 jet) law
  have cancellation (jet : ClosedJet 1) (scalar : ℂ) :
      scalar • angularClosedJet 0 jet - angularClosedJet 0 (scalar • angularClosedJet 0 jet) = 0 := by
    rw [angularClosedJet_smul, angularClosedJet_projection]
    simp
  exact (apSmoothRemoveMean_jet admissible _ cell).trans
    (difference.trans ((cancellation _ _).trans (map_zero (apSmoothJet admissible 1 cell)).symm))

end Grad.GaugeCoefficients.Physical.Compensated
