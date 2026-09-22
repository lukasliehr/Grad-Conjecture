import ANV3VectorGraphBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.ActualNonexceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra Grad.ActualAngularInverse
variable {L sigma gamma ell : ℝ}

theorem valueMapJet_identity {dimension : ℕ} (field : ClosedJet dimension) :
    valueMapJet (ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)) field = field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  exact valueMapJet_value _ _ _

def storedPair (L sigma gamma ell : ℝ) (vector : APSmooth L sigma gamma ell 2)
    (scalar : APSmooth L sigma gamma ell 1) : APSmooth L sigma gamma ell 3 :=
  apSmoothValueMap L sigma gamma ell planarInclusionMap vector +
    apSmoothValueMap L sigma gamma ell toroidalInclusionMap scalar

theorem storedPair_jet (admissible : Admissible L sigma gamma ell)
    (vector : APSmooth L sigma gamma ell 2) (scalar : APSmooth L sigma gamma ell 1) (cell : ℤ) :
    apSmoothJet admissible 3 cell (storedPair L sigma gamma ell vector scalar) =
      valueMapJet planarInclusionMap (apSmoothJet admissible 2 cell vector) +
        valueMapJet toroidalInclusionMap (apSmoothJet admissible 1 cell scalar) := by
  exact (map_add (apSmoothJet admissible 3 cell) _ _).trans
    (congrArg₂ (fun first second : ClosedJet 3 => first + second)
      (apSmoothValueMap_jet admissible planarInclusionMap vector cell)
      (apSmoothValueMap_jet admissible toroidalInclusionMap scalar cell))

theorem closedStoredPair_planar (vector : ClosedJet 2) (scalar : ClosedJet 1) :
    valueMapJet planarPartMap (valueMapJet planarInclusionMap vector + valueMapJet toroidalInclusionMap scalar) = vector := by
  rw [valueMapJet_add, valueMapJet_comp, valueMapJet_comp,
    planarPart_planarInclusion, planarPart_toroidalInclusion, valueMapJet_zero,
    valueMapJet_identity, add_zero]

theorem closedStoredPair_scalar (vector : ClosedJet 2) (scalar : ClosedJet 1) :
    valueMapJet toroidalPartMap (valueMapJet planarInclusionMap vector + valueMapJet toroidalInclusionMap scalar) = scalar := by
  rw [valueMapJet_add, valueMapJet_comp, valueMapJet_comp,
    toroidalPart_planarInclusion, toroidalPart_toroidalInclusion, valueMapJet_zero,
    valueMapJet_identity, zero_add]

theorem storedPair_planar (admissible : Admissible L sigma gamma ell)
    (vector : APSmooth L sigma gamma ell 2) (scalar : APSmooth L sigma gamma ell 1) :
    apSmoothPlanar L sigma gamma ell (storedPair L sigma gamma ell vector scalar) = vector := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothValueMap_jet admissible planarPartMap _ cell).trans
    ((congrArg (valueMapJet planarPartMap) (storedPair_jet admissible vector scalar cell)).trans
      (closedStoredPair_planar _ _))

theorem storedPair_scalar (admissible : Admissible L sigma gamma ell)
    (vector : APSmooth L sigma gamma ell 2) (scalar : APSmooth L sigma gamma ell 1) :
    apSmoothScalar L sigma gamma ell (storedPair L sigma gamma ell vector scalar) = scalar := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothValueMap_jet admissible toroidalPartMap _ cell).trans
    ((congrArg (valueMapJet toroidalPartMap) (storedPair_jet admissible vector scalar cell)).trans
      (closedStoredPair_scalar _ _))

end Grad.ActualNonexceptionalInverse
