import GQF14CircularDomain

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open scoped ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.Allocation
open Grad.NonlinearDivision

variable {L sigma gamma ell : ℝ}

theorem closedFirstJetZero_of_axisFlat {dimension : ℕ} (field : ClosedJet dimension)
    (flat : ClosedAxisFlat field.value) : ClosedFirstJetZero field := by
  refine ⟨flat.origin, ?_⟩
  intro coordinate
  have derivative := ((closedAxisFlat_iff_firstJet field.value).mp flat).2
  rw [partialJet_value_fderiv coordinate field closedOrigin (by simp [closedOrigin, openUnitDisk])]
  exact congrArg (fun mapping : SpatialPlane →L[ℝ] ComplexEuclidean dimension => mapping (spatialBasis coordinate))
    derivative.fderiv

theorem closedFirstJetZero_angular {dimension : ℕ} (field : ClosedJet dimension)
    (flat : ClosedFirstJetZero field) (mode : ℤ) : ClosedFirstJetZero (angularClosedJet mode field) := by
  apply closedFirstJetZero_of_axisFlat
  have original := closedJet_axisFlat field flat.1 flat.2
  have projected := original.character mode
  have value : (fun point => closedCharacterProjection mode field.value point) =
      (angularClosedJet mode field).value := funext (closedCharacterProjection_jet mode field)
  exact (congrArg ClosedAxisFlat value).mp projected

theorem closedFirstJetZero_valueMap {input output : ℕ}
    (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (field : ClosedJet input) (flat : ClosedFirstJetZero field) :
    ClosedFirstJetZero (valueMapJet mapping field) := by
  constructor
  · rw [valueMapJet_value, flat.1, map_zero]
  · intro coordinate
    rw [partialJet_valueMap, valueMapJet_value, flat.2 coordinate, map_zero]

theorem apSmoothAngularMean_preserves_firstJet (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension)
    (flat : APSmoothAxisFirstJetZero admissible field) :
    APSmoothAxisFirstJetZero admissible (apSmoothAngularMean L sigma gamma ell dimension field) := by
  apply apSmoothAxisFirstJetZero_of_closed admissible
  intro cell
  exact (congrArg ClosedFirstJetZero (apSmoothAngularMean_jet admissible field cell)).mpr
    (closedFirstJetZero_angular _ (apSmoothAxisFirstJetZero_closed admissible field flat cell) 0)

theorem apSmoothRemoveMean_preserves_firstJet (admissible : Admissible L sigma gamma ell)
    {dimension : ℕ} (field : APSmooth L sigma gamma ell dimension)
    (flat : APSmoothAxisFirstJetZero admissible field) :
    APSmoothAxisFirstJetZero admissible (apSmoothRemoveMean L sigma gamma ell dimension field) :=
  (mem_apSmoothAxisFirsts admissible _).mp ((apSmoothAxisFirsts admissible dimension).sub_mem
    ((mem_apSmoothAxisFirsts admissible field).mpr flat)
    ((mem_apSmoothAxisFirsts admissible _).mpr (apSmoothAngularMean_preserves_firstJet admissible field flat)))

theorem apSmoothValueMap_preserves_firstJet (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (field : APSmooth L sigma gamma ell input) (flat : APSmoothAxisFirstJetZero admissible field) :
    APSmoothAxisFirstJetZero admissible (apSmoothValueMap L sigma gamma ell mapping field) := by
  apply apSmoothAxisFirstJetZero_of_closed admissible
  intro cell
  exact (congrArg ClosedFirstJetZero (apSmoothValueMap_jet admissible mapping field cell)).mpr
    (closedFirstJetZero_valueMap mapping _ (apSmoothAxisFirstJetZero_closed admissible field flat cell))

/-- Continuous physical coefficient multiplication preserves the actual
zero first jet. Smooth reconstruction is the accepted AP2 realization. -/
theorem apSmoothMultiplier_preserves_firstJet (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (coefficient : CoefficientFamily L sigma gamma ell input output)
    (coherent : FamilyCoherent coefficient) (field : APSmooth L sigma gamma ell input)
    (flat : APSmoothAxisFirstJetZero admissible field) :
    APSmoothAxisFirstJetZero admissible (apSmoothMultiplier admissible coefficient coherent field) := by
  apply (apSmoothAxisFirstJetZero_iff_grade admissible (by omega : 2 ≤ 2) _).mpr
  intro angle
  apply (closedAxisFlat_iff_firstJet _).mp
  have original := (closedAxisFlat_iff_firstJet _).mpr
    (((apSmoothAxisFirstJetZero_iff_grade admissible (by omega : 2 ≤ 2) field).mp flat) angle)
  change ClosedAxisFlat (apPhysicalValue admissible (by omega : 2 ≤ 2) angle
    (apMultiplier admissible (coefficient 2) (field.val 2)))
  rw [apMultiplier_physical]
  exact original.operator (cMapCoefficient admissible 2 input output angle (coefficient 2))

end Grad.GaugeCoefficients.Physical.Compensated
