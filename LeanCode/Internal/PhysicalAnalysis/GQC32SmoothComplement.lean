import GQC31APSmoothRotation

noncomputable section

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope

theorem apComplement_trace {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {grade : ℕ} (large : 2 ≤ grade) (field : apGrade L sigma gamma ell 3 grade) (cell : ℤ) :
    apTrace admissible large cell (apComplement L sigma gamma ell grade field) = cMapComplement (apTrace admissible large cell field) := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := 3) (grade := grade) L sigma gamma ell)
    (isClosed_eq ((apTrace admissible large cell).continuous.comp (apComplement L sigma gamma ell grade).continuous)
      (cMapComplement.continuous.comp (apTrace admissible large cell).continuous)) _ field
  intro core
  simp only [Function.comp_apply]
  rw [apComplement_core, apTrace_core, apTrace_core, cMapComplement_jet]
  rfl

theorem apSmoothComplement_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) (cell : ℤ) :
    apSmoothJet admissible 3 cell (apSmoothComplement L sigma gamma ell field) =
      fixedComplementJet (apSmoothJet admissible 3 cell field) := by
  apply closedJet_eq_of_value_eq
  change (apFamilyJet (apSmoothComplement L sigma gamma ell field).val _ cell).value = _
  rw [apFamilyJet_value_trace admissible (apSmoothComplement L sigma gamma ell field).val
    (apSmoothComplement L sigma gamma ell field).property (by omega : 2 ≤ 2) cell]
  change apTrace admissible (by omega : 2 ≤ 2) cell (apComplement L sigma gamma ell 2 (field.val 2)) = _
  rw [apComplement_trace, ← apFamilyJet_value_trace admissible field.val field.property (by omega : 2 ≤ 2) cell,
    cMapComplement_jet]
  rfl

theorem apSmoothCircle_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (field : APSmooth L sigma gamma ell 3) (cell : ℤ) :
    apSmoothJet admissible 3 cell (apSmoothCircle L sigma gamma ell field) =
      apSmoothJet admissible 3 cell field - fixedComplementJet (apSmoothJet admissible 3 cell field) := by
  change apSmoothJet admissible 3 cell (field - apSmoothComplement L sigma gamma ell field) = _
  rw [map_sub, apSmoothComplement_jet]

theorem apSmoothRotation_valueMap {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (mapping : ComplexEuclidean input →L[ℂ] ComplexEuclidean output)
    (field : APSmooth L sigma gamma ell input) :
    apSmoothRotation admissible output (apSmoothValueMap L sigma gamma ell mapping field) =
      apSmoothValueMap L sigma gamma ell mapping (apSmoothRotation admissible input field) := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothRotation_jet admissible (apSmoothValueMap L sigma gamma ell mapping field) cell).trans
    ((congrArg Grad.NonlinearRange.rotationJet (apSmoothValueMap_jet admissible mapping field cell)).trans
      ((Grad.GaugeCoefficients.Physical.GaugeTransfer.rotationJet_valueMap mapping
        (apSmoothJet admissible input cell field)).trans
        ((congrArg (valueMapJet mapping) (apSmoothRotation_jet admissible field cell).symm).trans
          (apSmoothValueMap_jet admissible mapping (apSmoothRotation admissible input field) cell).symm)))

end Grad.GaugeCoefficients.Physical.Compensated
