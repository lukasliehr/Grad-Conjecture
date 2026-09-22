import AKCG10ActualAxialLeadingSplit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.RadialLedger

/-- Only the already regular lower axial powers are used in this graph.
The highest axial power is reserved for the principal same-field equation. -/
def startupPositiveAxialRemainderGraph {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output order weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (power : ℕ) (reserve : order - 1 ≤ weight)
    (lower : Fin power → GraphGrade input order weight openUnitDisk) : GraphGrade output order 0 openUnitDisk :=
  ∑ j : Fin power, (power.choose (j.val+1) : ℂ) •
    startupCellDisplacementGraph admissible family coherent (j.val+1) reserve (lower j)

theorem startupPositiveAxialRemainderGraph_base {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {input output order weight : ℕ}
    (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (power : ℕ) (reserve : order - 1 ≤ weight)
    (lower : Fin power → GraphGrade input order weight openUnitDisk)
    (moments : ℕ → StartupL2 input)
    (same : ∀ j : Fin power, base input order openUnitDisk (fun _ => weight) (lower j) = moments (power-(j.val+1))) :
    base output order openUnitDisk (fun _ => 0)
      (startupPositiveAxialRemainderGraph admissible family coherent power reserve lower) =
      startupPositiveAxialRemainder admissible family coherent power moments := by
  simp only [startupPositiveAxialRemainderGraph, startupPositiveAxialRemainder,
    map_sum, map_smul, startupCellDisplacementGraph_base, same]

end Grad.CartesianStartup
