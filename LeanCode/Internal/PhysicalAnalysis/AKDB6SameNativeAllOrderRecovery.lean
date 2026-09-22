import AKDB4SameWeightedNativeScalar
import AKCX44ActualNativeLowerSpatialGraphs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Algebra

/-- Recover all grades of the SAME full covariant from its fixed circle
quotient and the actual current identity already proved for the native field. -/
theorem StartupSignedFamily.current_allSpatialGrade {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (ledger : LedgerData L sigma gamma ell)
    (coherent : LedgerCoherent ledger)
    (inverseCoherent : FamilyCoherent (determinantInverseFamily admissible ledger.gaugeDeviation))
    (lengthNonzero : L ≠ 0) (scaleNonzero : ell ≠ 0)
    (family : StartupSignedFamily 3 L ell) (order : ℕ) (regular : family.circle.HasSpatialGrade order)
    (recovered : originalCurrentKernel admissible ledger.gaugeDeviation coherent.2.2.2.1 inverseCoherent
      (originalCircleKernel family.field) = family.field) : family.HasSpatialGrade order := by
  apply ((StartupSpatialAction.current admissible order ledger.gaugeDeviation coherent.2.2.2.1 inverseCoherent lengthNonzero scaleNonzero).preserves
    order family.circle regular).congr
  exact recovered

/-- The genuine scalar psi inherits every completed spatial grade of the
recovered gradient. The original radial phase and the actual weak force
fix its identity; no regularity of an arbitrary radius multiple is used. -/
theorem StartupNativeWeakRows.weighted_scalar_allSpatialGraphs {L ell scale : ℝ}
    {psi weightedPsi : StartupL2 1} {weighted original : StartupNativeERRows}
    (weak : StartupNativeWeakRows scale psi original)
    {symbol : ℤ → Spatial → ℝ} (same : StartupNativeERRowsRelated symbol weighted original)
    (radial : ∀ cell (first second : Spatial), ‖first‖=‖second‖ → symbol cell first=symbol cell second)
    (scalarSame : StartupRadialRelated symbol weightedPsi psi)
    (gradient : StartupSignedFamily 2 L ell) (gradientSame : gradient.field=weighted.gradient.field)
    (regular : ∀ order, gradient.HasSpatialGrade order) :
    ∀ order weight, ∃ scalar : GraphGrade 1 order weight openUnitDisk,
      base 1 order openUnitDisk (fun _ => weight) scalar=weightedPsi := by
  intro order weight
  obtain ⟨graph,graphSame⟩ := regular order 0 weight
  rw [gradient.zero,gradientSame] at graphSame
  exact weak.weighted_scalar_graph same radial scalarSame order weight graph graphSame

end Grad.CartesianStartup
