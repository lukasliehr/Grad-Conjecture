import AKDP2SameOriginalReservedCarrier
import AKCX39SameCutoffAllSpatialGraphs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.CartesianCoreRecovery Grad.ActualOriginalSourceMoments Grad.NonlinearProduct

/-- Exact mixed norm of a fixed localized signed native moment. The graph
comes from the completed SAME-field spatial induction. -/
def startupLocalizedMixedJet {L ell : ℝ}
    (family : StartupSignedFamily 3 L ell) (regular : ∀ grade, family.HasSpatialGrade grade)
    (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff) (compact : HasCompactSupport cutoff)
    (power grade : ℕ) : Mixed 3 grade openUnitDisk :=
  diagonalGraphToMixed (startupCutoffSpatialGraph cutoff smooth compact grade grade ((regular grade power grade).choose))

theorem startupLocalizedMixedJet_base {L ell : ℝ}
    (family : StartupSignedFamily 3 L ell) (regular : ∀ grade, family.HasSpatialGrade grade)
    (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff) (compact : HasCompactSupport cutoff)
    (power grade : ℕ) :
    base 3 grade openUnitDisk (fun index => grade-degree index)
      (startupLocalizedMixedJet family regular cutoff smooth compact power grade) =
        startupCutoffL2 cutoff smooth compact (family.moment power) := by
  rw [startupLocalizedMixedJet,diagonalGraphToMixed_base,startupCutoffSpatialGraph_base,
    (regular grade power grade).choose_spec]

/-- A genuine original ACore realizing exactly the localized weighted
native field, with exact mixed norms. It is the quantitative input core,
separate from the global physical gluing core. -/
theorem startupLocalized_sameOriginalCore {L ell : ℝ}
    (parameters : PhaseParameters) (family : StartupSignedFamily 3 L ell)
    (regular : ∀ grade, family.HasSpatialGrade grade)
    (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff) (compact : HasCompactSupport cutoff)
    (power : ℕ) :
    ∃ core : ACore parameters 3,
      (originalSourceMoments parameters core).field = startupCutoffL2 cutoff smooth compact (family.moment power) ∧
      ∀ grade, originalGradeNorm grade core =
        ‖startupLocalizedMixedJet family regular cutoff smooth compact power grade‖ := by
  obtain ⟨core,same,norms⟩ := allMixed_sameOriginalCore parameters
    (startupCutoffL2 cutoff smooth compact (family.moment power))
    (startupLocalizedMixedJet family regular cutoff smooth compact power)
    (startupLocalizedMixedJet_base family regular cutoff smooth compact power)
  refine ⟨core,same,?_⟩
  intro grade
  have actual := norms grade
  rw [aGradeEta_norm] at actual
  exact actual

end Grad.CartesianStartup
