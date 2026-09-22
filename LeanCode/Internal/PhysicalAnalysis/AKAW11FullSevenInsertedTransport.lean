import AKAW10HighPacketInsertedTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.ActualNativeCellMoments
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularCurrentEnergy
open Grad.AnnularReconstruction Grad.AnnularCrossMaps
open Grad.AnnularCurrentLow Grad.AnnularCurrentSource Grad.AnnularKnownLow Grad.AnnularStrongSolution
open Grad.AnnularStrongData Grad.AnnularStrongOrbit Grad.AnnularHighGenerators Grad.AnnularCoupledInverse

private theorem knownSevenPacket_scaled (lower : ℝ) (first second : HighKnownSourceBulk lower)
    (scale : ℤ × ℤ → ℂ) (same : ∀ slot mode, second slot mode = scale mode • first slot mode) (mode : ℤ × ℤ) :
    knownLowSevenPacket lower second mode = scale mode • knownLowSevenPacket lower first mode := by
  change radialMatrixUnit lower (4 : Fin 7) (0 : Fin 1) (second 0 mode) +
    radialMatrixUnit lower (5 : Fin 7) (0 : Fin 1) (second 1 mode) +
    radialMatrixUnit lower (6 : Fin 7) (0 : Fin 1) (second 2 mode) = _
  rw [same 0 mode,same 1 mode,same 2 mode,map_smul,map_smul,map_smul,← smul_add,← smul_add]
  rfl

/-- The original full packet preserves a literal inserted grade of the SAME
unknown and once-only source tuple. No graded solution equation is assumed. -/
theorem fullSevenPacket_inserted (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (grade : ℕ) (field weighted : CoupledSpace lower length positive lengthPositive)
    (data weightedData : StrongDataCarrier parameters lower positive bounded 0 0)
    (sameField : CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (sameData : StrongInsertedGrade parameters lower positive bounded grade data weightedData)
    (mode : ℤ × ℤ) :
    fullStrongSevenInput parameters length lower lengthPositive positive bounded weightedData weighted mode =
      ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        fullStrongSevenInput parameters length lower lengthPositive positive bounded data field mode := by
  let scale := fun mode : ℤ × ℤ => ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ)
  have high := highSevenPacket_scaled lower length positive lengthPositive field.ofLp.1 weighted.ofLp.1
    scale sameField.1 (sameField.2.1 0) mode
  have low := lowSevenPacket_scaled parameters lower length positive lengthPositive (field.ofLp.2.val 0) (weighted.ofLp.2.val 0)
    scale (sameField.2.2 0) mode
  have known : ∀ slot other, strongKnownBulk parameters lower positive bounded weightedData slot other =
      scale other • strongKnownBulk parameters lower positive bounded data slot other := by
    intro slot other
    have same := sameData.1 slot other
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)] at same
    exact same
  have source := knownSevenPacket_scaled lower _ _ scale known mode
  change (highCrossSevenInput lower length positive lengthPositive weighted.ofLp.1 mode +
    lowNormalizedSevenInput parameters lower length lengthPositive positive (weighted.ofLp.2.val 0) mode) +
    knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded weightedData) mode = _
  rw [high,low,source,← smul_add,← smul_add]
  rfl

end Grad.ActualNativeCellMoments
