import AKDP61SameOriginalMixedGraphNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.WeightedJets.SpatialMultiplier Grad.ActualOriginalSourceMoments Grad.CartesianCoreRecovery Grad.NonlinearProduct

def startupCutoffMixedGraph (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff)
    (compact : HasCompactSupport cutoff) (grade : ℕ) : Mixed 3 grade openUnitDisk →L[ℂ] Mixed 3 grade openUnitDisk :=
  compactJetMultiplier 3 grade openUnitDisk openUnitDisk_isOpen cutoff smooth compact
    (fun index => grade-degree index) (mixedExponent_antitone grade)

theorem startupCutoffMixedGraph_base (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff)
    (compact : HasCompactSupport cutoff) (grade : ℕ) (field : Mixed 3 grade openUnitDisk) :
    base 3 grade openUnitDisk (fun index => grade-degree index) (startupCutoffMixedGraph cutoff smooth compact grade field)=
      startupCutoffL2 cutoff smooth compact (base 3 grade openUnitDisk (fun index => grade-degree index) field) := by
  change base 3 grade openUnitDisk (fun index => grade-degree index)
    (jetMultiplier 3 grade openUnitDisk openUnitDisk_isOpen (compactSymbol grade openUnitDisk cutoff smooth compact)
      (fun index => grade-degree index) (mixedExponent_antitone grade) field)=_
  rw [jetMultiplier_base_apply]
  apply startupField_ae_ext
  filter_upwards [fieldMultiplier_ae 3 openUnitDisk openUnitDisk_isOpen
      (derivativeScalar (compactSymbol grade openUnitDisk cutoff smooth compact) (zeroIndex grade))
      (base 3 grade openUnitDisk (fun index => grade-degree index) field),
    startupCutoffL2_ae cutoff smooth compact (base 3 grade openUnitDisk (fun index => grade-degree index) field)]
    with point multiplied localized
  intro cell
  rw [multiplied cell,localized cell]
  rfl

/-- Same-order original norm of a fixed cutoff of the genuine weighted
field. The finite mixed multiplier avoids paying the diagonal reserve. -/
theorem startupOriginalCutoff_core_bound (parameters : PhaseParameters)
    (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff) (compact : HasCompactSupport cutoff)
    (grade : ℕ) (core image : ACore parameters 3)
    (same : (originalSourceMoments parameters image).field=
      startupCutoffL2 cutoff smooth compact (originalSourceMoments parameters core).field) :
    originalGradeNorm grade image≤‖startupCutoffMixedGraph cutoff smooth compact grade‖*originalGradeNorm grade core := by
  let inputProof := startupOriginal_reservedGraph parameters core (L := 1) (ell := 1) one_ne_zero one_ne_zero grade grade
  let input := diagonalGraphToMixed inputProof.choose
  have inputSame : base 3 grade openUnitDisk (fun index => grade-degree index) input=(originalSourceMoments parameters core).field :=
    (diagonalGraphToMixed_base inputProof.choose).trans inputProof.choose_spec
  have imageSame : base 3 grade openUnitDisk (fun index => grade-degree index)
      (startupCutoffMixedGraph cutoff smooth compact grade input)=(originalSourceMoments parameters image).field := by
    rw [startupCutoffMixedGraph_base,inputSame,←same]
  rw [startupOriginalMixedNorm_eq_graph parameters image _ imageSame,
    startupOriginalMixedNorm_eq_graph parameters core input inputSame]
  exact (startupCutoffMixedGraph cutoff smooth compact grade).le_opNorm input

theorem startupOriginalCutoff_core_exists (parameters : PhaseParameters)
    (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff) (compact : HasCompactSupport cutoff)
    (core : ACore parameters 3) :
    ∃ image : ACore parameters 3,(originalSourceMoments parameters image).field=
      startupCutoffL2 cutoff smooth compact (originalSourceMoments parameters core).field := by
  obtain ⟨image,same,_⟩ := startupLocalized_sameOriginalCore parameters (startupOriginalSignedFamily parameters core 1 1)
    (startupOriginalSignedFamily_allSpatial parameters core one_ne_zero one_ne_zero) cutoff smooth compact 0
  rw [StartupSignedFamily.zero] at same
  exact ⟨image,same⟩

end Grad.CartesianStartup
