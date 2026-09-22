import AKCX27SameDifferentiatedWeakER
import ClosedJetWordCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators ENNReal
namespace Grad.ActualOriginalSourceFirst
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.PDEBootstrap Grad.GenericCarriers
open Grad.ActualOriginalSourceMoments Grad.ActualNativeCellMoments Grad.CartesianStartup

variable {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)

def originalSourceOrderedCoordinate (rank : ℕ) (word : CartesianWord rank) (cell : ℤ) : DiskL2 dimension :=
  closedContinuousToDiskL2 (closedDerivative (phaseWeightedJet parameters cell (field.val cell)) rank word)

theorem originalSourceOrderedCoordinate_summable (rank : ℕ) (word : CartesianWord rank) :
    Summable (fun cell => ‖originalSourceOrderedCoordinate parameters field rank word cell‖^2) := by
  have summable := (memlp_iff_summable_sq (rawCartesianGradeCoordinates parameters rank field.val)).mp (field.property rank)
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ summable
  intro cell
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  simpa only [originalSourceOrderedCoordinate,rawCartesianGradeCoordinates,Nat.sub_self,pow_zero,one_mul] using
    weighted_word_norm_le_row parameters cell (field.val cell) (le_refl rank) word

theorem originalSourceOrderedCoordinate_same (rank : ℕ) (word : CartesianWord rank) (cell : ℤ) :
    ∀ᵐ point ∂volume.restrict openUnitDisk,
      originalSourceOrderedCoordinate parameters field rank word cell point =
        cartesianDerivative rank word (originalWeightedSourceCell parameters field cell) point := by
  filter_upwards [closedContinuousToDiskL2_ae (closedDerivative
      (phaseWeightedJet parameters cell (field.val cell)) rank word),
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point same inside
  rw [originalSourceOrderedCoordinate,same,closedDiskLift,dif_pos (openDiskMembershipClosed point inside)]
  exact (smoothClosedExtension_derivative (phaseWeightedJet parameters cell (field.val cell))
    word ⟨point,openDiskMembershipClosed point inside⟩).symm

theorem originalSourceOrderedJoint_finite (rank : ℕ) (word : CartesianWord rank) :
    (∫⁻ point in openUnitDisk, ∑' cell : ℤ, ENNReal.ofReal
      (‖originalSourceOrderedCoordinate parameters field rank word cell point‖^2)) < ⊤ := by
  have coordinateNorm : ∀ coordinate : DiskL2 dimension,
      (∫⁻ point in openUnitDisk, ENNReal.ofReal (‖coordinate point‖^2)) = ENNReal.ofReal (‖coordinate‖^2) := by
    intro coordinate
    rw [diskL2_norm_sq]
    exact (ofReal_integral_eq_lintegral_ofReal (Lp.memLp coordinate).norm.integrable_sq
      (Eventually.of_forall (fun _ => sq_nonneg _))).symm
  rw [lintegral_tsum (fun cell => (Lp.memLp (originalSourceOrderedCoordinate parameters field rank word cell)).norm.integrable_sq.aestronglyMeasurable.aemeasurable.ennreal_ofReal)]
  simp_rw [coordinateNorm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun _ => sq_nonneg _) (originalSourceOrderedCoordinate_summable parameters field rank word)]
  exact ENNReal.ofReal_lt_top

def originalSourceOrderedJoint (rank : ℕ) (word : CartesianWord rank) : StartupL2 dimension :=
  (jointCellRepresentative_memLp (volume.restrict openUnitDisk)
    (fun cell point => originalSourceOrderedCoordinate parameters field rank word cell point)
    (fun cell => Lp.aestronglyMeasurable (originalSourceOrderedCoordinate parameters field rank word cell))
    (originalSourceOrderedJoint_finite parameters field rank word)).toLp _

theorem originalSourceOrderedJoint_same (rank : ℕ) (word : CartesianWord rank) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      originalSourceOrderedJoint parameters field rank word point cell =
        cartesianDerivative rank word (originalWeightedSourceCell parameters field cell) point := by
  let raw := fun cell point => originalSourceOrderedCoordinate parameters field rank word cell point
  have measurable := fun cell => Lp.aestronglyMeasurable (originalSourceOrderedCoordinate parameters field rank word cell)
  have finite := originalSourceOrderedJoint_finite parameters field rank word
  have membership := jointCellRepresentative_memLp (volume.restrict openUnitDisk) raw measurable finite
  have actual := ae_all_iff.mpr (originalSourceOrderedCoordinate_same parameters field rank word)
  filter_upwards [membership.coeFn_toLp,finiteCellEnergy_ae_memlp (volume.restrict openUnitDisk) raw measurable finite,actual]
    with point same member actual
  intro cell
  exact ((congrArg (fun value : CellValues dimension => value cell) same).trans
    (jointCellRepresentative_same raw point member cell)).trans (actual cell)

end Grad.ActualOriginalSourceFirst
