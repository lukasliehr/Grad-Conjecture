import AKBJ5OriginalSourceCartesianCells
import AKBH2SameInverseWeightMoments

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 850000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators ENNReal
namespace Grad.ActualOriginalSourceMoments
open Grad.ClosedJets Grad.CartesianState Grad.ActualScalarWeakEquations Grad.PDEBootstrap

variable {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)

/-- The already constructed original grade coordinate at spatial derivative order zero. -/
def originalSourceCellCoordinate (grade : ℕ) (cell : ℤ) : DiskL2 dimension :=
  rawCartesianGradeCoordinates parameters grade field.val cell (zeroGradeIndex grade)

theorem originalSourceCellCoordinate_value (grade : ℕ) (cell : ℤ) :
    originalSourceCellCoordinate parameters field grade cell =
      (cellFrequency cell : ℂ)^grade • closedContinuousToDiskL2 (phaseWeightedJet parameters cell (field.val cell)).value := by
  simp only [originalSourceCellCoordinate,rawCartesianGradeCoordinates,cellGradeRowLinear_apply,
    zeroGradeIndex_toCartesian,closedMultiDerivative_zero,cartesianOrder,zero_add,Nat.sub_zero]

/-- Full signed-cell square summability is inherited directly from the original ACore grade. -/
theorem originalSourceCellCoordinate_summable (grade : ℕ) :
    Summable (fun cell => ‖originalSourceCellCoordinate parameters field grade cell‖^2) := by
  have summable := (memlp_iff_summable_sq (rawCartesianGradeCoordinates parameters grade field.val)).mp (field.property grade)
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ summable
  intro cell
  exact pow_le_pow_left₀ (norm_nonneg _)
    (PiLp.norm_apply_le (rawCartesianGradeCoordinates parameters grade field.val cell) (zeroGradeIndex grade)) 2

/-- Exact original weight and unchanged smooth source cell, before assembling the joint carrier. -/
theorem originalSourceCellCoordinate_ae (grade : ℕ) (cell : ℤ) :
    ∀ᵐ point ∂volume.restrict openUnitDisk,
      originalSourceCellCoordinate parameters field grade cell point =
        cellFrequency cell^grade • (cartesianWeight parameters cell point • originalCoreCell parameters field cell point) := by
  rw [originalSourceCellCoordinate_value]
  filter_upwards [Lp.coeFn_smul ((cellFrequency cell : ℂ)^grade)
      (closedContinuousToDiskL2 (phaseWeightedJet parameters cell (field.val cell)).value),
    closedContinuousToDiskL2_ae (phaseWeightedJet parameters cell (field.val cell)).value,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point smulAt weightedAt inside
  rw [smulAt,Pi.smul_apply,weightedAt,closedDiskLift,dif_pos (openDiskMembershipClosed point inside)]
  rw [phaseWeightedJet_value]
  have source := originalCoreCell_value parameters field cell ⟨point,openDiskMembershipClosed point inside⟩
  rw [← source,← Complex.ofReal_pow,Complex.coe_smul]

end Grad.ActualOriginalSourceMoments
