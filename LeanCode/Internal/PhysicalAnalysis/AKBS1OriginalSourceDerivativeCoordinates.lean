import AKBO4ActualOriginalSourceCarriers
import AKAA23ActualFirstGraphAssembly
import AKAD1ClassicalCompactDivergence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 850000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators ENNReal
namespace Grad.ActualOriginalSourceFirst
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.PDEBootstrap
open Grad.ActualOriginalSourceMoments Grad.ActualScalarWeakEquations Grad.CartesianStartup

variable {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)

/-- The existing phase-weighted closed jet, with its actual smooth extension. -/
def originalWeightedSourceCell (cell : ℤ) : Spatial → ComplexEuclidean dimension :=
  smoothClosedExtension (phaseWeightedJet parameters cell (field.val cell))

theorem originalWeightedSourceCell_smooth (cell : ℤ) :
    ContDiff ℝ ∞ (originalWeightedSourceCell parameters field cell) :=
  smoothClosedExtension_smooth _

theorem originalWeightedSourceCell_same (cell : ℤ) (point : Spatial) (inside : point ∈ openUnitDisk) :
    originalWeightedSourceCell parameters field cell point =
      cartesianWeight parameters cell point • originalCoreCell parameters field cell point := by
  let closed : ClosedDisk := ⟨point,openDiskMembershipClosed point inside⟩
  exact (smoothClosedExtension_value _ closed).trans
    ((phaseWeightedJet_value parameters cell (field.val cell) closed).trans
      (congrArg (fun value => cartesianWeight parameters cell point • value)
        (originalCoreCell_value parameters field cell closed).symm))

def originalSourceFirstGradeIndex (direction : Fin 2) : GradeMultiIndex 1 :=
  if direction = 0 then ⟨(1,0),by decide⟩ else ⟨(0,1),by decide⟩

def originalSourceDerivativeCoordinate (direction : Fin 2) (cell : ℤ) : DiskL2 dimension :=
  closedContinuousToDiskL2 (closedDerivative (phaseWeightedJet parameters cell (field.val cell))
    1 (fun _ => direction))

theorem originalSourceDerivativeCoordinate_grade (direction : Fin 2) (cell : ℤ) :
    originalSourceDerivativeCoordinate parameters field direction cell =
      rawCartesianGradeCoordinates parameters 1 field.val cell (originalSourceFirstGradeIndex direction) := by
  have firstWord : cartesianMultiIndexWord (1,0) = (fun _ : Fin 1 => (0 : Fin 2)) := by
    funext position
    fin_cases position
    rfl
  have secondWord : cartesianMultiIndexWord (0,1) = (fun _ : Fin 1 => (1 : Fin 2)) := by
    funext position
    fin_cases position
    rfl
  fin_cases direction <;>
    simp [originalSourceDerivativeCoordinate,rawCartesianGradeCoordinates,cellGradeRowLinear_apply,
      originalSourceFirstGradeIndex,GradeMultiIndex.toCartesian,closedMultiDerivative,
      cartesianOrder,firstWord,secondWord]

theorem originalSourceDerivativeCoordinate_summable (direction : Fin 2) :
    Summable (fun cell => ‖originalSourceDerivativeCoordinate parameters field direction cell‖^2) := by
  have summable := (memlp_iff_summable_sq (rawCartesianGradeCoordinates parameters 1 field.val)).mp (field.property 1)
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ summable
  intro cell
  rw [originalSourceDerivativeCoordinate_grade]
  exact pow_le_pow_left₀ (norm_nonneg _)
    (PiLp.norm_apply_le (rawCartesianGradeCoordinates parameters 1 field.val cell) (originalSourceFirstGradeIndex direction)) 2

theorem originalSourceDerivativeCoordinate_same (direction : Fin 2) (cell : ℤ) :
    ∀ᵐ point ∂volume.restrict openUnitDisk,
      originalSourceDerivativeCoordinate parameters field direction cell point =
        fderiv ℝ (originalWeightedSourceCell parameters field cell) point (spatialBasis direction) := by
  filter_upwards [closedContinuousToDiskL2_ae (closedDerivative
      (phaseWeightedJet parameters cell (field.val cell)) 1 (fun _ => direction)),
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point same inside
  rw [originalSourceDerivativeCoordinate,same,closedDiskLift,dif_pos (openDiskMembershipClosed point inside)]
  exact (smoothClosedExtension_derivative (phaseWeightedJet parameters cell (field.val cell))
    (fun _ : Fin 1 => direction) ⟨point,openDiskMembershipClosed point inside⟩).symm.trans
      (by simp only [cartesianDerivative,iteratedFDeriv_one_apply]; rfl)

end Grad.ActualOriginalSourceFirst
