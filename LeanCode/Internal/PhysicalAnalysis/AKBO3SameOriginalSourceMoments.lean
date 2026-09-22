import AKBO2OriginalSourceJointCarrier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators ENNReal
namespace Grad.ActualOriginalSourceMoments
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers
open Grad.ActualScalarWeakEquations Grad.CartesianStartup Grad.SpatialDilation

variable {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)

/-- Three actual frequency moments of the same source at the original analytic width. -/
def originalSourceMoments : StartupMoments dimension where
  field := originalSourceJointField parameters field 0
  moment grade := originalSourceJointField parameters field grade.val
  zero := rfl
  same := by
    have grades := ae_all_iff.mpr (fun grade : Fin 3 => originalSourceJointField_same parameters field grade.val)
    filter_upwards [grades,originalSourceJointField_same parameters field 0] with point allGrades zero
    intro grade cell
    simp only [pow_zero,one_smul] at zero
    simpa only [pow_zero,one_smul,cellFrequency] using
      (allGrades grade cell).trans (congrArg (Grad.CellWeights.cellWeight cell^grade.val • ·) (zero cell).symm)

theorem originalSourceMoments_same :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (originalSourceMoments parameters field).field point cell =
        cartesianWeight parameters cell point • originalCoreCell parameters field cell point := by
  simpa only [originalSourceMoments,pow_zero,one_smul] using originalSourceJointField_same parameters field 0

/-- The identical unweighted source, preserving every cell and all three moments. -/
def originalSourceRawMoments : StartupMoments dimension :=
  (originalSourceMoments parameters field).unweight parameters (⟨1,by norm_num⟩ : Scale)

theorem originalSourceRawMoments_same :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (originalSourceRawMoments parameters field).field point cell = originalCoreCell parameters field cell point := by
  exact (originalSourceMoments parameters field).unweight_same parameters (⟨1,by norm_num⟩ : Scale)
    (originalCoreCell parameters field) (originalSourceMoments_same parameters field)

theorem originalSourceRawMoments_norm (grade : Fin 3) :
    ‖(originalSourceRawMoments parameters field).moment grade‖ ≤ ‖(originalSourceMoments parameters field).moment grade‖ :=
  (originalSourceMoments parameters field).unweight_norm parameters (⟨1,by norm_num⟩ : Scale) grade

/-- Dimension-generic source endpoint: genuine joint carriers with exact same-field representatives, no per-cell injection substitute. -/
theorem originalCore_jointMoments : ∃ weighted unweighted : StartupMoments dimension,
    (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      weighted.field point cell = cartesianWeight parameters cell point • originalCoreCell parameters field cell point) ∧
    (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      unweighted.field point cell = originalCoreCell parameters field cell point) ∧
    (∀ grade : Fin 3, ‖unweighted.moment grade‖ ≤ ‖weighted.moment grade‖) :=
  ⟨originalSourceMoments parameters field,originalSourceRawMoments parameters field,
    originalSourceMoments_same parameters field,originalSourceRawMoments_same parameters field,
    originalSourceRawMoments_norm parameters field⟩

end Grad.ActualOriginalSourceMoments
