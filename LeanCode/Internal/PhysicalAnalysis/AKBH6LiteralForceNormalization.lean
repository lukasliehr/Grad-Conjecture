import AKBH3SameLiteralForceMatrix

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.ActualForceMoments
open Grad.PDEBootstrap Grad.GenericCarriers Grad.CartesianStartup Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Physical.Ledger Grad.SourceCollarCoefficients

/-- Original force factors: two planar rows and minus two times the third
frame column, cancelling its stored inverse-length normalization. -/
def forceCorrectionMap (length : ℝ) : PhysicalValue 3 →L[ℂ] PhysicalValue 3 :=
  (2 : ℂ) • matrixUnit (0 : Fin 3) (0 : Fin 3) +
    (2 : ℂ) • matrixUnit (1 : Fin 3) (1 : Fin 3) -
    ((2 * length : ℝ) : ℂ) • matrixUnit (2 : Fin 3) (2 : Fin 3)

theorem forceCorrectionMap_apply (length : ℝ) (value : PhysicalValue 3) :
    forceCorrectionMap length value = WithLp.toLp 2 ![2 * value 0,2 * value 1,-2 * (length : ℂ) * value 2] := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [forceCorrectionMap,matrixUnit_apply,operatorBasis]

theorem forceCorrectionMap_matrix (length : ℝ) (nonzero : length ≠ 0)
    (matrix : Matrix (Fin 3) (Fin 3) ℂ) (value : PhysicalValue 3) :
    forceCorrectionMap length (WithLp.toLp 2
      ((matrix * Matrix.diagonal ![1,1,(length : ℂ)⁻¹]).transpose.mulVec value)) =
        WithLp.toLp 2 ![2 * (matrix.transpose.mulVec value) 0,
          2 * (matrix.transpose.mulVec value) 1,-2 * (matrix.transpose.mulVec value) 2] := by
  rw [forceCorrectionMap_apply]
  apply PiLp.ext
  intro coordinate
  have complexNonzero : (length : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  fin_cases coordinate <;>
    simp [Matrix.mulVec,Matrix.mul_apply,dotProduct,Fin.sum_univ_three]
  field_simp [complexNonzero]

/-- Per-cell L1 follows from the actual joint-cell L2 field on the disk. -/
theorem startupField_cell_integrable {dimension : ℕ} (field : StartupL2 dimension) (cell : ℤ) :
    IntegrableOn (fun point => field point cell) openUnitDisk :=
  (lp.evalCLM ℂ (fun _ : ℤ => PhysicalValue dimension) 2 cell).integrable_comp
    ((Lp.memLp field).integrable (by norm_num))

theorem startupRaw_cell_integrable {dimension : ℕ} (field : StartupL2 dimension)
    (raw : ℤ → Spatial → PhysicalValue dimension)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, field point cell = raw cell point)
    (cell : ℤ) : IntegrableOn (raw cell) openUnitDisk :=
  (startupField_cell_integrable field cell).congr (same.mono (fun _ equality => equality cell))

theorem startupValueMap_same {input output : ℕ} (family : StartupMoments input)
    (mapping : PhysicalValue input →L[ℂ] PhysicalValue output)
    (raw : ℤ → Spatial → PhysicalValue input)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, family.field point cell = raw cell point) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (family.map (originalValueKernel mapping) (originalValueKernel_cellwise mapping)).field point cell = mapping (raw cell point) := by
  filter_upwards [startupPointKernel_field_ae mapping (LinearIsometryEquiv.refl ℝ _) family.field,same]
    with point mapped actual
  intro cell
  change (originalValueKernel mapping family.field) point cell = _
  exact (mapped cell).trans (congrArg mapping (actual cell))

end Grad.ActualForceMoments
