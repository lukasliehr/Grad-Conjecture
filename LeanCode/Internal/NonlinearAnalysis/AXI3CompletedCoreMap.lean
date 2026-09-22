import AXI2L2Multipliers

noncomputable section

namespace Grad.RawSourceFaithfulness

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct

variable {dimension : ℕ} (parameters : PhaseParameters)
variable (mapping : ACore parameters dimension →ₗ[ℂ] ACore parameters dimension)
variable (constant : ℝ)
variable (bounded : ∀ field, originalGradeNorm 0 (mapping field) ≤ constant * originalGradeNorm 0 field)

def completeCoreMap : AGrade parameters dimension 0 →L[ℂ] AGrade parameters dimension 0 :=
  denseCoreExtension parameters
    ((aGradeEta parameters).toLinearMap.comp
      (GradeCore.ofCoreLinear.comp (mapping.comp GradeCore.toCoreLinear)))
    constant (fun field => by
      change ‖aGradeEta parameters (GradeCore.ofCoreLinear (mapping field.toCore))‖ ≤ _
      rw [aGradeEta_norm]
      exact bounded field.toCore)

theorem completeCoreMap_core (field : ACore parameters dimension) :
    completeCoreMap parameters mapping constant bounded
        (aGradeEta parameters (GradeCore.ofCoreLinear field)) =
      aGradeEta parameters (GradeCore.ofCoreLinear (mapping field)) :=
  denseCoreExtension_apply_eta parameters _ _ _ _

theorem zeroCell_completeCoreMap (factor : SpatialPlane → ℂ) (smooth : Continuous factor)
    (factorBound : ℝ) (factorBounded : ∀ point ∈ openUnitDisk, ‖factor point‖ ≤ factorBound)
    (literal : ∀ (field : ACore parameters dimension) (cell : ℤ) (point : ClosedDisk),
      ((mapping field).val cell).value point = factor point.val • (field.val cell).value point)
    (cell : ℤ) (field : AGrade parameters dimension 0) :
    zeroCell parameters cell (completeCoreMap parameters mapping constant bounded field) =
      diskScalarMultiplier factor smooth factorBound factorBounded (zeroCell parameters cell field) := by
  apply isClosed_property (aGradeEta_denseRange parameters)
    (isClosed_eq
      ((zeroCell parameters cell).continuous.comp
        (completeCoreMap parameters mapping constant bounded).continuous)
      ((diskScalarMultiplier factor smooth factorBound factorBounded).continuous.comp
        (zeroCell parameters cell).continuous)) _ field
  intro core
  change zeroCell parameters cell
      (completeCoreMap parameters mapping constant bounded (aGradeEta parameters core)) = _
  have coreEta : aGradeEta parameters core =
      aGradeEta parameters (GradeCore.ofCoreLinear core.toCore) := by rw [GradeCore.ofCore_toCore]
  simp only [Function.comp_apply]
  rw [coreEta, completeCoreMap_core, zeroCell_core, zeroCell_core, diskScalarMultiplier_closed]
  congr 1
  apply ContinuousMap.ext
  intro point
  rw [phaseWeightedJet_spec, literal]
  change cartesianWeight parameters cell point.val •
      (factor point.val • (core.toCore.val cell).value point) =
    factor point.val • (phaseWeightedJet parameters cell (core.toCore.val cell)).value point
  rw [phaseWeightedJet_spec]
  exact smul_comm _ _ _

theorem completeCoreMap_injective (factor : SpatialPlane → ℂ) (smooth : Continuous factor)
    (factorBound : ℝ) (factorBounded : ∀ point ∈ openUnitDisk, ‖factor point‖ ≤ factorBound)
    (literal : ∀ (field : ACore parameters dimension) (cell : ℤ) (point : ClosedDisk),
      ((mapping field).val cell).value point = factor point.val • (field.val cell).value point)
    (nonzero : ∀ᵐ point ∂MeasureTheory.volume.restrict openUnitDisk, factor point ≠ 0) :
    Function.Injective (completeCoreMap parameters mapping constant bounded) := by
  intro first second equality
  apply zeroCell_ext parameters
  intro cell
  apply diskScalarMultiplier_injective factor smooth factorBound factorBounded nonzero
  rw [← zeroCell_completeCoreMap parameters mapping constant bounded factor smooth factorBound factorBounded literal,
    ← zeroCell_completeCoreMap parameters mapping constant bounded factor smooth factorBound factorBounded literal,
    equality]

end Grad.RawSourceFaithfulness
