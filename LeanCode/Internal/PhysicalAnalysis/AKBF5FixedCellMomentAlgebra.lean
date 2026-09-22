import AKAY33RoughAngularMapAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Algebra

/-- Literal diagonal action on every integer cell, before any spatial regularity. -/
def StartupCellwise {input output : ℕ} (operator : StartupL2 input →L[ℂ] StartupL2 output) : Prop :=
  ∀ cell : ℤ, ∃ mapping : DomainL2 (PhysicalValue input) openUnitDisk →L[ℂ]
      DomainL2 (PhysicalValue output) openUnitDisk,
    ∀ field, fieldCellProjection output openUnitDisk cell (operator field) =
      mapping (fieldCellProjection input openUnitDisk cell field)

theorem StartupCellwise.id (dimension : ℕ) : StartupCellwise (ContinuousLinearMap.id ℂ (StartupL2 dimension)) :=
  fun _ => ⟨ContinuousLinearMap.id ℂ _, fun _ => rfl⟩

theorem StartupCellwise.add {input output : ℕ} {first second : StartupL2 input →L[ℂ] StartupL2 output}
    (one : StartupCellwise first) (two : StartupCellwise second) : StartupCellwise (first + second) := by
  intro cell
  obtain ⟨left,leftSame⟩ := one cell
  obtain ⟨right,rightSame⟩ := two cell
  refine ⟨left + right,?_⟩
  intro field
  simp only [add_apply,map_add,leftSame,rightSame]

theorem StartupCellwise.sub {input output : ℕ} {first second : StartupL2 input →L[ℂ] StartupL2 output}
    (one : StartupCellwise first) (two : StartupCellwise second) : StartupCellwise (first - second) := by
  intro cell
  obtain ⟨left,leftSame⟩ := one cell
  obtain ⟨right,rightSame⟩ := two cell
  refine ⟨left - right,?_⟩
  intro field
  simp only [sub_apply,map_sub,leftSame,rightSame]

theorem StartupCellwise.smul {input output : ℕ} {operator : StartupL2 input →L[ℂ] StartupL2 output}
    (same : StartupCellwise operator) (scalar : ℂ) : StartupCellwise (scalar • operator) := by
  intro cell
  obtain ⟨mapping,mapped⟩ := same cell
  refine ⟨scalar • mapping,?_⟩
  intro field
  simp only [smul_apply,map_smul,mapped]

theorem StartupCellwise.comp {input middle output : ℕ}
    {first : StartupL2 middle →L[ℂ] StartupL2 output} {second : StartupL2 input →L[ℂ] StartupL2 middle}
    (one : StartupCellwise first) (two : StartupCellwise second) : StartupCellwise (first.comp second) := by
  intro cell
  obtain ⟨left,leftSame⟩ := one cell
  obtain ⟨right,rightSame⟩ := two cell
  exact ⟨left.comp right,fun field => (leftSame (second field)).trans (congrArg left (rightSame field))⟩

theorem startupPointKernel_cellwise {input output : ℕ} (mapping : OperatorValue input output)
    (orthogonal : Spatial ≃ₗᵢ[ℝ] Spatial) : StartupCellwise (startupPointKernel mapping orthogonal) :=
  fun cell => ⟨Grad.FullCellKernel.entry (startupPointKernelData mapping orthogonal) cell cell,
    fun field => startupPointKernel_coordinate mapping orthogonal field cell⟩

theorem startupAngularKernel_cellwise (dimension : ℕ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight) :
    StartupCellwise (startupAngularKernel dimension weight smooth) :=
  fun cell => ⟨Grad.FullCellKernel.entry (startupAngularKernelData dimension weight smooth) cell cell,
    fun field => startupAngularKernel_coordinate dimension weight smooth field cell⟩

/-- Unbounded frequency multipliers commute only through the proved fixed
cell-diagonal operators. Coefficient convolution is deliberately outside this lemma. -/
theorem StartupCellwise.moment {input output : ℕ} {operator : StartupL2 input →L[ℂ] StartupL2 output}
    (diagonal : StartupCellwise operator) (weight : ℤ → ℝ) (field moment : StartupL2 input)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      moment point cell = weight cell • field point cell) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (operator moment) point cell = weight cell • (operator field) point cell := by
  apply ae_all_iff.mpr
  intro cell
  obtain ⟨mapping,mapped⟩ := diagonal cell
  have localSame : fieldCellProjection input openUnitDisk cell moment =
      (weight cell) • fieldCellProjection input openUnitDisk cell field := by
    apply Lp.ext
    filter_upwards [same,fieldCellProjection_ae input openUnitDisk moment,
      fieldCellProjection_ae input openUnitDisk field,
      Lp.coeFn_smul (weight cell) (fieldCellProjection input openUnitDisk cell field)]
      with point equal one two scaled
    rw [one cell,scaled,Pi.smul_apply,two cell,equal cell]
  have outputSame : fieldCellProjection output openUnitDisk cell (operator moment) =
      (weight cell) • fieldCellProjection output openUnitDisk cell (operator field) := by
    rw [mapped,mapped,localSame]
    exact (mapping.restrictScalars ℝ).map_smul (weight cell) _
  have outputAE := Lp.ext_iff.mp outputSame
  filter_upwards [outputAE,fieldCellProjection_ae output openUnitDisk (operator moment),
    fieldCellProjection_ae output openUnitDisk (operator field),
    Lp.coeFn_smul (weight cell) (fieldCellProjection output openUnitDisk cell (operator field))]
    with point equal one two scaled
  rw [one cell,scaled,Pi.smul_apply,two cell] at equal
  exact equal

end Grad.CartesianStartup
