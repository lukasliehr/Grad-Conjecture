import GC18APFaithful
import GC21Completion
import FiniteAngularProjection

noncomputable section

open scoped BigOperators

namespace Grad.CircularHighWeak

open Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.WeightedTrace
open Grad.GaugeCoefficients.Envelope Grad.AnalyticWeights.Calculus

/-- Auxiliary ordinary unit-disk graph, represented at the single cell zero.
This does not specialize or replace any downstream original analytic width. -/
abbrev DiskAmbient := apGrade 1 0 0 1 1 1

def diskCore : ClosedJet 1 →ₗ[ℂ] DiskAmbient :=
  (apFiniteInto 1 0 0 1).comp (Finsupp.lsingle 0)

def diskGrade : Submodule ℂ DiskAmbient := diskCore.range.topologicalClosure

instance diskGrade_complete : CompleteSpace diskGrade := by
  unfold diskGrade
  infer_instance

def diskCoreInto : ClosedJet 1 →ₗ[ℂ] diskGrade :=
  diskCore.codRestrict _ (fun field =>
    Submodule.le_topologicalClosure _ ⟨field, rfl⟩)

theorem diskCoreInto_denseRange : DenseRange diskCoreInto := by
  have dense : DenseRange (Set.inclusion (Submodule.le_topologicalClosure diskCore.range)) := by
    apply (denseRange_inclusion_iff _).2
    intro point member
    exact member
  apply dense.mono
  rintro _ ⟨⟨point, field, equality⟩, rfl⟩
  exact ⟨field, Subtype.ext equality⟩

theorem diskCore_cell (field : ClosedJet 1) (cell : ℤ) :
    (diskCore field).val cell = if cell = 0 then apRowLinear 1 0 0 1 0 field else 0 := by
  change apFiniteEmbed 1 0 0 1 (Finsupp.single 0 field) cell = _
  rw [apFiniteEmbed_apply]
  by_cases equal : cell = 0
  · subst cell
    simp
  · simp [equal]

/-- Closure does not introduce any hidden nonzero-cell coordinates. -/
theorem diskGrade_cell_zero (field : diskGrade) (cell : ℤ) (different : cell ≠ 0) :
    field.val.val cell = 0 := by
  apply isClosed_property diskCoreInto_denseRange
    (isClosed_eq
      ((lp.evalCLM ℂ (fun _ : ℤ => APRow 1 1) 2 cell).continuous.comp
        ((apGrade 1 0 0 1 1 1).subtypeL.continuous.comp diskGrade.subtypeL.continuous))
      continuous_const) _ field
  intro core
  exact (diskCore_cell core cell).trans (if_neg different)

def diskCoordinate (index : DerivativeIndex 1) : diskGrade →L[ℂ] DiskL2 1 :=
  (apUnscaledCoordinate 1 0 0 1 0 index).comp diskGrade.subtypeL

def diskBulk : diskGrade →L[ℂ] DiskL2 1 := diskCoordinate (zeroGradeIndex 1)

/-- The original full-disk compact-test argument supplies faithfulness;
derivative coordinates cannot vary independently of the bulk field. -/
theorem diskBulk_injective : Function.Injective diskBulk := by
  intro first second equality
  apply Subtype.ext
  apply apGrade_ext 1 0 0 1
  intro cell
  by_cases equal : cell = 0
  · subst cell
    exact equality
  · change ((scaledCellWeight 1 1 cell : ℂ) ^ 1)⁻¹ • first.val.val cell (zeroGradeIndex 1) =
      ((scaledCellWeight 1 1 cell : ℂ) ^ 1)⁻¹ • second.val.val cell (zeroGradeIndex 1)
    rw [diskGrade_cell_zero first cell equal, diskGrade_cell_zero second cell equal]

def diskTrace : diskGrade →L[ℂ] APBoundaryGrade 1 0 0 1 1 1 :=
  (apBoundaryTrace 1 0 0 1 1 (by decide)).comp diskGrade.subtypeL

theorem diskTrace_core (field : ClosedJet 1) :
    diskTrace (diskCoreInto field) =
      apCoreTraceLinear 1 0 0 1 1 (by decide) (Finsupp.single 0 field) :=
  apBoundaryTrace_core 1 0 0 1 1 (by decide) _

theorem diskTrace_bound (field : diskGrade) :
    ‖diskTrace field‖ ≤ Real.sqrt (traceCellConstant 1) * ‖field‖ :=
  apBoundaryTrace_bound 1 0 0 1 1 (by decide) field.val

end Grad.CircularHighWeak
