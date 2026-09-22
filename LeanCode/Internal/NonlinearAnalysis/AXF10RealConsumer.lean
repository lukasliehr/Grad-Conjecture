import AXF9Reality

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.NonlinearQuotientBounds Grad.QuotientProjection Grad.AxisCore Grad.CompletedReality
open Grad.RealFixedRanges Grad.ChartAxisProjections Grad.ChartAxisSplit

variable {parameters : PhaseParameters}

theorem flatSourceProjection_real_mem (source : sourceSmoothRange parameters) :
    flatSourceProjection source.val ∈ sourceSmoothRange parameters := by
  apply (mem_sourceSmoothRange parameters _).mpr
  refine ⟨quotientProjection_fixes parameters _ (flatSourceProjection_constrained source.val), ?_⟩
  rw [flatSourceProjection_conjugate, ((mem_sourceSmoothRange parameters source.val).mp source.property).2]

def realFlatSourceProjection : sourceSmoothRange parameters →ₗ[ℝ] sourceSmoothRange parameters where
  toFun source := ⟨flatSourceProjection source.val, flatSourceProjection_real_mem source⟩
  map_add' first second := Subtype.ext
    ((flatSourceProjection (parameters := parameters)).map_add first.val second.val)
  map_smul' scalar source := Subtype.ext
    (((flatSourceProjection (parameters := parameters)).restrictScalars ℝ).map_smul scalar source.val)

theorem source_isFlat_iff_kernel (cellLength : ℝ) (positive : 0 < cellLength)
    (source : sourceSmoothRange parameters) :
    IsFlat source.val ↔ source ∈ LinearMap.ker (realExtraction parameters cellLength) := by
  rw [realSourceFlat_iff_jets cellLength positive]
  constructor
  · rintro ⟨_, first, second, gradient⟩ cell
    refine ⟨?_, ?_, ?_⟩
    · exact congrArg (fun family : AxisSmoothCore parameters 1 => family.val cell 0) first
    · exact congrArg (fun family : AxisSmoothCore parameters 1 => family.val cell 0) second
    · apply (scalarGradient_zero_iff (source.val 3) cell).mpr
      intro direction
      exact congrFun (congrArg Subtype.val (gradient direction)) cell
  · intro jets
    have fixed := ((mem_sourceSmoothRange parameters source.val).mp source.property).1
    have constrained : IsConstrained parameters source.val := by
      rw [← fixed]
      exact quotientProjection_constrained parameters source.val
    refine ⟨constrained, ?_, ?_, ?_⟩
    · apply Subtype.ext
      funext cell
      apply PiLp.ext
      intro component
      fin_cases component
      exact (jets cell).1
    · apply Subtype.ext
      funext cell
      apply PiLp.ext
      intro component
      fin_cases component
      exact (jets cell).2.1
    · intro direction
      apply Subtype.ext
      funext cell
      exact (scalarGradient_zero_iff (source.val 3) cell).mp (jets cell).2.2 direction

theorem realFlatSourceProjection_mem (cellLength : ℝ) (positive : 0 < cellLength)
    (source : sourceSmoothRange parameters) :
    realFlatSourceProjection source ∈ LinearMap.ker (realExtraction parameters cellLength) :=
  (source_isFlat_iff_kernel cellLength positive _).mp (flatSourceProjection_flat source.val)

theorem realFlatSourceProjection_fixes (cellLength : ℝ) (positive : 0 < cellLength)
    (source : sourceSmoothRange parameters) (flat : source ∈ LinearMap.ker (realExtraction parameters cellLength)) :
    realFlatSourceProjection source = source :=
  Subtype.ext (flatSourceProjection_fixes source.val ((source_isFlat_iff_kernel cellLength positive source).mpr flat))

theorem realFlatSourceProjection_idempotent (source : sourceSmoothRange parameters) :
    realFlatSourceProjection (realFlatSourceProjection source) = realFlatSourceProjection source :=
  Subtype.ext (flatSourceProjection_idempotent source.val)

theorem realFlatSourceProjection_range (cellLength : ℝ) (positive : 0 < cellLength) :
    LinearMap.range (realFlatSourceProjection (parameters := parameters)) =
      LinearMap.ker (realExtraction parameters cellLength) := by
  ext source
  constructor
  · rintro ⟨other, rfl⟩
    exact realFlatSourceProjection_mem cellLength positive other
  · intro flat
    exact ⟨source, realFlatSourceProjection_fixes cellLength positive source flat⟩

/-- Same grade on the original fourfold Hilbert completion, unlike AL29. -/
theorem realFlatSourceProjection_bound (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ source : sourceSmoothRange parameters,
      ‖sourceSmoothEmbedding parameters grade large (realFlatSourceProjection source)‖ ≤
        constant * ‖sourceSmoothEmbedding parameters grade large source‖ := by
  obtain ⟨constant, nonneg, bound⟩ := flatSourceProjection_bound parameters grade large
  exact ⟨constant, nonneg, fun source => bound source.val⟩

end Grad.FlatSourceProjection
