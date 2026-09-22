import AXF25CartesianProjector

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.QuotientProjection
open Grad.AxisSplit Grad.AxisJet Grad.AxisCore

variable {parameters : PhaseParameters}

theorem traceZero_spinCore_zero (sign : ℂ) (field : ACore parameters 2)
    (zero : traceZero field = 0) : traceZero (spinCore sign field) = 0 := by
  apply Subtype.ext
  funext cell
  have zeroAt := congrFun (congrArg Subtype.val zero) cell
  change originValue (field.val cell) = 0 at zeroAt
  change originValue (valueMapJet (spinValue sign) (field.val cell)) = 0
  change (valueMapJet (spinValue sign) (field.val cell)).value originPoint = 0
  rw [valueMapJet_value]
  change spinValue sign (originValue (field.val cell)) = 0
  rw [zeroAt, map_zero]

theorem traceZero_vectorTuple_zero (first second : ACore parameters 1)
    (firstZero : traceZero first = 0) (secondZero : traceZero second = 0) :
    traceZero (vectorTuple first second) = 0 := by
  apply Subtype.ext
  funext cell
  have firstAt := congrFun (congrArg Subtype.val firstZero) cell
  have secondAt := congrFun (congrArg Subtype.val secondZero) cell
  change (first.val cell).value originPoint = 0 at firstAt
  change (second.val cell).value originPoint = 0 at secondAt
  change ((vectorTuple first second).val cell).value originPoint = 0
  rw [vectorTuple_value, firstAt, secondAt]
  apply PiLp.ext
  intro index
  fin_cases index <;> rfl

theorem traceZero_cartesianSource_iff (source : SmoothQuotient parameters) :
    traceZero (cartesianSourceVector source) = 0 ↔
      traceZero (source 0) = 0 ∧ traceZero (source 1) = 0 := by
  constructor
  · intro zero
    have plus := traceZero_spinCore_zero 1 _ zero
    have minus := traceZero_spinCore_zero (-1) _ zero
    rw [spinCore_cartesianSource_plus] at plus
    rw [spinCore_cartesianSource_minus] at minus
    exact ⟨plus, minus⟩
  · rintro ⟨first, second⟩
    apply traceZero_vectorTuple_zero
    · change traceZero ((1 / 2 : ℂ) • (source 0 + source 1)) = 0
      rw [map_smul, map_add, first, second, add_zero, smul_zero]
    · change traceZero ((-Complex.I / 2) • (source 0 - source 1)) = 0
      rw [map_smul, map_sub, first, second, sub_zero, smul_zero]

theorem modeProjection_zero_iff_radial (source : SmoothQuotient parameters) :
    modeProjection parameters source = 0 ↔
      radialSourceCore parameters (cartesianSourceVector source) = 0 := by
  constructor
  · intro zero
    rw [← cartesianSourceVector_modeProjection, zero]
    exact cartesianSourceLinear.map_zero
  · intro zero
    have first := radialSource_cartesian_plus source
    rw [zero, map_zero] at first
    rw [modeProjection_apply, ← first, map_zero]
    funext index
    fin_cases index <;> rfl

theorem affineTrace_zero_iff_curl (source : SmoothQuotient parameters) :
    affineTrace parameters source = 0 ↔
      cartesianCurlTrace (cartesianSourceVector source) = 0 := by
  rw [affineTrace_cartesian_curl]
  exact smul_eq_zero.trans (or_iff_right (by norm_num))

/-- Literal BS4: full Cartesian radial projection, value and curl at the
axis; mean-free g and h; only h has the extra first-derivative condition. -/
def CartesianIsFlat (source : SmoothQuotient parameters) : Prop :=
  radialSourceCore parameters (cartesianSourceVector source) = 0 ∧
    traceZero (cartesianSourceVector source) = 0 ∧
    cartesianCurlTrace (cartesianSourceVector source) = 0 ∧
    angularCore parameters 0 (source 2) = 0 ∧
    angularCore parameters 0 (source 3) = 0 ∧
    ∀ direction, traceFirst direction (source 3) = 0

theorem isFlat_iff_cartesian (source : SmoothQuotient parameters) :
    IsFlat source ↔ CartesianIsFlat source := by
  unfold IsFlat IsConstrained CartesianIsFlat
  rw [traceZero_cartesianSource_iff, ← modeProjection_zero_iff_radial,
    ← affineTrace_zero_iff_curl]
  tauto

theorem flatSourceProjection_cartesian_range (source : SmoothQuotient parameters) :
    source ∈ LinearMap.range (flatSourceProjection (parameters := parameters)) ↔
      CartesianIsFlat source :=
  (flatSourceProjection_range source).trans (isFlat_iff_cartesian source)

theorem flatSourceProjection_cartesian_flat (source : SmoothQuotient parameters) :
    CartesianIsFlat (flatSourceProjection source) :=
  (isFlat_iff_cartesian _).mp (flatSourceProjection_flat source)

end Grad.FlatSourceProjection
