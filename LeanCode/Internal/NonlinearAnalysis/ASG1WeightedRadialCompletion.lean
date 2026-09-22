import SBT13EndpointMaps
import GC20WeakGraph

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Genuine infinitely smooth radial functions, with their genuine first
radial derivative. This core carries no independent endpoint coordinate. -/
def SmoothRadialCore (dimension : ℕ) : Submodule ℝ (collarSmoothGraph (ComplexEuclidean dimension)) where
  carrier := {core | ContDiff ℝ ∞ core.val.1}
  zero_mem' := by
    change ContDiff ℝ ∞ (fun _ : ℝ => (0 : ComplexEuclidean dimension))
    exact contDiff_const
  add_mem' := by
    intro first second firstLaw secondLaw
    change ContDiff ℝ ∞ first.val.1 at firstLaw
    change ContDiff ℝ ∞ second.val.1 at secondLaw
    change ContDiff ℝ ∞ (fun radius => first.val.1 radius + second.val.1 radius)
    exact firstLaw.add secondLaw
  smul_mem' := by
    intro scalar core smooth
    change ContDiff ℝ ∞ core.val.1 at smooth
    change ContDiff ℝ ∞ (fun radius => scalar • core.val.1 radius)
    exact smooth.const_smul scalar

abbrev WeightedRadialAmbient (dimension : ℕ) (lower : ℝ) :=
  PiLp 2 (fun _ : Fin 2 => RadialL2 dimension lower)

/-- AH10's two literal r dr graph coordinates. The square-root storage is
exactly the already accepted radial L2 convention. -/
def weightedRadialCore (dimension : ℕ) (lower : ℝ) :
    SmoothRadialCore dimension →ₗ[ℝ] WeightedRadialAmbient dimension lower where
  toFun core := WithLp.toLp 2
    ![weightedCurveLinear dimension lower core.val.val.1,
      weightedCurveLinear dimension lower core.val.val.2]
  map_add' first second := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [map_add]
  map_smul' scalar core := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [map_smul]

/-- Completion in the actual value-plus-conjugated-derivative weighted norm.
Faithfulness and traces are proved from this graph, not stored independently. -/
def WeightedRadialH1 (dimension : ℕ) (lower : ℝ) :
    Submodule ℝ (WeightedRadialAmbient dimension lower) :=
  (LinearMap.range (weightedRadialCore dimension lower)).topologicalClosure

instance weightedRadialH1_complete (dimension : ℕ) (lower : ℝ) :
    CompleteSpace (WeightedRadialH1 dimension lower) :=
  (LinearMap.range (weightedRadialCore dimension lower)).isClosed_topologicalClosure.completeSpace_coe

def weightedRadialCoreInto (dimension : ℕ) (lower : ℝ) :
    SmoothRadialCore dimension →ₗ[ℝ] WeightedRadialH1 dimension lower :=
  (weightedRadialCore dimension lower).codRestrict (WeightedRadialH1 dimension lower)
    (fun core => Submodule.le_topologicalClosure _ ⟨core, rfl⟩)

theorem weightedRadialCoreInto_denseRange (dimension : ℕ) (lower : ℝ) :
    DenseRange (weightedRadialCoreInto dimension lower) := by
  let source := LinearMap.range (weightedRadialCore dimension lower)
  have inclusionDense : DenseRange (Set.inclusion (Submodule.le_topologicalClosure source)) :=
    (denseRange_inclusion_iff _).2 (fun _ member => member)
  apply inclusionDense.mono
  rintro _ ⟨point, rfl⟩
  rcases point.property with ⟨core, equality⟩
  exact ⟨core, Subtype.ext equality⟩

def weightedRadialCoordinate (dimension : ℕ) (lower : ℝ) (coordinate : Fin 2) :
    WeightedRadialH1 dimension lower →L[ℝ] RadialL2 dimension lower :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => RadialL2 dimension lower) coordinate).comp
    (WeightedRadialH1 dimension lower).subtypeL

theorem weightedRadialCoordinate_core_zero (dimension : ℕ) (lower : ℝ)
    (core : SmoothRadialCore dimension) :
    weightedRadialCoordinate dimension lower 0 (weightedRadialCoreInto dimension lower core) =
      weightedCurveLinear dimension lower core.val.val.1 := rfl

theorem weightedRadialCoordinate_core_one (dimension : ℕ) (lower : ℝ)
    (core : SmoothRadialCore dimension) :
    weightedRadialCoordinate dimension lower 1 (weightedRadialCoreInto dimension lower core) =
      weightedCurveLinear dimension lower core.val.val.2 := rfl

theorem weightedRadialH1_norm_sq (dimension : ℕ) (lower : ℝ)
    (field : WeightedRadialH1 dimension lower) :
    ‖field‖ ^ 2 = ‖weightedRadialCoordinate dimension lower 0 field‖ ^ 2 +
      ‖weightedRadialCoordinate dimension lower 1 field‖ ^ 2 := by
  change ‖field.val‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
  rfl

/-- Literal r dr norm on every genuine smooth radial core field. -/
theorem weightedRadialCore_norm_sq (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (core : SmoothRadialCore dimension) :
    ‖weightedRadialCoreInto dimension lower core‖ ^ 2 =
      ∫ radius in lower..1, radius *
        (‖core.val.val.1 radius‖ ^ 2 + ‖core.val.val.2 radius‖ ^ 2) := by
  rw [weightedRadialH1_norm_sq, weightedRadialCoordinate_core_zero, weightedRadialCoordinate_core_one]
  change ‖radialToLp lower core.val.val.1 core.val.val.1.continuous‖ ^ 2 +
      ‖radialToLp lower core.val.val.2 core.val.val.2.continuous‖ ^ 2 = _
  rw [radialToLp_norm_sq lower positive.le bounded, radialToLp_norm_sq lower positive.le bounded]
  rw [← intervalIntegral.integral_add]
  · apply intervalIntegral.integral_congr
    intro radius _
    ring
  · exact (continuous_id.mul (core.val.val.1.continuous.norm.pow 2)).intervalIntegrable lower 1
  · exact (continuous_id.mul (core.val.val.2.continuous.norm.pow 2)).intervalIntegrable lower 1

end Grad.AnnularSourceGraph
