import ANR29RadialPrimitiveDerivative

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.WeightedTrace

def radialInverseRadiusCurve (lower : ℝ) (positive : 0 < lower) : C(ℝ, ℝ) :=
  ⟨fun radius => (max lower radius)⁻¹,
    (continuous_const.max continuous_id).inv₀
      (fun radius => (positive.trans_le (le_max_left lower radius)).ne')⟩

theorem radialFlux_decode (dimension : ℕ) (lower : ℝ) (positive : 0 < lower)
    (flux : C(ℝ, ComplexEuclidean dimension)) (derivative : CollarL2 (ComplexEuclidean dimension) lower)
    (actual : ∀ᵐ radius ∂volume.restrict (Icc lower 1), flux radius = radius • derivative radius) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), (max lower radius)⁻¹ • flux radius = derivative radius := by
  filter_upwards [actual, ae_restrict_mem measurableSet_Icc] with radius literal inside
  rw [literal, max_eq_right inside.1, smul_smul, inv_mul_cancel₀ (positive.trans_le inside.1).ne', one_smul]

def diskRadialValueSection (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (field : diskGrade) : RadialContinuousSection 1 lower :=
  weightedRadialSection 1 lower positive bounded (diskRadial lower positive bounded.le mode field)

theorem diskRadialValueSection_ae (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (field : diskGrade) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      radialSectionExtension 1 lower bounded.le (diskRadialValueSection lower positive bounded mode field) radius =
        diskRadialValue lower positive bounded.le mode field radius :=
  weightedRadialSection_ae 1 lower positive bounded _

theorem diskRadialValueSection_primitive (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (field : diskGrade) (radius : Icc lower (1 : ℝ)) :
    diskRadialValueSection lower positive bounded mode field radius =
      diskRadialValueSection lower positive bounded mode field ⟨lower, le_rfl, bounded.le⟩ +
        ∫ point in lower..radius.val, diskRadialSlope lower positive bounded.le mode field point := by
  have primitive := weightedRadialSection_primitive 1 lower positive bounded
    (diskRadial lower positive bounded.le mode field) radius
  have endpoint := weightedRadialSection_endpoint 1 lower positive bounded 0
    (diskRadial lower positive bounded.le mode field)
  exact primitive.trans (congrArg (fun value : ComplexEuclidean 1 => value +
    ∫ point in lower..radius.val, diskRadialSlope lower positive bounded.le mode field point) endpoint.symm)

/-- Every actual L2 source gives a continuously differentiable radial
representative on each positive closed collar. Its derivative is the same
weak slope, with both endpoint limits, obtained from the proved flux law. -/
theorem weakInverse_closedCollar_derivative (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (parameter : ℝ) (source : highDiskL2) :
    ∃ derivative : C(ℝ, ComplexEuclidean 1),
      (∀ᵐ radius ∂volume.restrict (Icc lower 1), derivative radius =
        diskRadialSlope lower positive bounded.le mode (highRobinWeakInverse parameter source).val radius) ∧
      ∀ radius ∈ Icc lower 1,
        HasDerivWithinAt (radialSectionExtension 1 lower bounded.le
          (diskRadialValueSection lower positive bounded mode (highRobinWeakInverse parameter source).val))
          (derivative radius) (Icc lower 1) radius := by
  have existence := weakInverse_radial_flux_representative lower positive bounded mode parameter source
  obtain ⟨flux, actual, _primitive⟩ := existence
  let extension := radialSectionExtension 1 lower bounded.le flux
  let inverse := radialInverseRadiusCurve lower positive
  let derivative : C(ℝ, ComplexEuclidean 1) :=
    ⟨fun radius => inverse radius • extension radius, inverse.continuous.smul extension.continuous⟩
  have same : ∀ᵐ radius ∂volume.restrict (Icc lower 1), derivative radius =
      diskRadialSlope lower positive bounded.le mode (highRobinWeakInverse parameter source).val radius :=
    radialFlux_decode 1 lower positive extension
      (diskRadialSlope lower positive bounded.le mode (highRobinWeakInverse parameter source).val) actual
  refine ⟨derivative, same, ?_⟩
  intro radius inside
  exact radialSection_hasDerivWithinAt 1 lower bounded.le
    (diskRadialValueSection lower positive bounded mode (highRobinWeakInverse parameter source).val)
    (diskRadialSlope lower positive bounded.le mode (highRobinWeakInverse parameter source).val)
    derivative (Filter.EventuallyEq.symm same)
    (diskRadialValueSection_primitive lower positive bounded mode (highRobinWeakInverse parameter source).val)
    radius inside

end Grad.CircularHighRegularity
