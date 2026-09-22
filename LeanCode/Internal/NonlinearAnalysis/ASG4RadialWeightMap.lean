import ASG3CompletedEndpoints
import MK1Construction

noncomputable section

set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.MatrixMultiplier

def radialSqrtCoefficient (dimension : ℕ) (radius : ℝ) :
    ComplexEuclidean dimension →L[ℂ] ComplexEuclidean dimension :=
  Real.sqrt radius • ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)

theorem radialSqrtCoefficient_measurable (dimension : ℕ) (lower : ℝ) :
    AEStronglyMeasurable (radialSqrtCoefficient dimension) (volume.restrict (Icc lower 1)) :=
  (Real.continuous_sqrt.smul continuous_const).aestronglyMeasurable

theorem radialSqrtCoefficient_bound (dimension : ℕ) (lower : ℝ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ‖radialSqrtCoefficient dimension radius‖ ≤ 1 := by
  filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
  calc
    _ ≤ ‖Real.sqrt radius‖ * ‖ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)‖ := norm_smul_le _ _
    _ ≤ Real.sqrt radius * 1 := by
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
      exact mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (Real.sqrt_nonneg _)
    _ ≤ 1 := by simpa only [mul_one, Real.sqrt_one] using Real.sqrt_le_sqrt inside.2

/-- Multiplication by sqrt(r) is precisely the accepted isometric storage
map from ordinary radial functions to the r dr coordinates. -/
def radialSqrtMap (dimension : ℕ) (lower : ℝ) :
    CollarL2 (ComplexEuclidean dimension) lower →L[ℂ] RadialL2 dimension lower :=
  matrixMultiplier (volume.restrict (Icc lower 1)) (radialSqrtCoefficient dimension) 1
    (radialSqrtCoefficient_measurable dimension lower) (radialSqrtCoefficient_bound dimension lower)

theorem radialSqrtMap_ae (dimension : ℕ) (lower : ℝ)
    (field : CollarL2 (ComplexEuclidean dimension) lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), radialSqrtMap dimension lower field radius =
      Real.sqrt radius • field radius := by
  filter_upwards [matrixMultiplier_apply_ae (volume.restrict (Icc lower 1))
    (radialSqrtCoefficient dimension) 1 (radialSqrtCoefficient_measurable dimension lower)
    (radialSqrtCoefficient_bound dimension lower) field] with radius equality
  exact equality

theorem radialSqrtMap_core (dimension : ℕ) (lower : ℝ)
    (curve : C(ℝ, ComplexEuclidean dimension)) :
    radialSqrtMap dimension lower (collarContinuousL2 (ComplexEuclidean dimension) lower curve) =
      weightedCurveLinear dimension lower curve := by
  apply Lp.ext
  filter_upwards [radialSqrtMap_ae dimension lower (collarContinuousL2 (ComplexEuclidean dimension) lower curve),
    (collarContinuous_memLp (ComplexEuclidean dimension) lower curve).coeFn_toLp,
    radialToLp_ae lower curve curve.continuous] with radius mapped ordinary weighted
  change collarContinuousL2 (ComplexEuclidean dimension) lower curve radius = curve radius at ordinary
  change _ = radialToLp lower curve curve.continuous radius
  rw [mapped, ordinary, weighted]

theorem radialSqrtMap_injective (dimension : ℕ) (lower : ℝ) (positive : 0 < lower) :
    Function.Injective (radialSqrtMap dimension lower) := by
  intro first second same
  apply Lp.ext
  filter_upwards [radialSqrtMap_ae dimension lower first, radialSqrtMap_ae dimension lower second,
    ae_restrict_mem measurableSet_Icc] with radius firstLaw secondLaw inside
  have pointwise := congrArg (fun field : RadialL2 dimension lower => field radius) same
  rw [firstLaw, secondLaw] at pointwise
  have nonzero : Real.sqrt radius ≠ 0 := (Real.sqrt_pos.2 (positive.trans_le inside.1)).ne'
  have rescaled := congrArg (fun value : ComplexEuclidean dimension => (Real.sqrt radius)⁻¹ • value) pointwise
  simpa only [smul_smul, inv_mul_cancel₀ nonzero, one_smul] using rescaled

end Grad.AnnularSourceGraph
