import AQR1ActualSecondRadialEquation

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval
namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.AnnularSourceGraph Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

def actualRadialSlope (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (parameter : ℝ) (source : highDiskL2) : C(ℝ, ComplexEuclidean 1) :=
  (weakInverse_closedCollar_derivative lower positive bounded mode parameter source).choose

theorem actualRadialSlope_ae (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (parameter : ℝ) (source : highDiskL2) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), actualRadialSlope lower positive bounded mode parameter source radius =
      diskRadialSlope lower positive bounded.le mode (highRobinWeakInverse parameter source).val radius :=
  (weakInverse_closedCollar_derivative lower positive bounded mode parameter source).choose_spec.1

theorem actualRadialSlope_eq_deriv (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (parameter : ℝ) (source : highDiskL2) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    derivWithin (actualRadialValue lower positive bounded mode parameter source) (Icc lower 1) radius =
      actualRadialSlope lower positive bounded mode parameter source radius :=
  ((weakInverse_closedCollar_derivative lower positive bounded mode parameter source).choose_spec.2 radius inside).derivWithin
    (uniqueDiffOn_Icc bounded radius inside)

private theorem radialToLp_of_ordinary (lower : ℝ) (curve : C(ℝ, ComplexEuclidean 1))
    (ordinary : CollarL2 (ComplexEuclidean 1) lower)
    (same : ∀ᵐ radius ∂volume.restrict (Icc lower 1), curve radius = ordinary radius) :
    radialToLp lower curve curve.continuous = radialSqrtMap 1 lower ordinary := by
  apply Lp.ext
  filter_upwards [radialToLp_ae lower curve curve.continuous, radialSqrtMap_ae 1 lower ordinary, same]
    with radius stored mapped literal
  rw [stored, mapped, literal]

theorem actualRadialValue_stored (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (parameter : ℝ) (source : highDiskL2) :
    radialToLp lower (actualRadialValue lower positive bounded mode parameter source)
      (actualRadialValue lower positive bounded mode parameter source).continuous =
      diskL2Radial lower positive bounded.le mode (highDiskBulk (highRobinWeakInverse parameter source)) := by
  have same := radialToLp_of_ordinary lower (actualRadialValue lower positive bounded mode parameter source)
    (diskRadialValue lower positive bounded.le mode (highRobinWeakInverse parameter source).val)
    (diskRadialValueSection_ae lower positive bounded mode _)
  exact same.trans ((weightedRadialCoordinate_eq_sqrt 1 lower positive bounded.le 0
    (diskRadial lower positive bounded.le mode (highRobinWeakInverse parameter source).val)).symm.trans
      (diskRadial_bulk lower positive bounded.le mode _))

theorem actualRadialSlope_stored (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (parameter : ℝ) (source : highDiskL2) :
    radialToLp lower (actualRadialSlope lower positive bounded mode parameter source)
      (actualRadialSlope lower positive bounded mode parameter source).continuous =
      weightedRadialCoordinate 1 lower 1
        (diskRadial lower positive bounded.le mode (highRobinWeakInverse parameter source).val) :=
  (radialToLp_of_ordinary lower (actualRadialSlope lower positive bounded mode parameter source)
    (diskRadialSlope lower positive bounded.le mode (highRobinWeakInverse parameter source).val)
    (actualRadialSlope_ae lower positive bounded mode parameter source)).trans
      (weightedRadialCoordinate_eq_sqrt 1 lower positive bounded.le 1
        (diskRadial lower positive bounded.le mode (highRobinWeakInverse parameter source).val)).symm

theorem actualRadialValue_energy (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (parameter : ℝ) (source : highDiskL2) :
    (∫ radius in lower..1, radius * ‖actualRadialValue lower positive bounded mode parameter source radius‖ ^ 2) =
      ‖diskL2Radial lower positive bounded.le mode (highDiskBulk (highRobinWeakInverse parameter source))‖ ^ 2 :=
  (radialToLp_norm_sq lower positive.le bounded.le _
    (actualRadialValue lower positive bounded mode parameter source).continuous).symm.trans
      (congrArg (fun field : RadialL2 1 lower => ‖field‖ ^ 2) (actualRadialValue_stored lower positive bounded mode parameter source))

theorem actualRadialSlope_energy (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : ℤ) (parameter : ℝ) (source : highDiskL2) :
    (∫ radius in lower..1, radius * ‖actualRadialSlope lower positive bounded mode parameter source radius‖ ^ 2) =
      ‖weightedRadialCoordinate 1 lower 1
        (diskRadial lower positive bounded.le mode (highRobinWeakInverse parameter source).val)‖ ^ 2 :=
  (radialToLp_norm_sq lower positive.le bounded.le _
    (actualRadialSlope lower positive bounded mode parameter source).continuous).symm.trans
      (congrArg (fun field : RadialL2 1 lower => ‖field‖ ^ 2) (actualRadialSlope_stored lower positive bounded mode parameter source))

end Grad.CircularHighRegularity
