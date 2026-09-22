import AKBK14OriginalPlanarSourceCells

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
namespace Grad.ActualCartesianWeakEquations
open Grad.ClosedJets Grad.Constraints Grad.SourceCollar Grad.SourceCollarFullSource Grad.BoundaryTrace
open Grad.SourceCollarDivision Grad.PDEBootstrap

def originalCircleRadialProjection (field : ℝ → ComplexEuclidean 2) (angle : ℝ) : ComplexEuclidean 2 :=
  field angle - angularCoefficient (fun polar => polarRadialComponent polar (field polar)) 0 • polarRadialVector angle

theorem originalCircleRadialProjection_add (first second : ℝ → ComplexEuclidean 2)
    (firstContinuous : Continuous first) (secondContinuous : Continuous second) (angle : ℝ) :
    originalCircleRadialProjection (fun polar => first polar + second polar) angle =
      originalCircleRadialProjection first angle + originalCircleRadialProjection second angle := by
  have values : (fun polar => polarRadialComponent polar (first polar + second polar)) =
      fun polar => polarRadialComponent polar (first polar) + polarRadialComponent polar (second polar) := by
    funext polar
    simpa only [polarRadialComponentLinear_apply] using (polarRadialComponentLinear polar).map_add (first polar) (second polar)
  unfold originalCircleRadialProjection
  rw [values,angularCoefficient_add_general _ _ (polarRadialComponent_curve_continuous firstContinuous)
    (polarRadialComponent_curve_continuous secondContinuous),add_smul]
  abel
  simp only [add_assoc]

theorem originalCircleRadialProjection_sub (first second : ℝ → ComplexEuclidean 2)
    (firstContinuous : Continuous first) (secondContinuous : Continuous second) (angle : ℝ) :
    originalCircleRadialProjection (fun polar => first polar - second polar) angle =
      originalCircleRadialProjection first angle - originalCircleRadialProjection second angle := by
  have values : (fun polar => polarRadialComponent polar (first polar - second polar)) =
      fun polar => polarRadialComponent polar (first polar) - polarRadialComponent polar (second polar) := by
    funext polar
    simpa only [polarRadialComponentLinear_apply] using (polarRadialComponentLinear polar).map_sub (first polar) (second polar)
  unfold originalCircleRadialProjection
  rw [values,angularCoefficient_sub_general _ _ (polarRadialComponent_curve_continuous firstContinuous)
    (polarRadialComponent_curve_continuous secondContinuous),sub_smul]
  abel
  simp only [add_assoc]

/-- Moving the lower-order terms uses the literal original circle projection. -/
theorem originalCircleRadialProjection_move (divergence lower source : ℝ → ComplexEuclidean 2)
    (divergenceContinuous : Continuous divergence) (lowerContinuous : Continuous lower) (sourceContinuous : Continuous source)
    (angle : ℝ)
    (equation : originalCircleRadialProjection (fun polar => divergence polar - lower polar) angle =
      originalCircleRadialProjection source angle) :
    originalCircleRadialProjection (fun polar => source polar + lower polar) angle =
      originalCircleRadialProjection divergence angle := by
  rw [originalCircleRadialProjection_sub _ _ divergenceContinuous lowerContinuous] at equation
  rw [originalCircleRadialProjection_add _ _ sourceContinuous lowerContinuous]
  exact (sub_eq_iff_eq_add.mp equation).symm

/-- Punctured Cartesian continuity suffices for the exact polar projector. -/
theorem originalCircleRadialProjection_closed (field : Spatial → ComplexEuclidean 2)
    (continuousField : ContinuousOn field (openUnitDisk \ {(0 : Spatial)}))
    (radius : ℝ) (positive : 0 < radius) (inside : radius < 1) (bounded : |radius| ≤ 1) (angle : ℝ) :
    closedRadialReflectionValue (fun point : ClosedDisk => field point.val)
      (Grad.Constraints.polarClosedPoint radius bounded angle) =
      originalCircleRadialProjection (fun polar => field (polarPlane (radius,polar))) angle := by
  have same (polar : ℝ) : (Grad.Constraints.polarClosedPoint radius bounded polar).val = polarPlane (radius,polar) := by
    rw [Grad.Constraints.polarClosedPoint_coordinates]
    simp only [polarPlane,collarPlane,sub_sub_cancel]
  rw [puncturedRadialReflectionValue_polar field continuousField radius positive inside bounded angle]
  simp only [same,originalCircleRadialProjection]

end Grad.ActualCartesianWeakEquations
