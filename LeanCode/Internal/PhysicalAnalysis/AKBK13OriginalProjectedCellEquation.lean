import AKBK8NativeForceMatrixCells

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
namespace Grad.ActualCartesianWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.ActualCartesianEquations Grad.SourceCollarFullSource Grad.BoundaryTrace Grad.SourceCollar

theorem originalRadialMeanFree_planar (field : ℝ × ℝ → ComplexEuclidean 3) (angles : ℝ × ℝ) :
    planarPartMap (cartesianRadialMeanFree field angles) =
      planarPartMap (field angles) -
        angularCoefficient (fun polar => polarRadialComponent polar (planarPartMap (field (polar,angles.2)))) 0 •
          polarRadialVector angles.1 := by
  unfold cartesianRadialMeanFree
  rw [map_sub,map_smul]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [planarPartMap,Grad.ActualCartesianEquations.planarPart,polarRadialComponent,polarRadialVector,physicalRadialVector]

/-- The genuine projected equation passes to every axial Fourier cell.
All full-field coefficient multiplication has already occurred. -/
theorem originalProjectedEquation_axialCell (first second : ℝ × ℝ → ComplexEuclidean 3)
    (firstContinuous : Continuous first) (secondContinuous : Continuous second)
    (equation : ∀ angles, cartesianRadialMeanFree first angles = cartesianRadialMeanFree second angles)
    (cell : ℤ) (angle : ℝ) :
    angularCoefficient (fun axial => planarPartMap (first (angle,axial))) cell -
      angularCoefficient (fun polar => polarRadialComponent polar
        (angularCoefficient (fun axial => planarPartMap (first (polar,axial))) cell)) 0 • polarRadialVector angle =
    angularCoefficient (fun axial => planarPartMap (second (angle,axial))) cell -
      angularCoefficient (fun polar => polarRadialComponent polar
        (angularCoefficient (fun axial => planarPartMap (second (polar,axial))) cell)) 0 • polarRadialVector angle := by
  have firstSwap := originalRadialProjection_axialCell (fun angles => planarPartMap (first angles))
    (planarPartMap.continuous.comp firstContinuous) cell angle
  have secondSwap := originalRadialProjection_axialCell (fun angles => planarPartMap (second angles))
    (planarPartMap.continuous.comp secondContinuous) cell angle
  rw [← firstSwap,← secondSwap]
  apply congrArg (fun function : ℝ → ComplexEuclidean 2 => angularCoefficient function cell)
  funext axial
  exact (originalRadialMeanFree_planar first (angle,axial)).symm.trans
    ((congrArg planarPartMap (equation (angle,axial))).trans (originalRadialMeanFree_planar second (angle,axial)))

end Grad.ActualCartesianWeakEquations
