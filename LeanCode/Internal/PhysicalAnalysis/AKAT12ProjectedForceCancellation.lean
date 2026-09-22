import AKAT11SameCartesianForceExpression

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set
namespace Grad.ActualCartesianEquations
open Grad.ClosedJets Grad.CartesianState Grad.ActualSmoothPhysicalField Grad.SourceCollarFullSource
open Grad.SourceCollarCoefficients Grad.BoundaryTrace

theorem removePolarMean_coordinate (field : ℝ × ℝ → ComplexEuclidean 1) (continuousField : Continuous field)
    (angles : ℝ × ℝ) :
    removePolarMean field angles 0 = removePolarMean (fun query => field query 0) angles := by
  unfold removePolarMean
  rw [PiLp.sub_apply]
  change field angles 0-angularCoefficient (fun polar => field (polar,angles.2)) 0 0 = _
  have sectionContinuous : Continuous (fun polar => field (polar,angles.2)) :=
    continuousField.comp (continuous_id.prodMk continuous_const)
  rw [angularCoefficient_component (fun polar => field (polar,angles.2)) sectionContinuous 0 0]

/-- Exact force cancellation for arbitrary continuous SAME raw j and source.
The original Cartesian radial projection removes the compensating mean,
while every tangential mode is retained. -/
theorem cartesianProjectedForce_cancellation (j force : ℝ × ℝ → ComplexEuclidean 1)
    (tangential : ℝ × ℝ → ℂ) (continuousJ : Continuous j) (continuousForce : Continuous force)
    (angles : ℝ × ℝ) :
    cartesianRadialMeanFree (fun query => cartesianCovariantValue query.1
      (WithLp.toLp 2 ![removePolarMean (fun point => j point+force point) query 0-j query 0,tangential query,0])) angles =
    cartesianCovariantValue angles.1 (WithLp.toLp 2 ![
      removePolarMean (fun query => force query 0) angles,tangential angles,0]) := by
  have sourceContinuous : Continuous (fun query => force query 0) := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).continuous.comp continuousForce
  have cancelled := congrFun (removePolarMean_radial_force (fun query => j query 0) (fun query => force query 0) sourceContinuous) angles
  simp_rw [removePolarMean_coordinate (fun point => j point+force point) (continuousJ.add continuousForce)]
  rw [cartesianRadialMeanFree_polar]
  congr 1
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · change removePolarMean (fun query => removePolarMean (fun point => j point 0+force point 0) query-j query 0) angles = _
    exact cancelled
  · rfl
  · rfl

end Grad.ActualCartesianEquations
