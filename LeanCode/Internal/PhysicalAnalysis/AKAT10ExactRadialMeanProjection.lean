import AKAT9SameCartesianForceDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set
open scoped BigOperators
namespace Grad.ActualCartesianEquations
open Grad.ClosedJets Grad.CartesianState Grad.ActualSmoothPhysicalField
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients Grad.SourceCollar
open Grad.BoundaryTrace

/-- The literal punctured-circle formula for the Cartesian radial complement.
Only the radial mean is removed; the tangential mean is retained. -/
def cartesianRadialMeanFree (field : ℝ × ℝ → ComplexEuclidean 3) (angles : ℝ × ℝ) : ComplexEuclidean 3 :=
  planarPart (field angles) -
    angularCoefficient (fun polar => (Real.cos polar : ℂ)*field (polar,angles.2) 0 +
      (Real.sin polar : ℂ)*field (polar,angles.2) 1) 0 • WithLp.toLp 2 (physicalRadialVector angles.1)

theorem cartesianCovariantValue_radial (angle : ℝ) (polar : ComplexEuclidean 3) :
    (Real.cos angle : ℂ)*cartesianCovariantValue angle polar 0 +
      (Real.sin angle : ℂ)*cartesianCovariantValue angle polar 1 = polar 0 := by
  rw [cartesianCovariantValue_apply]
  have circle : (Real.sin angle : ℂ)^2+(Real.cos angle : ℂ)^2=1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq angle
  dsimp
  linear_combination polar 0 * circle

/-- Exact correspondence between the radial Cartesian projection and P on
just the first polar component. This is an identity, not a gauge assumption. -/
theorem cartesianRadialMeanFree_polar (field : ℝ × ℝ → ComplexEuclidean 3) (angles : ℝ × ℝ) :
    cartesianRadialMeanFree (fun query => cartesianCovariantValue query.1 (field query)) angles =
      cartesianCovariantValue angles.1 (WithLp.toLp 2 ![
        removePolarMean (fun query => field query 0) angles,field angles 1,0]) := by
  simp only [cartesianRadialMeanFree,cartesianCovariantValue_radial]
  rw [cartesianCovariantValue_apply,cartesianCovariantValue_apply]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [planarPart,removePolarMean,physicalRadialVector]
  all_goals ring

/-- The actual radial equation P(j+f) removes exactly j after the original
radial complement is applied; no extra mean condition on j is required. -/
theorem removePolarMean_radial_force (j f : ℝ × ℝ → ℂ)
    (continuousF : Continuous f) :
    removePolarMean (fun query => removePolarMean (fun point => j point+f point) query-j query) = removePolarMean f := by
  funext angles
  have reduced (query : ℝ × ℝ) :
      removePolarMean (fun point => j point+f point) query-j query =
        f query-angularCoefficient (fun polar => j (polar,query.2)+f (polar,query.2)) 0 := by
    unfold removePolarMean
    ring
  have fixed : (fun polar => removePolarMean (fun point => j point+f point) (polar,angles.2)-j (polar,angles.2)) =
      fun polar => f (polar,angles.2)-angularCoefficient (fun theta => j (theta,angles.2)+f (theta,angles.2)) 0 :=
    funext (fun polar => reduced (polar,angles.2))
  change (removePolarMean (fun point => j point+f point) angles-j angles) -
    angularCoefficient (fun polar => removePolarMean (fun point => j point+f point) (polar,angles.2)-j (polar,angles.2)) 0 =
    f angles-angularCoefficient (fun polar => f (polar,angles.2)) 0
  rw [reduced angles]
  have sectionContinuous : Continuous (fun polar : ℝ => f (polar,angles.2)) :=
    continuousF.comp (continuous_id.prodMk continuous_const)
  rw [fixed,angularCoefficient_sub_general (fun polar => f (polar,angles.2))
    (fun _ : ℝ => angularCoefficient (fun theta => j (theta,angles.2)+f (theta,angles.2)) 0)
    sectionContinuous continuous_const 0,angularCoefficient_constant,if_pos rfl]
  ring

end Grad.ActualCartesianEquations
