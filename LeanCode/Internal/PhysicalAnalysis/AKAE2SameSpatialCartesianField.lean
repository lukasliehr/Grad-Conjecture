import AKAE1GenuineCartesianPolarDescent

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter
open scoped Topology ContDiff
namespace Grad.ActualCartesianDescent
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.BoundaryLift Grad.SourceCollarDivision
open Grad.DiskExtension.Operator Grad.ActualSmoothPhysicalField Grad.AnnularClosedJointRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The definite Cartesian realization uses the accepted spatial-plane
complex coordinate. The auxiliary axial variable is unchanged. -/
def cartesianPhysicalField (field : ℝ × (ℝ × ℝ) → E) (point : SpatialPlane × ℝ) : E :=
  cartesianFromPolar field (signedComplexCoordinate 1 point.1,point.2)

 theorem signedComplexCoordinate_polar (radius polar : ℝ) :
    signedComplexCoordinate 1 (polarPlane (radius,polar)) =
      (radius : ℂ)*((Real.cos polar : ℂ)+(Real.sin polar : ℂ)*Complex.I) := by
  simp [signedComplexCoordinate,polarPlane,Grad.BoundaryTrace.collarPlane,Complex.ofReal_mul]
  ring

 theorem polarPlane_originalParametrization (radius polar : ℝ) :
    spatialPlaneOfPair (polarCoord.symm (radius,polar)) = polarPlane (radius,polar) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [spatialPlaneOfPair,polarPlane,Grad.BoundaryTrace.collarPlane,polarCoord]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem cartesianPhysicalField_at_polar (field : ℝ × (ℝ × ℝ) → E)
    (periodic : ∀ radius axial,Function.Periodic (fun polar => field (radius,polar,axial)) (2*Real.pi))
    (radius : ℝ) (positive : 0 < radius) (polar axial : ℝ) :
    cartesianPhysicalField field (polarPlane (radius,polar),axial) = field (radius,polar,axial) := by
  rw [cartesianPhysicalField,signedComplexCoordinate_polar]
  exact cartesianFromPolar_at_polar field periodic radius positive polar axial

 theorem cartesianPhysicalField_smoothAt (field : ℝ × (ℝ × ℝ) → E) (lower upper : ℝ)
    (smooth : ContDiffOn ℝ ∞ field (Ioo lower upper ×ˢ (univ : Set (ℝ × ℝ))))
    (periodic : ∀ radius axial,Function.Periodic (fun polar => field (radius,polar,axial)) (2*Real.pi))
    (point : SpatialPlane × ℝ) (nonzero : point.1 ≠ 0) (inside : ‖point.1‖ ∈ Ioo lower upper) :
    ContDiffAt ℝ ∞ (cartesianPhysicalField field) point := by
  have coordinateNonzero : signedComplexCoordinate 1 point.1 ≠ 0 := by
    intro zero
    have same := congrArg norm zero
    rw [complexCoordinate_norm,norm_zero] at same
    exact nonzero (norm_eq_zero.mp same)
  have coordinateInside : ‖signedComplexCoordinate 1 point.1‖ ∈ Ioo lower upper := by
    rw [complexCoordinate_norm]
    exact inside
  exact (cartesianFromPolar_smoothAt field lower upper smooth periodic
    (signedComplexCoordinate 1 point.1,point.2) coordinateNonzero coordinateInside).comp point
      (((signedComplexCoordinate_smooth 1).contDiffAt.comp point contDiffAt_fst).prodMk contDiffAt_snd)

end Grad.ActualCartesianDescent

namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.DiskExtension.Operator
open Grad.ActualCartesianDescent Grad.AnnularClosedJointRegularity

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower < 1)

def SmoothLowPhysicalRow.cartesianField (point : SpatialPlane × ℝ) : ComplexEuclidean dimension :=
  cartesianPhysicalField (curves.fullField bounded) point

theorem SmoothLowPhysicalRow.cartesianField_polar (radius : ℝ) (radiusPositive : 0 < radius) (polar axial : ℝ) :
    curves.cartesianField bounded (spatialPlaneOfPair (polarCoord.symm (radius,polar)),axial) =
      curves.fullField bounded (radius,polar,axial) := by
  rw [polarPlane_originalParametrization]
  exact cartesianPhysicalField_at_polar (curves.fullField bounded)
    (fun radius axial => curves.fullField_angular_periodic bounded radius axial) radius radiusPositive polar axial

/-- The SAME complete reconstructed row is genuinely Cartesian smooth
through the angular seam on the punctured open annulus. -/
theorem SmoothLowPhysicalRow.cartesianField_smoothAt (point : SpatialPlane × ℝ)
    (inside : ‖point.1‖ ∈ Ioo lower 1) :
    ContDiffAt ℝ ∞ (curves.cartesianField bounded) point := by
  apply cartesianPhysicalField_smoothAt (curves.fullField bounded) lower 1
    ((curves.fullField_smooth bounded).mono (fun _ member => ⟨⟨member.1.1.le,member.1.2.le⟩,member.2⟩))
    (fun radius axial => curves.fullField_angular_periodic bounded radius axial) point _ inside
  exact (norm_pos_iff.mp (positive.trans inside.1))

end Grad.ActualSmoothPhysicalField
