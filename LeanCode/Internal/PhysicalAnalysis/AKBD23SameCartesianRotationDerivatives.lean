import AKBD22ActualPolarRotationDifferentials

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter
open scoped Topology ContDiff
namespace Grad.ActualDeterminantEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.ActualSmoothPhysicalField
open Grad.ActualCartesianEquations Grad.ActualCartesianDescent Grad.PhysicalFamily Grad.BoundaryTrace

variable {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower < 1)
    (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ)

include inside

theorem sameCartesianRotation_radial :
    fderiv ℝ (curves.cartesianCovariant.cartesianField bounded) (polarPlane (radius,polar),axial) (radialDirection polar,0) =
      cartesianCovariantValue polar (vectorDirectionalField curves bounded (1,0,0) (radius,polar,axial)) := by
  have initial := (fullVectorField_hasFDerivAt curves bounded (radius,polar,axial) inside).comp_hasDerivAt radius
    ((hasDerivAt_id radius).prodMk ((hasDerivAt_const radius polar).prodMk (hasDerivAt_const radius axial)))
  have rotated := ((polarRotationCLM polar).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt radius initial
  change HasDerivAt (fun location => polarRotationCLM polar (curves.fullField bounded (location,polar,axial)))
    (polarRotationCLM polar (vectorDirectionalField curves bounded (1,0,0) (radius,polar,axial))) radius at rotated
  simp_rw [polarRotationCLM_apply] at rotated
  have actual : HasDerivAt (fun location => curves.cartesianCovariant.fullField bounded (location,polar,axial))
      (cartesianCovariantValue polar (vectorDirectionalField curves bounded (1,0,0) (radius,polar,axial))) radius := by
    apply rotated.congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds inside.1 inside.2] with location member
    exact curves.fullField_cartesianCovariant bounded location ⟨member.1.le,member.2.le⟩ (polar,axial)
  exact (cartesianPhysicalField_radial_hasDerivAt (curves.cartesianCovariant.fullField bounded) lower 1
    ((curves.cartesianCovariant.fullField_smooth bounded).mono (fun _ member => ⟨⟨member.1.1.le,member.1.2.le⟩,mem_univ _⟩))
    (fun r z => curves.cartesianCovariant.fullField_angular_periodic bounded r z)
    radius (positive.trans inside.1) inside polar axial).unique actual

theorem sameCartesianRotation_angular :
    fderiv ℝ (curves.cartesianCovariant.cartesianField bounded) (polarPlane (radius,polar),axial) (radius • planeQuarterTurn (radialDirection polar),0) =
      cartesianCovariantValue polar (vectorDirectionalField curves bounded (0,1,0) (radius,polar,axial) +
        polarQuarter (curves.fullField bounded (radius,polar,axial))) := by
  have initial := (fullVectorField_hasFDerivAt curves bounded (radius,polar,axial) inside).comp_hasDerivAt polar
    ((hasDerivAt_const polar radius).prodMk ((hasDerivAt_id polar).prodMk (hasDerivAt_const polar axial)))
  have rotated := cartesianCovariantValue_hasDerivAt _ _ polar initial
  have actual : HasDerivAt (fun angle => curves.cartesianCovariant.fullField bounded (radius,angle,axial))
      (cartesianCovariantValue polar (vectorDirectionalField curves bounded (0,1,0) (radius,polar,axial) +
        polarQuarter (curves.fullField bounded (radius,polar,axial)))) polar := by
    apply rotated.congr_of_eventuallyEq
    exact Eventually.of_forall (fun angle => curves.fullField_cartesianCovariant bounded radius ⟨inside.1.le,inside.2.le⟩ (angle,axial))
  exact (cartesianPhysicalField_angular_hasDerivAt (curves.cartesianCovariant.fullField bounded) lower 1
    ((curves.cartesianCovariant.fullField_smooth bounded).mono (fun _ member => ⟨⟨member.1.1.le,member.1.2.le⟩,mem_univ _⟩))
    (fun r z => curves.cartesianCovariant.fullField_angular_periodic bounded r z)
    radius (positive.trans inside.1) inside polar axial).unique actual

theorem sameCartesianRotation_axial :
    fderiv ℝ (curves.cartesianCovariant.cartesianField bounded) (polarPlane (radius,polar),axial) (0,1) =
      cartesianCovariantValue polar (vectorDirectionalField curves bounded (0,0,1) (radius,polar,axial)) := by
  have initial := (fullVectorField_hasFDerivAt curves bounded (radius,polar,axial) inside).comp_hasDerivAt axial
    ((hasDerivAt_const axial radius).prodMk ((hasDerivAt_const axial polar).prodMk (hasDerivAt_id axial)))
  have rotated := ((polarRotationCLM polar).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt axial initial
  change HasDerivAt (fun angle => polarRotationCLM polar (curves.fullField bounded (radius,polar,angle)))
    (polarRotationCLM polar (vectorDirectionalField curves bounded (0,0,1) (radius,polar,axial))) axial at rotated
  simp_rw [polarRotationCLM_apply] at rotated
  have actual : HasDerivAt (fun angle => curves.cartesianCovariant.fullField bounded (radius,polar,angle))
      (cartesianCovariantValue polar (vectorDirectionalField curves bounded (0,0,1) (radius,polar,axial))) axial := by
    apply rotated.congr_of_eventuallyEq
    exact Eventually.of_forall (fun angle => curves.fullField_cartesianCovariant bounded radius ⟨inside.1.le,inside.2.le⟩ (polar,angle))
  exact (cartesianPhysicalField_axial_hasDerivAt (curves.cartesianCovariant.fullField bounded) lower 1
    ((curves.cartesianCovariant.fullField_smooth bounded).mono (fun _ member => ⟨⟨member.1.1.le,member.1.2.le⟩,mem_univ _⟩))
    (fun r z => curves.cartesianCovariant.fullField_angular_periodic bounded r z)
    radius (positive.trans inside.1) inside polar axial).unique actual

end Grad.ActualDeterminantEquations
