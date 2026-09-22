import AKBD4SameCorrectedFluxProducts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter
open scoped Topology ContDiff
namespace Grad.ActualDeterminantEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.ActualSmoothPhysicalField

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1) (component : Fin dimension)

def scalarDirectionalField (direction : ℝ × (ℝ × ℝ)) (point : ℝ × (ℝ × ℝ)) : ℂ :=
  fderiv ℝ (fun query => curves.fullField bounded query component) point direction

theorem fullScalarField_smooth :
    ContDiffOn ℝ ∞ (fun query => curves.fullField bounded query component)
      (Ioo lower 1 ×ˢ (univ : Set (ℝ × ℝ))) :=
  ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin dimension => ℂ) component).restrictScalars ℝ).contDiff.comp_contDiffOn
    ((curves.fullField_smooth bounded).mono (fun _ member => ⟨⟨member.1.1.le,member.1.2.le⟩,mem_univ _⟩))

theorem scalarDirectionalField_smooth (direction : ℝ × (ℝ × ℝ)) :
    ContDiffOn ℝ ∞ (scalarDirectionalField curves bounded component direction)
      (Ioo lower 1 ×ˢ (univ : Set (ℝ × ℝ))) :=
  ((contDiffOn_infty_iff_fderiv_of_isOpen (isOpen_Ioo.prod isOpen_univ)).mp
    (fullScalarField_smooth curves bounded component)).2.clm_apply contDiffOn_const

theorem scalarDirectionalField_continuous_angles (direction : ℝ × (ℝ × ℝ))
    (radius : ℝ) (inside : radius ∈ Ioo lower 1) :
    Continuous (fun angles => scalarDirectionalField curves bounded component direction (radius,angles)) :=
  (scalarDirectionalField_smooth curves bounded component direction).continuousOn.comp_continuous
    (continuous_const.prodMk continuous_id) (fun _ => ⟨inside,mem_univ _⟩)

theorem fullScalarField_hasFDerivAt (point : ℝ × (ℝ × ℝ)) (inside : point.1 ∈ Ioo lower 1) :
    HasFDerivAt (fun query => curves.fullField bounded query component)
      (fderiv ℝ (fun query => curves.fullField bounded query component) point) point :=
  ((fullScalarField_smooth curves bounded component).contDiffAt
    ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨inside,mem_univ _⟩)).differentiableAt (by simp) |>.hasFDerivAt

theorem scalarRadial_hasDerivAt (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ) :
    HasDerivAt (fun value => curves.fullField bounded (value,polar,axial) component)
      (scalarDirectionalField curves bounded component (1,0,0) (radius,polar,axial)) radius := by
  exact (fullScalarField_hasFDerivAt curves bounded component (radius,polar,axial) inside).comp_hasDerivAt radius
    ((hasDerivAt_id radius).prodMk ((hasDerivAt_const radius polar).prodMk (hasDerivAt_const radius axial)))

theorem scalarPolar_hasDerivAt (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ) :
    HasDerivAt (fun value => curves.fullField bounded (radius,value,axial) component)
      (scalarDirectionalField curves bounded component (0,1,0) (radius,polar,axial)) polar := by
  exact (fullScalarField_hasFDerivAt curves bounded component (radius,polar,axial) inside).comp_hasDerivAt polar
    ((hasDerivAt_const polar radius).prodMk ((hasDerivAt_id polar).prodMk (hasDerivAt_const polar axial)))

theorem scalarAxial_hasDerivAt (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ) :
    HasDerivAt (fun value => curves.fullField bounded (radius,polar,value) component)
      (scalarDirectionalField curves bounded component (0,0,1) (radius,polar,axial)) axial := by
  exact (fullScalarField_hasFDerivAt curves bounded component (radius,polar,axial) inside).comp_hasDerivAt axial
    ((hasDerivAt_const axial radius).prodMk ((hasDerivAt_const axial polar).prodMk (hasDerivAt_id axial)))

end Grad.ActualDeterminantEquations
