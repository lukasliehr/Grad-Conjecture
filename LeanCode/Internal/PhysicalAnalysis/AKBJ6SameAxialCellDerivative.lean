import AKBJ4SameXiCartesianCellDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
open scoped ContDiff Topology
namespace Grad.ActualScalarWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.BoundaryTrace Grad.SourceBoundaryTrace Grad.ActualCartesianDescent Grad.ActualSmoothPhysicalField
open Grad.PDEBootstrap Grad.ActualPuncturedFamily

/-- Genuine axial differentiation of a periodic Cartesian field is multiplication by its signed integer cell. -/
theorem originalCell_axialDerivative {dimension : ℕ} {domain : Set Spatial}
    (openDomain : IsOpen domain) (field : Spatial × ℝ → ComplexEuclidean dimension)
    (smooth : ContDiffOn ℝ ∞ field (domain ×ˢ (univ : Set ℝ)))
    (point : Spatial) (inside : point ∈ domain)
    (periodic : Function.Periodic (fun axial => field (point,axial)) (2*Real.pi)) (cell : ℤ) :
    angularCoefficient (fun axial => fderiv ℝ field (point,axial) (0,1)) cell =
      (Complex.I * (cell : ℂ)) • angularCoefficient (fun axial => field (point,axial)) cell := by
  have fieldContinuous : Continuous (fun axial => field (point,axial)) :=
    smooth.continuousOn.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => ⟨inside,mem_univ _⟩)
  have derivativeSmooth : ContDiffOn ℝ ∞ (fderiv ℝ field) (domain ×ˢ (univ : Set ℝ)) :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen (openDomain.prod isOpen_univ)).mp smooth).2
  have derivativeContinuous : Continuous (fun axial => fderiv ℝ field (point,axial) (0,1)) :=
    (derivativeSmooth.clm_apply (contDiffOn_const (c := (0,1)))).continuousOn.comp_continuous
      (continuous_const.prodMk continuous_id) (fun _ => ⟨inside,mem_univ _⟩)
  apply angularCoefficient_derivative _ _ fieldContinuous derivativeContinuous
  · intro axial
    have fieldDerivative := ((smooth.contDiffAt ((openDomain.prod isOpen_univ).mem_nhds
      (show (point,axial) ∈ domain ×ˢ (univ : Set ℝ) from ⟨inside,mem_univ _⟩))).differentiableAt (by simp)).hasFDerivAt
    have insertion : HasDerivAt (fun current : ℝ => (point,current)) (0,1) axial :=
      (hasDerivAt_const axial point).prodMk (hasDerivAt_id axial)
    exact fieldDerivative.comp_hasDerivAt axial insertion
  · have endpoint := periodic (-Real.pi)
    simpa only [show -Real.pi+2*Real.pi=Real.pi by ring] using endpoint

/-- The existing compatible full Cartesian field is axially periodic, including its chosen zero extension. -/
theorem nativeFamilyField_cell_periodic {dimension : ℕ} (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (rows : ∀ index,DivisionRow dimension (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (point : Spatial) :
    Function.Periodic (fun axial => gluedCartesianFamilyField parameters lower positive bounded cofinal rows curves (point,axial)) (2*Real.pi) := by
  have polarPeriodic (radius polar : ℝ) : Function.Periodic
      (fun axial => gluedPhysicalFamilyField parameters lower positive bounded cofinal rows curves (radius,polar,axial)) (2*Real.pi) := by
    intro axial
    dsimp only [gluedPhysicalFamilyField]
    split_ifs
    · exact (curves _).fullField_cell_periodic (bounded _) radius polar axial
    · rfl
  intro axial
  exact polarPeriodic _ _ axial

end Grad.ActualScalarWeakEquations
