import AKBD19SameProjectedDeterminant

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter
open scoped Topology ContDiff BigOperators
namespace Grad.ActualDeterminantEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.ActualSmoothPhysicalField
open Grad.ActualCartesianEquations Grad.ActualCartesianDescent Grad.PhysicalFamily
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryTrace

def polarRotationCLM (angle : ℝ) : ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 3 :=
  (Real.cos angle : ℂ) • matrixUnit 0 0 - (Real.sin angle : ℂ) • matrixUnit 0 1 +
  (Real.sin angle : ℂ) • matrixUnit 1 0 + (Real.cos angle : ℂ) • matrixUnit 1 1 + matrixUnit 2 2

theorem polarRotationCLM_apply (angle : ℝ) (value : ComplexEuclidean 3) :
    polarRotationCLM angle value = cartesianCovariantValue angle value := by
  rw [cartesianCovariantValue_apply]
  apply PiLp.ext
  intro component
  fin_cases component <;> simp [polarRotationCLM,matrixUnit_apply,operatorBasis]

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower < 1)

def vectorDirectionalField (direction : ℝ × (ℝ × ℝ)) (point : ℝ × (ℝ × ℝ)) : ComplexEuclidean dimension :=
  fderiv ℝ (curves.fullField bounded) point direction

theorem fullVectorField_hasFDerivAt (point : ℝ × (ℝ × ℝ)) (inside : point.1 ∈ Ioo lower 1) :
    HasFDerivAt (curves.fullField bounded) (fderiv ℝ (curves.fullField bounded) point) point := by
  have smooth : ContDiffOn ℝ ∞ (curves.fullField bounded) (Ioo lower 1 ×ˢ (univ : Set (ℝ × ℝ))) :=
    (curves.fullField_smooth bounded).mono (fun _ member => ⟨⟨member.1.1.le,member.1.2.le⟩,mem_univ _⟩)
  exact (smooth.contDiffAt ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨inside,mem_univ _⟩)).differentiableAt (by simp) |>.hasFDerivAt

theorem vectorDirectionalField_component (component : Fin dimension) (direction : ℝ × (ℝ × ℝ))
    (point : ℝ × (ℝ × ℝ)) (inside : point.1 ∈ Ioo lower 1) :
    vectorDirectionalField curves bounded direction point component = scalarDirectionalField curves bounded component direction point := by
  have composed := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin dimension => ℂ) component).restrictScalars ℝ).hasFDerivAt.comp point
    (fullVectorField_hasFDerivAt curves bounded point inside)
  exact (congrArg (fun derivative : (ℝ × (ℝ × ℝ)) →L[ℝ] ℂ => derivative direction) composed.fderiv).symm

omit curves bounded in
/-- The genuine original Cartesian divergence in the exact L,L,1 convention. -/
def cartesianDeterminantDivergence (length : ℝ) (field : SpatialPlane × ℝ → ComplexEuclidean 3) (point : SpatialPlane × ℝ) : ℂ :=
  (length : ℂ) * (fderiv ℝ field point (spatialBasis 0,0) 0 + fderiv ℝ field point (spatialBasis 1,0) 1) +
    fderiv ℝ field point (0,1) 2

end Grad.ActualDeterminantEquations
