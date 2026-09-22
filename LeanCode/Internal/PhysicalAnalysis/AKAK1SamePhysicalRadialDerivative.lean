import AKAF12ActualSourcePointwiseForceConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1)

/-- The radial derivative uses the already accepted SAME full physical
Hilbert jet, rather than a newly chosen physical representative. -/
def componentRadialField (component : Fin dimension) : ℝ × (ℝ × ℝ) → ComplexEuclidean 1 :=
  physicalMixedFourierField lower positive bounded
    (physicalJetOfHilbert lower positive bounded (curves.componentCurve component)
      (curves.componentCurve_smooth bounded component) (curves.componentCurve_grade bounded component)) 1 0 0

theorem componentField_radial_hasDerivWithinAt (component : Fin dimension)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    HasDerivWithinAt (fun current => curves.componentField bounded component (current,angles))
      (componentRadialField curves bounded component (radius,angles)) (Icc lower 1) radius := by
  unfold SmoothLowPhysicalRow.componentField
  rw [hilbertPhysicalField_eq_jet lower positive bounded (curves.componentCurve component)
    (curves.componentCurve_smooth bounded component) (curves.componentCurve_grade bounded component)]
  have derivative := physicalMixedFourierSection_radialDerivative lower positive bounded
    (physicalJetOfHilbert lower positive bounded (curves.componentCurve component)
      (curves.componentCurve_smooth bounded component) (curves.componentCurve_grade bounded component))
    0 0 0 angles radius inside
  simpa only [componentRadialField,physicalMixedFourierField,radialSectionExtension,
    radialClamp_eq lower bounded.le radius inside, ContinuousMap.coe_mk, Nat.zero_add] using derivative

def fullRadialField (point : ℝ × (ℝ × ℝ)) : ComplexEuclidean dimension :=
  ∑ component : Fin dimension, matrixUnit component 0 (componentRadialField curves bounded component point)

/-- The actual full vector field has a genuine closed-collar radial
HasDerivWithinAt, with every Fourier mode and the same stored radial jets. -/
theorem fullField_radial_hasDerivWithinAt (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    HasDerivWithinAt (fun current => curves.fullField bounded (current,angles))
      (fullRadialField curves bounded (radius,angles)) (Icc lower 1) radius := by
  have derivative := HasDerivWithinAt.fun_sum (u := Finset.univ) (fun component _ =>
    ((matrixUnit (input := 1) (output := dimension) component 0).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt radius
      (componentField_radial_hasDerivWithinAt curves bounded component radius inside angles))
  simpa only [SmoothLowPhysicalRow.fullField, fullRadialField, Finset.sum_apply,
    Function.comp_apply, ContinuousLinearMap.coe_restrictScalars'] using derivative

end Grad.ActualPolarEquations
