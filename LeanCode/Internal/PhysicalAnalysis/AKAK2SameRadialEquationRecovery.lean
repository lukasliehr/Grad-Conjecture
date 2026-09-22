import AKAK1SamePhysicalRadialDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row rhsRow : DivisionRow dimension lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row)
    (rhs : SmoothLowPhysicalRow parameters lower positive rhsRow) (bounded : lower < 1)
    (equation : ∀ mode : ℤ × ℤ, ∀ radius, radius ∈ Icc lower 1 →
      HasDerivWithinAt (fun current => curves.physicalCurve 0 current mode)
        (rhs.physicalCurve 0 radius mode) (Icc lower 1) radius)
include equation

/-- Uniqueness of the already checked Hilbert derivative identifies every
radial Fourier jet with the SAME original equation's physical RHS. -/
theorem componentRadialField_eq_of_equation (component : Fin dimension)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    componentRadialField curves bounded component (radius,angles) =
      rhs.componentField bounded component (radius,angles) := by
  have coefficients (mode : ℤ × ℤ) :
      hilbertRadialJetSection lower bounded (curves.componentCurve component)
        (curves.componentCurve_smooth bounded component) 1 0 mode ⟨radius,inside⟩ =
      rhs.componentCurve component 0 radius mode := by
    have actual := ((matrixUnit (input := dimension) (output := 1) 0 component).restrictScalars ℝ).hasFDerivAt.comp_hasDerivWithinAt radius
      (equation mode radius inside)
    have given : HasDerivWithinAt (fun current => curves.componentCurve component 0 current mode)
        (rhs.componentCurve component 0 radius mode) (Icc lower 1) radius := by
      change HasDerivWithinAt
        (fun current => matrixUnit (0 : Fin 1) component (curves.physicalCurve 0 current mode))
        (matrixUnit (0 : Fin 1) component (rhs.physicalCurve 0 radius mode)) (Icc lower 1) radius
      exact actual
    have jet := hilbertRadialJetSection_derivative lower bounded (curves.componentCurve component)
      (curves.componentCurve_smooth bounded component) 0 0 mode radius inside
    simp only [iteratedDerivWithin_zero,Nat.zero_add] at jet
    exact (jet.derivWithin (uniqueDiffOn_Icc bounded radius inside)).symm.trans
      (given.derivWithin (uniqueDiffOn_Icc bounded radius inside))
  unfold componentRadialField
  rw [physicalMixedFourierField_baseSeries]
  unfold SmoothLowPhysicalRow.componentField hilbertPhysicalField
  rw [radialClamp_eq lower bounded.le radius inside]
  change physicalCharacterSeries
      (fun mode => hilbertRadialJetSection lower bounded (curves.componentCurve component)
        (curves.componentCurve_smooth bounded component) 1 0 mode ⟨radius,inside⟩) angles = _
  congr 1
  exact funext coefficients

theorem samePhysical_radialDerivative (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    HasDerivWithinAt (fun current => curves.fullField bounded (current,angles))
      (rhs.fullField bounded (radius,angles)) (Icc lower 1) radius := by
  have same : fullRadialField curves bounded (radius,angles) = rhs.fullField bounded (radius,angles) := by
    unfold fullRadialField SmoothLowPhysicalRow.fullField
    apply Finset.sum_congr rfl
    intro component _
    rw [componentRadialField_eq_of_equation curves rhs bounded equation component radius inside angles]
  rw [← same]
  exact fullField_radial_hasDerivWithinAt curves bounded radius inside angles

end Grad.ActualPolarEquations
