import AKAK3ActualPairPhysicalRadialPDE

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularSmoothCore

private theorem scalarMatrixUnit (value : ComplexEuclidean 1) : matrixUnit (0 : Fin 1) 0 value = value := by
  apply PiLp.ext
  intro component
  fin_cases component
  simp [matrixUnit_apply,operatorBasis]

/-- The one-dimensional full physical representative is its literal
original coefficient series, with no extra component or normalization. -/
theorem fullField_scalarSeries {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1) (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    curves.fullField bounded (radius,angles) = physicalCharacterSeries (fun mode => curves.physicalCurve 0 radius mode) angles := by
  have component : curves.componentCurve 0 = curves.physicalCurve := by
    funext grade location
    apply lp.ext
    funext mode
    exact scalarMatrixUnit _
  simp only [SmoothLowPhysicalRow.fullField,Fin.sum_univ_one,scalarMatrixUnit,
    SmoothLowPhysicalRow.componentField,component,hilbertPhysicalField,
    radialClamp_eq lower bounded.le radius inside]

/-- Continuous genuine coefficient derivatives and actual a.e. original
RHS coefficients determine a classical equation on the SAME closed collar. -/
theorem hilbertPhysicalField_radial_of_actual_rhs {parameters : PhaseParameters}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (curve : ℕ → ℝ → CellL2 1)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (curve grade) (Icc lower 1))
    (same : ∀ grade radius, radius ∈ Icc lower 1 → ∀ mode : ℤ × ℤ,
      curve grade radius mode = ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • curve 0 radius mode)
    {row : DivisionRow 1 lower} (rhs : SmoothLowPhysicalRow parameters lower positive row)
    (slopes : (ℤ × ℤ) → C(ℝ,ComplexEuclidean 1))
    (derivatives : ∀ mode radius, radius ∈ Icc lower 1 →
      HasDerivWithinAt (fun current => curve 0 current mode) (slopes mode radius) (Icc lower 1) radius)
    (actual : ∀ mode, slopes mode =ᵐ[volume.restrict (Icc lower 1)]
      fun radius => lowRhoPhysicalCoefficient parameters lower positive row radius mode)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    HasDerivWithinAt (fun current => hilbertPhysicalField lower bounded curve (current,angles))
      (rhs.fullField bounded (radius,angles)) (Icc lower 1) radius := by
  rw [fullField_scalarSeries rhs bounded radius inside angles]
  apply hilbertPhysicalField_radial_of_coefficients lower positive bounded curve smooth same radius inside
  intro mode
  have identified : slopes mode radius = rhs.physicalCurve 0 radius mode := by
    apply collarCurve_eq_of_ae lower bounded (slopes mode)
      (fun location => rhs.physicalCurve 0 location mode) (slopes mode).continuous.continuousOn
      ((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode).continuous.comp_continuousOn
        (rhs.physicalCurve_smooth bounded 0).continuousOn) _ inside
    filter_upwards [actual mode,rhs.physicalCurve_actual bounded 0] with location slope curveSame
    simpa only [curveSame mode,pow_zero,one_smul] using slope
  rw [← identified]
  exact derivatives mode radius inside

end Grad.ActualPolarEquations
