import AKAW6OriginalNativeConjugatedEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.ActualNativeCellMoments
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.ActualPuncturedFamily Grad.AnnularRestriction Grad.AnnularCurrentLow
open Grad.ActualCartesianDescent Grad.ActualCartesianIntegrability Grad.PhaseAlgebra Grad.SourceCollarFullSource
open Grad.DiskExtension.Operator Grad.BoundaryTrace Grad.PhysicalAxisEquation

variable {dimension : ℕ} (parameters : PhaseParameters) (lower : ℕ → ℝ)
    (positive : ∀ index,0 < lower index) (bounded : ∀ index,lower index < 1)
    (cofinal : Tendsto lower atTop (𝓝 0)) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow dimension (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first ≤ second),
      originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second)=rows first)

/-- The literal Cartesian conjugation, with an optional cell-frequency moment. -/
def sameWeightedCartesianCell (grade : ℕ) (cell : ℤ) (point : SpatialPlane) : ComplexEuclidean dimension :=
  cellFrequency cell ^ grade • (cartesianWeight parameters cell point •
    gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell point)

theorem sameWeightedCartesianCell_polar (grade : ℕ) (cell : ℤ) (radius angle : ℝ) (nonnegative : 0 ≤ radius) :
    sameWeightedCartesianCell parameters lower positive bounded cofinal rows curves grade cell
      (spatialPlaneOfPair (polarCoord.symm (radius,angle))) =
        cellFrequency cell ^ grade • (Real.exp (radialPhase parameters radius cell) •
          gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell
            (spatialPlaneOfPair (polarCoord.symm (radius,angle)))) := by
  unfold sameWeightedCartesianCell
  rw [polarPlane_originalParametrization radius angle,cartesianWeight_polar parameters cell radius angle nonnegative]

include compatible in
theorem sameWeightedCartesianCell_aestronglyMeasurable (grade : ℕ) (cell : ℤ) :
    AEStronglyMeasurable (sameWeightedCartesianCell parameters lower positive bounded cofinal rows curves grade cell)
      (volume.restrict openUnitDisk) :=
  (aestronglyMeasurable_const (b := cellFrequency cell ^ grade)).smul
    ((cartesianWeight_contDiff parameters cell).continuous.aestronglyMeasurable.smul
      (sameCartesianCell_aestronglyMeasurable parameters lower positive bounded cofinal decreasing rows curves compatible cell))

include compatible in
theorem sameWeightedCartesianCell_polar_aestronglyMeasurable (grade : ℕ) (cell : ℤ) :
    AEStronglyMeasurable (fun point : ℝ × ℝ =>
      sameWeightedCartesianCell parameters lower positive bounded cofinal rows curves grade cell
        (spatialPlaneOfPair (polarCoord.symm point)))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (-Real.pi) Real.pi))) := by
  have weight : Continuous (fun point : ℝ × ℝ => cartesianWeight parameters cell
      (spatialPlaneOfPair (polarCoord.symm point))) := by
    have equal : (fun point : ℝ × ℝ => cartesianWeight parameters cell (spatialPlaneOfPair (polarCoord.symm point))) =
        fun point => cartesianWeight parameters cell (polarPlane point) :=
      funext (fun point => congrArg (cartesianWeight parameters cell) (polarPlane_originalParametrization point.1 point.2))
    rw [equal]
    exact (cartesianWeight_contDiff parameters cell).continuous.comp polarPlane_smooth.continuous
  exact (aestronglyMeasurable_const (b := cellFrequency cell ^ grade)).smul (weight.aestronglyMeasurable.smul
    (sameCartesianCell_polar_aestronglyMeasurable parameters lower positive bounded cofinal decreasing rows curves compatible cell))

include compatible in
theorem sameWeightedCartesianCell_continuousSlices (grade : ℕ) (cell : ℤ) (radius : ℝ) (inside : radius ∈ Ioc (0 : ℝ) 1) :
    Continuous (fun angle => sameWeightedCartesianCell parameters lower positive bounded cofinal rows curves grade cell
      (spatialPlaneOfPair (polarCoord.symm (radius,angle)))) := by
  simp_rw [sameWeightedCartesianCell_polar parameters lower positive bounded cofinal rows curves grade cell radius _ inside.1.le]
  exact (continuous_const (y := cellFrequency cell ^ grade)).smul ((continuous_const (y := Real.exp (radialPhase parameters radius cell))).smul
    (sameCartesianCell_polar_continuousSlices parameters lower positive bounded cofinal decreasing rows curves compatible cell radius inside))

include compatible in
theorem sameWeightedCartesianCell_coefficient_bound (grade : ℕ) (radius : ℝ) (inside : radius ∈ Ioc (0 : ℝ) 1) (mode cell : ℤ) :
    ‖angularCoefficient (fun angle => sameWeightedCartesianCell parameters lower positive bounded cofinal rows curves grade cell
      (spatialPlaneOfPair (polarCoord.symm (radius,angle)))) mode‖ ≤
        ‖gluedWeightedFamilyCurve parameters lower positive cofinal rows curves grade radius (mode,cell)‖ := by
  simp_rw [sameWeightedCartesianCell_polar parameters lower positive bounded cofinal rows curves grade cell radius _ inside.1.le,
    ← Complex.coe_smul]
  rw [show (fun angle => ((cellFrequency cell ^ grade : ℝ) : ℂ) • ((Real.exp (radialPhase parameters radius cell) : ℂ) •
      gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell (spatialPlaneOfPair (polarCoord.symm (radius,angle))))) =
      ((cellFrequency cell ^ grade : ℝ) : ℂ) • ((Real.exp (radialPhase parameters radius cell) : ℂ) •
        (fun angle => gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell (spatialPlaneOfPair (polarCoord.symm (radius,angle))))) from rfl,
    angularCoefficient_smul_continuous,angularCoefficient_smul_continuous,
    sameCartesianCell_coefficients parameters lower positive bounded cofinal decreasing rows curves compatible cell radius inside mode]
  rw [← gluedWeightedFamilyCurve_physical parameters lower positive bounded cofinal decreasing rows curves compatible 0 radius inside (mode,cell)]
  let index := selectedInnerCollar lower cofinal radius inside.1
  have localInside : radius ∈ Icc (lower index) 1 := ⟨(selectedInnerCollar_lt lower cofinal radius inside.1).le,inside.2⟩
  rw [gluedWeightedFamilyCurve_same parameters lower positive bounded cofinal decreasing rows curves compatible grade index radius localInside,
    gluedWeightedFamilyCurve_same parameters lower positive bounded cofinal decreasing rows curves compatible 0 index radius localInside]
  have shifted := (curves index).shift (bounded index) 0 grade radius localInside (mode,cell)
  simp only [zero_add] at shifted
  rw [shifted,norm_smul,norm_smul,norm_pow,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (pow_nonneg (cellFrequency_pos cell).le grade),Real.norm_of_nonneg (annularFrequency_pos (mode,cell)).le]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply pow_le_pow_left₀ (cellFrequency_pos cell).le
  apply (cellFrequency_le_polynomial cell).trans
  change 1 + |(cell : ℝ)| ≤ 1 + |(mode : ℝ)| + |(cell : ℝ)|
  linarith [abs_nonneg (mode : ℝ)]

end Grad.ActualNativeCellMoments
