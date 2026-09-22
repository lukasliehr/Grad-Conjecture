import AKAW3JointCellRepresentative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.ActualNativeCellMoments
open Grad.ClosedJets Grad.SourceCollarCoefficients Grad.BoundaryTrace Grad.DiskExtension.Operator

/-- Tonelli converts the actual joint Fourier energy to the all-cell polar
energy before any cell is selected. -/
theorem fullCell_polar_energy {dimension : ℕ}
    (curve : ℝ → CellL2 dimension) (field : ℤ → ℝ × ℝ → ComplexEuclidean dimension)
    (curveMeasurable : AEStronglyMeasurable curve (volume.restrict (Ioc (0 : ℝ) 1)))
    (measurable : ∀ cell, AEStronglyMeasurable (field cell)
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (-Real.pi) Real.pi))))
    (continuousSlices : ∀ᵐ radius ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ cell,
      Continuous (fun angle => field cell (radius,angle)))
    (coefficientBound : ∀ᵐ radius ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ mode cell,
      ‖angularCoefficient (fun angle => field cell (radius,angle)) mode‖ ≤ ‖curve radius (mode,cell)‖) :
    (∫⁻ point : ℝ × ℝ in Ioc (0 : ℝ) 1 ×ˢ Ioc (-Real.pi) Real.pi,
      ∑' cell : ℤ, ENNReal.ofReal (‖field cell point‖ ^ 2)) ≤
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal (‖curve radius‖ ^ 2) := by
  have density (cell : ℤ) : AEMeasurable (fun point => ENNReal.ofReal (‖field cell point‖ ^ 2))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (-Real.pi) Real.pi))) :=
    ((measurable cell).norm.pow 2).aemeasurable.ennreal_ofReal
  rw [Measure.volume_eq_prod,← Measure.prod_restrict]
  rw [lintegral_prod _ (AEMeasurable.tsum density)]
  calc
    _ ≤ ∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal ((2 * Real.pi) * ‖curve radius‖ ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [continuousSlices,coefficientBound] with radius continuousSlices coefficientBound
      exact fullCell_angular_energy (curve radius) (fun cell angle => field cell (radius,angle))
        continuousSlices coefficientBound
    _ = _ := by
      simp_rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.pi)]
      exact lintegral_const_mul'' _ (curveMeasurable.norm.pow 2).aemeasurable.ennreal_ofReal

/-- Exact polar Jacobian and the unit-disk radius bound give a genuine
Cartesian all-cell energy bound. -/
theorem fullCell_disk_energy {dimension : ℕ}
    (curve : ℝ → CellL2 dimension) (field : ℤ → SpatialPlane → ComplexEuclidean dimension)
    (curveMeasurable : AEStronglyMeasurable curve (volume.restrict (Ioc (0 : ℝ) 1)))
    (measurable : ∀ cell, AEStronglyMeasurable
      (fun point : ℝ × ℝ => field cell (spatialPlaneOfPair (polarCoord.symm point)))
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc (-Real.pi) Real.pi))))
    (continuousSlices : ∀ᵐ radius ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ cell,
      Continuous (fun angle => field cell (spatialPlaneOfPair (polarCoord.symm (radius,angle)))))
    (coefficientBound : ∀ᵐ radius ∂volume.restrict (Ioc (0 : ℝ) 1), ∀ mode cell,
      ‖angularCoefficient (fun angle => field cell (spatialPlaneOfPair (polarCoord.symm (radius,angle)))) mode‖ ≤
        ‖curve radius (mode,cell)‖) :
    (∫⁻ point in openUnitDisk, ∑' cell : ℤ, ENNReal.ofReal (‖field cell point‖ ^ 2)) ≤
      ENNReal.ofReal (2 * Real.pi) *
        ∫⁻ radius in Ioc (0 : ℝ) 1, ENNReal.ofReal (‖curve radius‖ ^ 2) := by
  rw [Grad.WeightedAxisRemoval.openDisk_lintegral_eq_polar]
  calc
    _ ≤ ∫⁻ point : ℝ × ℝ in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
        ∑' cell : ℤ, ENNReal.ofReal (‖field cell (spatialPlaneOfPair (polarCoord.symm point))‖ ^ 2) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)] with point inside
      exact mul_le_of_le_one_left zero_le (by simpa using ENNReal.ofReal_le_ofReal inside.1.2.le)
    _ ≤ ∫⁻ point : ℝ × ℝ in Ioc (0 : ℝ) 1 ×ˢ Ioc (-Real.pi) Real.pi,
        ∑' cell : ℤ, ENNReal.ofReal (‖field cell (spatialPlaneOfPair (polarCoord.symm point))‖ ^ 2) :=
      lintegral_mono_set (Set.prod_mono Ioo_subset_Ioc_self Ioo_subset_Ioc_self)
    _ ≤ _ := fullCell_polar_energy curve _ curveMeasurable measurable continuousSlices coefficientBound

end Grad.ActualNativeCellMoments
