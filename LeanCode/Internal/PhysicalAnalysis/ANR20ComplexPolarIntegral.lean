import ANR19TestLaplacian

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.BoundaryTrace
open Grad.DiskExtension.Operator

/-- Ordinary area polar integration for complex pairings, obtained from the
accepted real-valued Jacobian identity by continuous real component maps. -/
theorem closedDisk_polar_complex (field : SpatialPlane → ℂ) (continuousField : Continuous field) :
    (∫ point in closedUnitDisk, field point) =
      ∫ radius in Icc (0 : ℝ) 1, ∫ angle in Icc (-Real.pi) Real.pi,
        radius • field (polarPlane (radius, angle)) := by
  let integrand : ℝ × ℝ → ℂ := fun point => point.1 • field (polarPlane point)
  have continuousIntegrand : Continuous integrand := continuous_fst.smul (continuousField.comp polarPlane_smooth.continuous)
  have diskIntegrable : IntegrableOn field closedUnitDisk := by
    apply continuousField.continuousOn.integrableOn_compact
    rw [closedUnitDisk_eq_closedBall]
    exact isCompact_closedBall _ _
  have rectangleIntegrable : Integrable integrand
      ((volume.restrict (Icc (0 : ℝ) 1)).prod (volume.restrict (Icc (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact continuousIntegrand.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have outerContinuous : Continuous (fun angle : ℝ => ∫ radius in Icc (0 : ℝ) 1, integrand (radius, angle)) :=
    continuous_parametric_integral_of_continuous (μ := (volume : Measure ℝ))
      (f := fun angle radius : ℝ => integrand (radius, angle))
      (continuousIntegrand.comp continuous_swap) (s := Icc (0 : ℝ) 1) isCompact_Icc
  have innerIntegrable (angle : ℝ) : IntegrableOn (fun radius => integrand (radius, angle)) (Icc (0 : ℝ) 1) :=
    (continuousIntegrand.comp (continuous_id.prodMk continuous_const)).continuousOn.integrableOn_compact isCompact_Icc
  have component (projection : ℂ →L[ℝ] ℝ) :
      projection (∫ point in closedUnitDisk, field point) =
        projection (∫ angle in Icc (-Real.pi) Real.pi, ∫ radius in Icc (0 : ℝ) 1, integrand (radius, angle)) := by
    rw [← projection.integral_comp_comm diskIntegrable,
      ← projection.integral_comp_comm (outerContinuous.continuousOn.integrableOn_compact isCompact_Icc)]
    have realFormula := closedUnitDisk_polar_integral (fun point => projection (field point))
      (projection.continuous.comp continuousField)
    rw [realFormula, Measure.restrict_congr_set Ioo_ae_eq_Icc]
    apply integral_congr_ae
    filter_upwards [] with angle
    rw [← projection.integral_comp_comm (innerIntegrable angle),
      intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), ← integral_Icc_eq_integral_Ioc]
    apply integral_congr_ae
    filter_upwards [] with radius
    change radius * projection (field (spatialPlaneOfPair (polarCoord.symm (radius, angle)))) =
      projection (radius • field (polarPlane (radius, angle)))
    rw [projection.map_smul, smul_eq_mul, polarPlane_polar]
  have expression : (∫ point in closedUnitDisk, field point) =
      ∫ angle in Icc (-Real.pi) Real.pi, ∫ radius in Icc (0 : ℝ) 1, integrand (radius, angle) :=
    Complex.ext (component Complex.reCLM) (component Complex.imCLM)
  exact expression.trans (integral_integral_swap rectangleIntegrable).symm

end Grad.CircularHighRegularity
