import AKBE17PuncturedRadialTranspose

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.PDEBootstrap Grad.ClosedJets Grad.CompactCutoff Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.SourceCollarFullSource Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.RadialLedger

private theorem originalCircle_continuousLocalization (raw : Spatial → ComplexEuclidean 2)
    (continuousRaw : ContinuousOn raw (openUnitDisk \ {(0 : Spatial)}))
    (point : Spatial) (positive : 0 < ‖point‖) (inside : ‖point‖ < 1) :
    ∃ localized : Spatial → ComplexEuclidean 2, Continuous localized ∧
      ∀ other : Spatial, ‖other‖ = ‖point‖ → localized other = raw other := by
  let circle := Metric.sphere (0 : Spatial) ‖point‖
  have included : circle ⊆ openUnitDisk \ {(0 : Spatial)} := by
    intro other membership
    have sameNorm : ‖other‖ = ‖point‖ := by simpa only [circle,Metric.mem_sphere,dist_zero_right] using membership
    refine ⟨sameNorm.trans_lt inside,?_⟩
    intro zeroPoint
    have otherZero : other = 0 := Set.mem_singleton_iff.mp zeroPoint
    rw [otherZero,norm_zero] at sameNorm
    exact (ne_of_gt positive) sameNorm.symm
  let cutoff := compactCutoff circle (openUnitDisk \ {(0 : Spatial)}) (isCompact_sphere 0 ‖point‖)
    (openUnitDisk_isOpen.sdiff isClosed_singleton) included
  refine ⟨fun other => cutoff.toFun other • raw other,
    continuous_smul_of_tsupport_subset _ (openUnitDisk_isOpen.sdiff isClosed_singleton)
      cutoff.toFun cutoff.smooth.continuous cutoff.supported raw continuousRaw,?_⟩
  intro other sameNorm
  change cutoff.toFun other • raw other = raw other
  rw [cutoff.one_on (by simpa only [circle,Metric.mem_sphere,dist_zero_right] using sameNorm),one_smul]

private theorem originalPolarClosedPoint_norm (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) :
    ‖(Grad.Constraints.polarClosedPoint radius bounded angle).val‖ = |radius| := by
  change ‖planeRotationEquiv angle (axisClosedPoint radius bounded).val‖ = _
  rw [LinearIsometryEquiv.norm_map]
  change ‖WithLp.toLp 2 ![radius,(0 : ℝ)]‖ = _
  rw [PiLp.norm_eq_of_L2]
  simp [Fin.sum_univ_two,Real.sqrt_sq_eq_abs]

/-- The checked rough Cartesian projector is the literal original radial
mean removal at every interior nonzero radius, even without axis smoothness. -/
theorem puncturedRadialReflectionValue_polar (raw : Spatial → ComplexEuclidean 2)
    (continuousRaw : ContinuousOn raw (openUnitDisk \ {(0 : Spatial)}))
    (radius : ℝ) (positive : 0 < radius) (inside : radius < 1)
    (bounded : |radius| ≤ 1) (angle : ℝ) :
    closedRadialReflectionValue (fun point : ClosedDisk => raw point.val)
      (Grad.Constraints.polarClosedPoint radius bounded angle) =
      raw (Grad.Constraints.polarClosedPoint radius bounded angle).val -
        angularCoefficient (fun polar => polarRadialComponent polar
          (raw (Grad.Constraints.polarClosedPoint radius bounded polar).val)) 0 • polarRadialVector angle := by
  let point := Grad.Constraints.polarClosedPoint radius bounded angle
  have pointNorm : ‖point.val‖ = radius := (originalPolarClosedPoint_norm radius bounded angle).trans (abs_of_pos positive)
  obtain ⟨localized,continuousLocal,same⟩ := originalCircle_continuousLocalization raw continuousRaw point.val
    (by rw [pointNorm]; exact positive) (by rw [pointNorm]; exact inside)
  let closedLocal : ClosedDisk → ComplexEuclidean 2 := fun other => localized other.val
  have continuousClosed : Continuous closedLocal := continuousLocal.comp continuous_subtype_val
  have projected := closedRadialReflectionValue_norm_locality (fun other : ClosedDisk => raw other.val) closedLocal point
    (fun other sameNorm => (same other.val sameNorm).symm)
  have localPolar (polar : ℝ) : localized (Grad.Constraints.polarClosedPoint radius bounded polar).val =
      raw (Grad.Constraints.polarClosedPoint radius bounded polar).val := by
    apply same
    rw [originalPolarClosedPoint_norm,pointNorm,abs_of_pos positive]
  rw [projected,closedRadialReflectionValue_polar closedLocal continuousClosed]
  simp only [closedLocal,localPolar]

end Grad.ActualCartesianWeakEquations
