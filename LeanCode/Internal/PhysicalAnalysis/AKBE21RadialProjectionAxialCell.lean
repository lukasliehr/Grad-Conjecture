import AKBE20OriginalPlanarForceFlux

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.CartesianState Grad.ClosedJets Grad.Constraints Grad.BoundaryTrace Grad.SourceCollarFullSource

private theorem originalAngularCoefficient_map {E F : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (mapping : E →L[ℂ] F) (field : ℝ → E) (continuousField : Continuous field) (cell : ℤ) :
    angularCoefficient (fun angle => mapping (field angle)) cell = mapping (angularCoefficient field cell) := by
  rw [angularCoefficient_compact_general,angularCoefficient_compact_general,mapping.map_smul_of_tower]
  congr 1
  have integrable : IntegrableOn (fun angle => cellExponential (-cell) angle • field angle) (Icc (-Real.pi) Real.pi) :=
    ((cellExponential_smooth (-cell)).continuous.smul continuousField).continuousOn.integrableOn_Icc
  have actual := mapping.integral_comp_comm (μ := volume.restrict (Icc (-Real.pi) Real.pi)) integrable
  simpa only [map_smul] using actual

private def originalRadialValueMap (angle : ℝ) : ComplexEuclidean 2 →L[ℂ] ℂ :=
  (Real.cos angle : ℂ) • PiLp.proj 2 (fun _ : Fin 2 => ℂ) 0 +
    (Real.sin angle : ℂ) • PiLp.proj 2 (fun _ : Fin 2 => ℂ) 1

private theorem originalRadialValueMap_apply (angle : ℝ) (value : ComplexEuclidean 2) :
    originalRadialValueMap angle value = polarRadialComponent angle value := rfl

/-- The original radial mean removal commutes with the actual axial Fourier
cell. This is Fubini on the SAME full physical field, with no angular or
axial mode discarded and no coefficient multiplication moved across cells. -/
theorem originalRadialProjection_axialCell (field : ℝ × ℝ → ComplexEuclidean 2)
    (continuousField : Continuous field) (cell : ℤ) (angle : ℝ) :
    angularCoefficient (fun axial => field (angle,axial) -
      angularCoefficient (fun polar => polarRadialComponent polar (field (polar,axial))) 0 • polarRadialVector angle) cell =
      angularCoefficient (fun axial => field (angle,axial)) cell -
        angularCoefficient (fun polar => polarRadialComponent polar
          (angularCoefficient (fun axial => field (polar,axial)) cell)) 0 • polarRadialVector angle := by
  let radial : ℝ × ℝ → ℂ := fun angles => polarRadialComponent angles.1 (field angles)
  have radialContinuous : Continuous radial := by
    unfold radial polarRadialComponent
    fun_prop
  have meanContinuous : Continuous (fun axial => angularCoefficient (fun polar => radial (polar,axial)) 0) :=
    Grad.SourceCollarFullSource.angularCoefficient_continuous_parameter (fun angles => radial (angles.2,angles.1))
      (radialContinuous.comp (continuous_snd.prodMk continuous_fst)) 0
  have radialCell (polar : ℝ) : angularCoefficient (fun axial => radial (polar,axial)) cell =
      polarRadialComponent polar (angularCoefficient (fun axial => field (polar,axial)) cell) := by
    exact originalAngularCoefficient_map (originalRadialValueMap polar) (fun axial => field (polar,axial))
      (continuousField.comp (continuous_const.prodMk continuous_id)) cell
  have meanSame := (doubleCoefficient_swap radial radialContinuous 0 cell).symm
  simp_rw [radialCell] at meanSame
  let mapping : ℂ →L[ℂ] ComplexEuclidean 2 := (ContinuousLinearMap.id ℂ ℂ).smulRight (polarRadialVector angle)
  have mapped := originalAngularCoefficient_map mapping (fun axial => angularCoefficient (fun polar => radial (polar,axial)) 0)
    meanContinuous cell
  change angularCoefficient (fun axial => angularCoefficient (fun polar => radial (polar,axial)) 0 • polarRadialVector angle) cell =
    angularCoefficient (fun axial => angularCoefficient (fun polar => radial (polar,axial)) 0) cell • polarRadialVector angle at mapped
  rw [meanSame] at mapped
  have subtraction := angularCoefficient_sub_general (fun axial => field (angle,axial))
    (fun axial => angularCoefficient (fun polar => radial (polar,axial)) 0 • polarRadialVector angle)
    (continuousField.comp (continuous_const.prodMk continuous_id)) (meanContinuous.smul continuous_const) cell
  exact subtraction.trans (congrArg (angularCoefficient (fun axial => field (angle,axial)) cell - ·) mapped)

end Grad.ActualCartesianWeakEquations
