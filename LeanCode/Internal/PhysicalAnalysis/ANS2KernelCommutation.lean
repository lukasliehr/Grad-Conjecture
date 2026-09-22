import ANS1ComplexRotation

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.ActualAngularInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.GaugeCoefficients.Radial Grad.PhysicalFamily

theorem kernelRotation_projection {dimension : ℕ} (weight : ℝ → ℂ) (weightContinuous : Continuous weight)
    (field : SpatialPlane → ComplexEuclidean dimension) (continuousField : Continuous field)
    (mode : ℤ) (point : SpatialPlane) :
    angularProjectionValue mode (kernelRotationValue weight field) point =
      kernelRotationValue weight (angularProjectionValue mode field) point := by
  let integrand : ℝ × ℝ → ComplexEuclidean dimension := fun pair =>
    angularCharacter mode pair.1 • (weight pair.2 • field (planeRotationAction (pair.2 + pair.1) point))
  have rotationContinuous : Continuous (fun pair : ℝ × ℝ =>
      planeRotationAction (pair.2 + pair.1) point) := by
    have smooth : ContDiff ℝ ∞ (fun pair : ℝ × ℝ =>
        planeRotationAction (pair.2 + pair.1) point) := by
      rw [contDiff_piLp]
      intro coordinate
      fin_cases coordinate <;>
        simp [planeRotationAction, Grad.GeometryClosure.planarRotation, Matrix.vecHead, Matrix.vecTail] <;>
        fun_prop
    exact smooth.continuous
  have integrandContinuous : Continuous integrand :=
    ((angularCharacter_smooth mode).continuous.comp continuous_fst).smul
      ((weightContinuous.comp continuous_snd).smul (continuousField.comp rotationContinuous))
  have integrable : Integrable integrand
      ((volume.restrict (Icc (0 : ℝ) (2 * Real.pi))).prod (volume.restrict (Icc (0 : ℝ) (2 * Real.pi)))) := by
    rw [Measure.prod_restrict]
    exact integrandContinuous.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have leftRow (angle : ℝ) :
      angularCharacter mode angle • kernelRotationValue weight field (planeRotationAction angle point) =
        (2 * Real.pi)⁻¹ • ∫ other in Icc (0 : ℝ) (2 * Real.pi), integrand (angle, other) := by
    unfold kernelRotationValue integrand
    simp_rw [physicalRotation_add]
    rw [integral_smul, smul_comm (angularCharacter mode angle) ((2 * Real.pi)⁻¹)]
  have rightRow (other : ℝ) :
      weight other • angularProjectionValue mode field (planeRotationAction other point) =
        (2 * Real.pi)⁻¹ • ∫ angle in Icc (0 : ℝ) (2 * Real.pi), integrand (angle, other) := by
    rw [angularProjectionValue_eq_compactIntegral]
    rw [smul_comm (weight other) ((2 * Real.pi)⁻¹)]
    congr 1
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards with angle
    dsimp only [integrand]
    rw [physicalRotation_add, add_comm angle other, smul_comm]
  rw [angularProjectionValue_eq_compactIntegral]
  simp_rw [leftRow]
  change (2 * Real.pi)⁻¹ • _ = (2 * Real.pi)⁻¹ •
    ∫ other in Icc (0 : ℝ) (2 * Real.pi), weight other • angularProjectionValue mode field (planeRotationAction other point)
  simp_rw [rightRow]
  rw [integral_smul, integral_smul]
  exact congrArg (fun value : ComplexEuclidean dimension => (2 * Real.pi)⁻¹ • ((2 * Real.pi)⁻¹ • value))
    (integral_integral_swap integrable)

theorem kernelRotationValue_congr_closed {dimension : ℕ} (weight : ℝ → ℂ)
    {first second : SpatialPlane → ComplexEuclidean dimension}
    (same : ∀ point : ClosedDisk, first point.val = second point.val) (point : ClosedDisk) :
    kernelRotationValue weight first point.val = kernelRotationValue weight second point.val := by
  unfold kernelRotationValue
  congr 1
  apply integral_congr_ae
  filter_upwards with angle
  have equality := same (rotatedPoint angle point)
  simpa only [physicalRotation_eq_orthogonal, planeRotationEquiv_apply, rotatedPoint] using
    congrArg (fun value : ComplexEuclidean dimension => weight angle • value) equality

theorem angularClosedJet_kernelRotation {dimension : ℕ} (weight : ℝ → ℂ) (weightSmooth : ContDiff ℝ ∞ weight)
    (mode : ℤ) (field : ClosedJet dimension) :
    angularClosedJet mode (kernelRotationJet weight weightSmooth field) =
      kernelRotationJet weight weightSmooth (angularClosedJet mode field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have first : ∀ next : ClosedDisk,
      smoothClosedExtension (kernelRotationJet weight weightSmooth field) next.val =
        kernelRotationValue weight (smoothClosedExtension field) next.val :=
    fun next => smoothClosedExtension_value (kernelRotationJet weight weightSmooth field) next
  have second : ∀ next : ClosedDisk,
      smoothClosedExtension (angularClosedJet mode field) next.val =
        angularProjectionValue mode (smoothClosedExtension field) next.val :=
    fun next => smoothClosedExtension_value (angularClosedJet mode field) next
  change angularProjectionValue mode (smoothClosedExtension (kernelRotationJet weight weightSmooth field)) point.val =
    kernelRotationValue weight (smoothClosedExtension (angularClosedJet mode field)) point.val
  exact (angularProjectionValue_congr_closed mode first point).trans
    ((kernelRotation_projection weight weightSmooth.continuous _ (smoothClosedExtension_smooth field).continuous mode point.val).trans
      (kernelRotationValue_congr_closed weight second point).symm)

end Grad.ActualAngularInverse
