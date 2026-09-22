import ANS2KernelCommutation

noncomputable section
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff Interval Topology
namespace Grad.ActualAngularInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.PhysicalFamily Grad.GaugeCoefficients.Radial Grad.ActualSmoothPDE

theorem kernelRotationIntegrand_smooth {dimension : ℕ} (weight : ℝ → ℂ)
    (weightSmooth : ContDiff ℝ ∞ weight)
    {field : SpatialPlane → ComplexEuclidean dimension} (smooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (fun argument : SpatialPlane × ℝ =>
      weight argument.2 • field (planeRotationAction argument.2 argument.1)) :=
  (weightSmooth.comp contDiff_snd).smul (smooth.comp cartesianRotation_smooth)

theorem kernelRotationValue_derivative {dimension order : ℕ} (weight : ℝ → ℂ) (weightSmooth : ContDiff ℝ ∞ weight)
    {field : SpatialPlane → ComplexEuclidean dimension} (smooth : ContDiff ℝ ∞ field)
    (word : CartesianWord order) (point : SpatialPlane) :
    cartesianDerivative order word (kernelRotationValue weight field) point =
      (2 * Real.pi)⁻¹ • ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
        cartesianDerivative order word
          (fun source => weight angle • field (planeRotationAction angle source)) point := by
  let integrand : SpatialPlane × ℝ → ComplexEuclidean dimension := fun argument =>
    weight argument.2 • field (planeRotationAction argument.2 argument.1)
  have integrandSmooth : ContDiff ℝ ∞ integrand := kernelRotationIntegrand_smooth weight weightSmooth smooth
  have integralSmooth : ContDiff ℝ ∞
      (fun source => ∫ angle in Icc (0 : ℝ) (2 * Real.pi), integrand (source, angle)) :=
    contDiffOn_univ.mp (contDiffOn_compactIntegral isOpen_univ integrandSmooth.contDiffOn 0 (2 * Real.pi))
  have derivativeSmul := iteratedFDeriv_const_smul_apply (x := point) (a := ((2 * Real.pi)⁻¹ : ℝ))
    (integralSmooth.contDiffAt.of_le
      (WithTop.coe_le_coe.mpr (show (order : ℕ∞) ≤ ⊤ from le_top)))
  have functionEquality : kernelRotationValue weight field =
      fun source => (2 * Real.pi)⁻¹ •
        ∫ angle in Icc (0 : ℝ) (2 * Real.pi), integrand (source, angle) := by
    funext source
    rfl
  rw [functionEquality]
  exact (congrArg (fun derivative => derivative (fun position => spatialBasis (word position)))
      derivativeSmul).trans
    (congrArg (fun value => ((2 * Real.pi)⁻¹ : ℝ) • value)
      (cartesianDerivative_compactIntegral order word integrandSmooth 0 (2 * Real.pi) point))

theorem globalRotatedKernel_restricts {dimension : ℕ} (weight : ℝ → ℂ) (weightSmooth : ContDiff ℝ ∞ weight) (angle : ℝ)
    (field : ClosedJet dimension) :
    globalClosedJet
        (fun source => weight angle •
          smoothClosedExtension field (planeRotationAction angle source))
        ((kernelRotationIntegrand_smooth weight weightSmooth (smoothClosedExtension_smooth field)).comp
          (contDiff_id.prodMk contDiff_const)) =
      weight angle • orthogonalJet (planeRotationEquiv angle) field := by
  apply globalClosedJet_eq_of_restriction
  intro point
  change weight angle • smoothClosedExtension field (planeRotationAction angle point.val) =
    weight angle • field.value (orthogonalClosedPoint (planeRotationEquiv angle) point)
  rw [physicalRotation_eq_orthogonal]
  exact congrArg (fun value => weight angle • value)
    (smoothClosedExtension_value field (orthogonalClosedPoint (planeRotationEquiv angle) point))

theorem globalRotatedKernel_derivative {dimension order : ℕ} (weight : ℝ → ℂ) (weightSmooth : ContDiff ℝ ∞ weight) (angle : ℝ)
    (field : ClosedJet dimension) (word : CartesianWord order) (point : ClosedDisk) :
    cartesianDerivative order word
        (fun source => weight angle •
          smoothClosedExtension field (planeRotationAction angle source)) point.val =
      weight angle •
        orthogonalDerivative (planeRotationEquiv angle) field order word point := by
  have equality := globalRotatedKernel_restricts weight weightSmooth angle field
  have derivativeEquality := congrArg (fun jet => closedDerivative jet order word point) equality
  rw [globalClosedJet_derivative] at derivativeEquality
  change _ = closedDerivative (closedJetSmul (weight angle)
    (orthogonalJet (planeRotationEquiv angle) field)) order word point at derivativeEquality
  rw [closedJetSmul_derivative] at derivativeEquality
  change _ = weight angle •
    closedDerivative (orthogonalJet (planeRotationEquiv angle) field) order word point at derivativeEquality
  rw [orthogonalJet_derivative] at derivativeEquality
  exact derivativeEquality

/-- Every literal Cartesian derivative, including the boundary, commutes with
the specified angular projector. No extension norm enters this identity. -/
theorem kernelRotationJet_derivative {dimension order : ℕ} (weight : ℝ → ℂ) (weightSmooth : ContDiff ℝ ∞ weight)
    (field : ClosedJet dimension) (word : CartesianWord order) (point : ClosedDisk) :
    closedDerivative (kernelRotationJet weight weightSmooth field) order word point =
      (2 * Real.pi)⁻¹ • ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
        weight angle •
          orthogonalDerivative (planeRotationEquiv angle) field order word point := by
  rw [kernelRotationJet, globalClosedJet_derivative,
    kernelRotationValue_derivative weight weightSmooth (smoothClosedExtension_smooth field)]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro angle _
  exact globalRotatedKernel_derivative weight weightSmooth angle field word point

end Grad.ActualAngularInverse
