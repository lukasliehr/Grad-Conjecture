import AKCE3FullSourcedOuterSeven

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularSourceGraph Grad.AnnularCurrentSource Grad.BoundaryKernelAction Grad.PhaseAlgebra Grad.AnnularCrossMaps

 theorem originalEndpointLowering_coefficient (parameters : PhaseParameters) (angular : ℕ)
    (trace : AnnularTotalEndpointTrace parameters 1 1 angular 0 0) (mode : ℤ×ℤ) :
    sourceBoundaryCoefficient parameters 0
      (annularEndpointInclusion parameters 1 1 0 0 angular 0 (Nat.zero_le _) le_rfl trace) mode=
        totalEndpointCoefficient parameters 1 1 angular 0 0 trace mode := by
  unfold sourceBoundaryCoefficient
  rw [annularEndpointInclusion_apply]
  rw [← Complex.ofReal_inv,Complex.coe_smul,smul_smul]
  unfold totalEndpointCoefficient
  congr 1
  simp only [sourceBoundaryWeight,pow_zero,mul_one,sourceGradeRatio,totalEndpointWeight,
    sourceInsertedWeight,one_mul,splitTangentialWeight,div_eq_mul_inv]
  rw [boundaryPhase_at_outer]
  simp only [mul_inv_rev]

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (graphs : HighRadialSourceGraphs parameters lower 0)

 theorem originalGraphOuter_f0 (mode : ℤ×ℤ) :
    sourceBoundaryCoefficient parameters 0 (highGraphOuterTuple parameters lower positive bounded 0 graphs 0) mode=
      (Real.exp (radialPhase parameters 1 mode.2))⁻¹ •
        totalConjugatedSection parameters 1 lower positive bounded 1 0 0 graphs.1 mode ⟨1,bounded.le,le_rfl⟩ := by
  rw [highGraphOuterTuple_f0]
  change sourceBoundaryCoefficient parameters 0
    (annularEndpointInclusion parameters 1 1 0 0 1 0 _ _
      (totalSourceTrace parameters 1 lower positive bounded 1 0 0 1 graphs.1)) mode=_
  rw [originalEndpointLowering_coefficient]
  exact actualGRF10_physical_evaluation parameters 1 lower positive bounded 1 0 1 graphs.1 mode

 theorem originalGraphOuter_f2 (mode : ℤ×ℤ) :
    sourceBoundaryCoefficient parameters 0 (highGraphOuterTuple parameters lower positive bounded 0 graphs 2) mode=
      (Real.exp (radialPhase parameters 1 mode.2))⁻¹ •
        totalConjugatedSection parameters 1 lower positive bounded 0 0 0 graphs.2 mode ⟨1,bounded.le,le_rfl⟩ := by
  rw [highGraphOuterTuple_f2]
  have coefficient : sourceBoundaryCoefficient parameters 0
      (totalSourceTrace parameters 1 lower positive bounded 0 0 0 1 graphs.2) mode=
      totalEndpointCoefficient parameters 1 1 0 0 0
        (totalSourceTrace parameters 1 lower positive bounded 0 0 0 1 graphs.2) mode := by
    unfold sourceBoundaryCoefficient totalEndpointCoefficient sourceBoundaryWeight totalEndpointWeight sourceInsertedWeight splitTangentialWeight
    simp only [pow_zero,mul_one,one_mul,← Complex.ofReal_inv,Complex.coe_smul,boundaryPhase_at_outer]
  exact coefficient.trans (actualGRF10_physical_evaluation parameters 1 lower positive bounded 0 0 1 graphs.2 mode)

 theorem originalGraphOuter_rf0 (mode : ℤ×ℤ) :
    sourceBoundaryCoefficient parameters 0 (highGraphOuterTuple parameters lower positive bounded 0 graphs 1) mode=
      (Complex.I*(mode.1:ℂ)) • ((Real.exp (radialPhase parameters 1 mode.2))⁻¹ •
        totalConjugatedSection parameters 1 lower positive bounded 1 0 0 graphs.1 mode ⟨1,bounded.le,le_rfl⟩) := by
  rw [highGraphOuterTuple_rf0]
  have coefficient : sourceBoundaryCoefficient parameters 0
      (sourceRotationTrace parameters 1 lower positive bounded 0 0 1 graphs.1) mode=
      totalEndpointCoefficient parameters 1 1 0 0 0
        (sourceRotationTrace parameters 1 lower positive bounded 0 0 1 graphs.1) mode := by
    unfold sourceBoundaryCoefficient totalEndpointCoefficient sourceBoundaryWeight totalEndpointWeight sourceInsertedWeight splitTangentialWeight
    simp only [pow_zero,mul_one,one_mul,← Complex.ofReal_inv,Complex.coe_smul,boundaryPhase_at_outer]
  apply coefficient.trans
  have rotation := sourceRotationTrace_coefficient parameters 1 lower positive bounded 0 0 1 graphs.1 mode
  exact rotation.trans (congrArg (fun value : ComplexEuclidean 1 => (Complex.I*(mode.1:ℂ)) • value)
    (actualGRF10_physical_evaluation parameters 1 lower positive bounded 1 0 1 graphs.1 mode))

end Grad.OriginalCoreRealization
