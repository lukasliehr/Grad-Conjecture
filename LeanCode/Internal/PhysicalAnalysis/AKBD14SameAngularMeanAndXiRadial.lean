import AKBD13SameAngularForceComponents

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualDeterminantEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.ActualSmoothPhysicalField
open Grad.BoundaryTrace Grad.SourceCollarFullSource Grad.ActualPolarEquations
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularSourceGraph
open Grad.AnnularGeneralSourceRegularity Grad.AnnularHighGenerators Grad.SourceBoundaryTrace

/-- Every actual angular derivative has zero circular mean. -/
theorem sameScalarAngular_meanFree {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1) (component : Fin dimension) (radius : ℝ) (inside : radius ∈ Ioo lower 1) (angles : ℝ × ℝ) :
    removePolarMean (fun query => scalarDirectionalField curves bounded component (0,1,0) (radius,query)) angles =
      scalarDirectionalField curves bounded component (0,1,0) (radius,angles) := by
  have fieldContinuous : Continuous (fun polar => curves.fullField bounded (radius,polar,angles.2) component) :=
    (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin dimension => ℂ) component).continuous.comp
      ((curves.fullField_continuous_angles bounded radius ⟨inside.1.le,inside.2.le⟩).comp (continuous_id.prodMk continuous_const))
  have derivativeContinuous := (scalarDirectionalField_continuous_angles curves bounded component (0,1,0) radius inside).comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => angles.2)))
  have periodic := congrArg (fun value : ComplexEuclidean dimension => value component)
    (curves.fullField_angular_periodic bounded radius angles.2 (-Real.pi))
  have endpoint : curves.fullField bounded (radius,Real.pi,angles.2) component =
      curves.fullField bounded (radius,-Real.pi,angles.2) component := by
    simpa only [show -Real.pi + (2 * Real.pi) = Real.pi by ring] using periodic
  have mean := angularCoefficient_scalar_derivative _ _ fieldContinuous derivativeContinuous
    (fun polar => scalarPolar_hasDerivAt curves bounded component radius inside polar angles.2) endpoint 0
  simp only [Int.cast_zero,mul_zero,zero_mul] at mean
  exact sub_eq_self.mpr mean

variable (parameters : PhaseParameters) (length lower : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (solution : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade solution weighted)
    (smooth : ∀ grade, ContDiffOn ℝ ∞
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive solution grade) (Icc lower 1))
    (curves : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data solution))

include allGrades smooth

/-- The SAME Xi has the genuine product derivative q+r q_r. -/
theorem samePhysicalXi_scalarRadial (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ) :
    HasDerivAt (fun location => originalPhysicalComponentField parameters lower length positive bounded lengthPositive solution 1
      (location,polar,axial) 0)
      (curves.fullField bounded (radius,polar,axial) 3 +
        (radius : ℂ) * scalarDirectionalField curves bounded 3 (1,0,0) (radius,polar,axial)) radius := by
  have product := ((hasDerivAt_id radius).ofReal_comp).mul (scalarRadial_hasDerivAt curves bounded 3 radius inside polar axial)
  simp only [Complex.ofReal_one,one_mul,id_eq] at product
  apply product.congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds inside.1 inside.2] with location member
  have same := congrArg (fun value : ComplexEuclidean 1 => value 0)
    (fullSeven_physicalXiOverRadius parameters lower length positive bounded lengthPositive data solution allGrades smooth curves
      location ⟨member.1.le,member.2.le⟩ (polar,axial))
  rw [fullField_bulkUnit_zero_scalar curves bounded 3 location ⟨member.1.le,member.2.le⟩] at same
  change curves.fullField bounded (location,polar,axial) 3 = (location : ℂ)⁻¹ *
    originalPhysicalComponentField parameters lower length positive bounded lengthPositive solution 1 (location,polar,axial) 0 at same
  change _ = (location : ℂ) * curves.fullField bounded (location,polar,axial) 3
  rw [same,mul_inv_cancel_left₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (positive.trans member.1)))]

end Grad.ActualDeterminantEquations
