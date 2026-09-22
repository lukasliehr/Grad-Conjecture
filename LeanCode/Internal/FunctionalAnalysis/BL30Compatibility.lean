import BL29Completion
import COR16Consumer

noncomputable section

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints
  Grad.CompatibleCompletion

def boundaryCoefficientCLM {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (mode : ℤ × ℤ) :
    BoundaryGrade parameters (ComplexEuclidean dimension) grade →L[ℂ] ComplexEuclidean dimension :=
  (boundaryWeight parameters grade mode : ℂ)⁻¹ •
    lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode

theorem boundaryCoefficientCLM_apply {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (mode : ℤ × ℤ) (values : BoundaryGrade parameters (ComplexEuclidean dimension) grade) :
    boundaryCoefficientCLM parameters grade mode values = boundaryCoefficient parameters grade values mode := rfl

/-- A continuous realization of boundary grade inclusion. The coefficient
law below identifies it with the literal unchanged raw coefficient sequence. -/
def boundaryGradeInclusion {dimension lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (lowerPositive : 1 ≤ lower) :
    BoundaryGrade parameters (ComplexEuclidean dimension) upper →L[ℂ]
      BoundaryGrade parameters (ComplexEuclidean dimension) lower :=
  (completedTrace parameters lower lowerPositive).comp
    ((completedInclusion parameters ordered).comp
      (completedBoundaryLift parameters upper (lowerPositive.trans ordered)))

theorem boundaryGradeInclusion_finite {dimension lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (lowerPositive : 1 ≤ lower) (values : FiniteBoundaryData dimension) :
    boundaryGradeInclusion parameters ordered lowerPositive
      (finiteBoundaryToGrade parameters upper (lowerPositive.trans ordered) values) =
        finiteBoundaryToGrade parameters lower lowerPositive values := by
  simp only [boundaryGradeInclusion, ContinuousLinearMap.comp_apply,
    completedBoundaryLift_finite, completedInclusion_apply_eta, GradeCore.toCore_ofCore,
    finiteLiftLinear_completed_trace]

theorem boundaryGradeInclusion_coefficient {dimension lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (lowerPositive : 1 ≤ lower)
    (values : BoundaryGrade parameters (ComplexEuclidean dimension) upper) (mode : ℤ × ℤ) :
    boundaryCoefficient parameters lower (boundaryGradeInclusion parameters ordered lowerPositive values) mode =
      boundaryCoefficient parameters upper values mode := by
  have equalFunctions := (finiteBoundaryToGrade_dense (dimension := dimension) parameters upper
    (lowerPositive.trans ordered)).equalizer
      ((boundaryCoefficientCLM parameters lower mode).comp
        (boundaryGradeInclusion parameters ordered lowerPositive)).continuous
      (boundaryCoefficientCLM (dimension := dimension) parameters upper mode).continuous (by
        funext data
        simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
          boundaryGradeInclusion_finite, boundaryCoefficientCLM_apply, finiteBoundaryToGrade_coefficient])
  exact congrFun equalFunctions values

theorem boundaryGradeInclusion_core {dimension lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (lowerPositive : 1 ≤ lower) (values : BoundaryCore parameters dimension) :
    boundaryGradeInclusion parameters ordered lowerPositive
      (boundaryToGrade parameters upper (lowerPositive.trans ordered) values) =
        boundaryToGrade parameters lower lowerPositive values := by
  apply Subtype.ext
  funext mode
  rw [← boundary_weighted_coefficient parameters lower
    (boundaryGradeInclusion parameters ordered lowerPositive
      (boundaryToGrade parameters upper (lowerPositive.trans ordered) values)) mode,
    ← boundary_weighted_coefficient parameters lower (boundaryToGrade parameters lower lowerPositive values) mode,
    boundaryGradeInclusion_coefficient, boundaryToGrade_coefficient, boundaryToGrade_coefficient]

theorem completedBoundaryLift_compatible {dimension lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (lowerPositive : 1 ≤ lower) :
    (completedInclusion parameters ordered).comp
      (completedBoundaryLift (dimension := dimension) parameters upper (lowerPositive.trans ordered)) =
        (completedBoundaryLift parameters lower lowerPositive).comp
          (boundaryGradeInclusion parameters ordered lowerPositive) := by
  apply DFunLike.ext
  have equalFunctions := (finiteBoundaryToGrade_dense (dimension := dimension) parameters upper
    (lowerPositive.trans ordered)).equalizer
      ((completedInclusion parameters ordered).comp
        (completedBoundaryLift parameters upper (lowerPositive.trans ordered))).continuous
      ((completedBoundaryLift parameters lower lowerPositive).comp
        (boundaryGradeInclusion parameters ordered lowerPositive)).continuous (by
        funext data
        simp only [Function.comp_apply, ContinuousLinearMap.comp_apply,
          completedBoundaryLift_finite, boundaryGradeInclusion_finite,
          completedInclusion_apply_eta, GradeCore.toCore_ofCore])
  exact congrFun equalFunctions

theorem completedBoundaryLift_core_compatible {dimension lower upper : ℕ} (parameters : PhaseParameters)
    (ordered : lower ≤ upper) (lowerPositive : 1 ≤ lower) (values : BoundaryCore parameters dimension) :
    completedInclusion parameters ordered
      (completedBoundaryLift parameters upper (lowerPositive.trans ordered)
        (boundaryToGrade parameters upper (lowerPositive.trans ordered) values)) =
      completedBoundaryLift parameters lower lowerPositive
        (boundaryToGrade parameters lower lowerPositive values) := by
  have equality := DFunLike.congr_fun (completedBoundaryLift_compatible parameters ordered lowerPositive)
    (boundaryToGrade parameters upper (lowerPositive.trans ordered) values)
  simpa only [ContinuousLinearMap.comp_apply, boundaryGradeInclusion_core] using equality

end Grad.BoundaryLift
