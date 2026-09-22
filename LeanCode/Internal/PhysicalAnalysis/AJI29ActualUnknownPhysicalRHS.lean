import AJI28UnknownPhysicalRHSAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularCurrentLow
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularStrongSolution
open Grad.AnnularSourceGraph Grad.AnnularRadialSmoothness Grad.AnnularSmoothSources

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (field : CoupledSpace lower length positive lengthPositive)

/-- The original homogeneous radial system acting on the SAME field, with
literal original physical j/c/rV rows and the unweighted physical x. -/
def actualOriginalUnknownRHS (radius : ℝ) (mode : ℤ × ℤ) :
    ComplexEuclidean 1 × ComplexEuclidean 1 :=
  let row := fun index : Fin 3 => lowRhoPhysicalCoefficient parameters lower positive
    (lowPhysicalRowAction parameters length compact lower positive bounded.le state index
      (homogeneousCoupledSevenInput parameters length lower lengthPositive positive field)) radius mode
  rawOriginalUnknownRHS length radius mode
    (sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0
      (radialClamp lower bounded.le radius) mode) (row 0) (row 1) (row 2)

variable (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
include allGrades

/-- Each polynomial Hilbert coefficient is exactly the original unknown
physical RHS. This uses the actual all-grade field and the actual row action. -/
theorem originalRadialSystemOperator_actual (grade : ℕ) :
    ∀ᵐ (radius : ℝ) ∂volume.restrict (Icc lower (1 : ℝ)), ∀ mode : ℤ × ℤ,
      let input :=
        (sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive (grade + 2) field
          (radialClamp lower bounded.le radius),
         sameCoupledPhysicalXiSection parameters lower length positive bounded lengthPositive (grade + 2) field
          (radialClamp lower bounded.le radius))
      let output := originalRadialSystemOperator parameters length compact lower state positive bounded grade radius input
      (output.1 mode, output.2 mode) =
        ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
          actualOriginalUnknownRHS parameters length compact lower positive bounded lengthPositive state field radius mode := by
  have sameX : ∀ᵐ (radius : ℝ) ∂volume.restrict (Icc lower (1 : ℝ)), ∀ mode : ℤ × ℤ,
      sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive (grade + 2) field
        (radialClamp lower bounded.le radius) mode =
      (Grad.AnnularVariational.annularFrequency mode.1 mode.2 : ℂ) ^ (grade + 2) •
        sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0
          (radialClamp lower bounded.le radius) mode := by
    exact Filter.Eventually.of_forall fun radius mode => by
      rw [sameCoupledPhysicalXSection_coefficient parameters lower length positive bounded lengthPositive field allGrades,
        sameCoupledXCoefficient_grade parameters lower length positive bounded lengthPositive field]
      rw [Complex.ofReal_pow]
  have actual := unknownFrequency_ae length lower grade
    (fun index radius mode => sameUnknownPhysicalRowCurve parameters lower length compact positive bounded lengthPositive state field index grade radius mode)
    (fun index radius mode => lowRhoPhysicalCoefficient parameters lower positive
      (lowPhysicalRowAction parameters length compact lower positive bounded.le state index
        (homogeneousCoupledSevenInput parameters length lower lengthPositive positive field)) radius mode)
    (fun radius mode => sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive (grade + 2) field
      (radialClamp lower bounded.le radius) mode)
    (fun radius mode => sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0
      (radialClamp lower bounded.le radius) mode)
    (fun index => sameUnknownPhysicalRowCurve_actual parameters lower length compact positive bounded lengthPositive state field allGrades index grade)
    sameX
  filter_upwards [actual] with radius same
  intro mode
  exact (originalRadialSystemOperator_coefficient parameters lower length compact positive bounded state grade radius
    (sameCoupledPhysicalXSection parameters lower length positive bounded lengthPositive (grade + 2) field
      (radialClamp lower bounded.le radius),
     sameCoupledPhysicalXiSection parameters lower length positive bounded lengthPositive (grade + 2) field
      (radialClamp lower bounded.le radius)) mode).trans (same mode)

end Grad.AnnularSmoothCore
