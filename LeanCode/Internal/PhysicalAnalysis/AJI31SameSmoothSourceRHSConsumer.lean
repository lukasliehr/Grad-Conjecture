import AJI30ActualFullRadialRHS
import AJQ3SameSmoothSourceContinuousSolution

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularStrongSolution
open Grad.AnnularSourceGraph Grad.AnnularStrongData Grad.AnnularStrongOrbit
open Grad.GaugeCoefficients.Physical.Allocation

/-- All Fourier grades describe the SAME full RHS. This is an AE equality
derived from its literal physical coefficient formula, with no derivative premise. -/
theorem originalRadialSystemRHS_coefficient_grade
    (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (field : CoupledSpace lower length positive lengthPositive)
    (core : OriginalSmoothSourceCore parameters)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (grade : ℕ) :
    ∀ᵐ (radius : ℝ) ∂volume.restrict (Icc lower (1 : ℝ)), ∀ mode : ℤ × ℤ,
      ((originalRadialSystemRHS parameters length compact lower positive bounded lengthPositive state field core grade radius).1 mode,
       (originalRadialSystemRHS parameters length compact lower positive bounded lengthPositive state field core grade radius).2 mode) =
      ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        ((originalRadialSystemRHS parameters length compact lower positive bounded lengthPositive state field core 0 radius).1 mode,
         (originalRadialSystemRHS parameters length compact lower positive bounded lengthPositive state field core 0 radius).2 mode) := by
  filter_upwards [originalRadialSystemRHS_actual parameters length compact lower positive bounded lengthPositive state field core allGrades grade,
    originalRadialSystemRHS_actual parameters length compact lower positive bounded lengthPositive state field core allGrades 0] with radius graded base
  intro mode
  have baseSame := base mode
  simp only [pow_zero, Complex.ofReal_one, one_smul] at baseSame
  exact (graded mode).trans
    (congrArg (fun value => ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) • value) baseSame.symm)

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters length compact)
    (core : OriginalSmoothSourceCore parameters)

/-- Exact full RHS coefficients for the actual shared inverse of the
original smooth source on the unchanged B8 ball and analytic widths. -/
theorem originalSmoothSourceRHS_actual (grade : ℕ) :
    let bounded : lower < 1 := lowerHalf.trans_lt (by norm_num)
    let field := originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core
    ∀ᵐ (radius : ℝ) ∂volume.restrict (Icc lower (1 : ℝ)), ∀ mode : ℤ × ℤ,
      ((originalRadialSystemRHS parameters length compact lower positive bounded lengthPositive state field core grade radius).1 mode,
       (originalRadialSystemRHS parameters length compact lower positive bounded lengthPositive state field core grade radius).2 mode) =
      ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        actualOriginalFullRHS parameters length compact lower positive bounded lengthPositive state field core radius mode :=
  originalRadialSystemRHS_actual parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state
    (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) core
    (originalSmoothSourceResponse_allGrades parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) grade

/-- The actual full RHS at any polynomial grade is the fixed frequency
multiple of grade zero for the SAME shared smooth-source response. -/
theorem originalSmoothSourceRHS_coefficient_grade (grade : ℕ) :
    let bounded : lower < 1 := lowerHalf.trans_lt (by norm_num)
    let field := originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state small core
    ∀ᵐ (radius : ℝ) ∂volume.restrict (Icc lower (1 : ℝ)), ∀ mode : ℤ × ℤ,
      ((originalRadialSystemRHS parameters length compact lower positive bounded lengthPositive state field core grade radius).1 mode,
       (originalRadialSystemRHS parameters length compact lower positive bounded lengthPositive state field core grade radius).2 mode) =
      ((annularFrequency mode.1 mode.2 ^ grade : ℝ) : ℂ) •
        ((originalRadialSystemRHS parameters length compact lower positive bounded lengthPositive state field core 0 radius).1 mode,
         (originalRadialSystemRHS parameters length compact lower positive bounded lengthPositive state field core 0 radius).2 mode) :=
  originalRadialSystemRHS_coefficient_grade parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) lengthPositive state
    (originalSmoothSourceResponse parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) core
    (originalSmoothSourceResponse_allGrades parameters length compact lower positive lowerHalf lengthPositive widthHalf widthLength state small core) grade

end Grad.AnnularSmoothCore
