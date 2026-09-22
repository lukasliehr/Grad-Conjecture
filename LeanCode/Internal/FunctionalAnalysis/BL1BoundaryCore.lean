import BTConsumer

noncomputable section

open scoped BigOperators

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace

/-- Original boundary coefficients belonging to every positive half-order grade. -/
def boundaryCoreSubmodule (parameters : PhaseParameters) (dimension : ℕ) :
    Submodule ℂ (ℤ × ℤ → ComplexEuclidean dimension) where
  carrier values := ∀ grade : ℕ, 1 ≤ grade →
    Memℓp (fun mode => (boundaryWeight parameters grade mode : ℂ) • values mode) 2
  zero_mem' := by
    intro grade _
    convert (zero_memℓp : Memℓp (0 : ℤ × ℤ → ComplexEuclidean dimension) 2) using 1
    funext mode
    exact smul_zero _
  add_mem' := by
    intro first second firstMember secondMember grade gradePositive
    convert (firstMember grade gradePositive).add (secondMember grade gradePositive) using 1
    funext mode
    exact smul_add _ _ _
  smul_mem' := by
    intro scalar values member grade gradePositive
    convert (member grade gradePositive).const_smul scalar using 1
    funext mode
    simp only [Pi.smul_apply, smul_smul]
    rw [mul_comm]

abbrev BoundaryCore (parameters : PhaseParameters) (dimension : ℕ) :=
  boundaryCoreSubmodule parameters dimension

def boundaryToGrade {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) :
    BoundaryCore parameters dimension →ₗ[ℂ] BoundaryGrade parameters (ComplexEuclidean dimension) grade where
  toFun values := ⟨fun mode => (boundaryWeight parameters grade mode : ℂ) • values.1 mode,
    values.property grade gradePositive⟩
  map_add' first second := by apply Subtype.ext; funext mode; exact smul_add _ _ _
  map_smul' scalar values := by
    apply Subtype.ext
    funext mode
    change (boundaryWeight parameters grade mode : ℂ) • (scalar • values.1 mode) =
      scalar • ((boundaryWeight parameters grade mode : ℂ) • values.1 mode)
    exact smul_comm _ _ _

theorem boundaryToGrade_coefficient {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (values : BoundaryCore parameters dimension) (mode : ℤ × ℤ) :
    boundaryCoefficient parameters grade (boundaryToGrade parameters grade gradePositive values) mode =
      values.1 mode := by
  exact inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (boundaryWeight_pos parameters grade mode).ne') _

theorem boundaryToGrade_norm_sq {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ)
    (gradePositive : 1 ≤ grade) (values : BoundaryCore parameters dimension) :
    ‖boundaryToGrade parameters grade gradePositive values‖ ^ 2 =
      ∑' mode : ℤ × ℤ, Real.exp (2 * boundaryPhase parameters mode.2) *
        boundaryFrequency mode ^ (2 * grade - 1) * ‖values.1 mode‖ ^ 2 := by
  simpa only [boundaryToGrade_coefficient] using
    boundary_norm_sq parameters grade (boundaryToGrade parameters grade gradePositive values)

def BoundaryReality {dimension : ℕ} (parameters : PhaseParameters)
    (values : BoundaryCore parameters dimension) : Prop :=
  ∀ mode : ℤ × ℤ, values.1 (-mode.1, -mode.2) = cartesianPhysicalConjugation dimension (values.1 mode)

def HighBoundarySupport {dimension : ℕ} (parameters : PhaseParameters)
    (values : BoundaryCore parameters dimension) : Prop :=
  ∀ mode : ℤ × ℤ, |mode.1| ≤ 2 → values.1 mode = 0

/-- The literal N24 summand, before any phase conjugation. -/
def boundaryLiftSummand {dimension : ℕ} (values : ℤ × ℤ → ComplexEuclidean dimension)
    (time : ℝ) (angle cell : CellCircle) (mode : ℤ × ℤ) : ComplexEuclidean dimension :=
  ((Real.exp (-boundaryFrequency mode * time) : ℂ) * fourier mode.1 angle * fourier mode.2 cell) •
    values mode

def literalBoundaryLift {dimension : ℕ} (values : ℤ × ℤ → ComplexEuclidean dimension)
    (time : ℝ) (angle cell : CellCircle) : ComplexEuclidean dimension :=
  collarCutoff1D time • ∑' mode : ℤ × ℤ, boundaryLiftSummand values time angle cell mode

def literalBoundaryCell {dimension : ℕ} (values : ℤ × ℤ → ComplexEuclidean dimension)
    (time : ℝ) (angle : CellCircle) (cell : ℤ) : ComplexEuclidean dimension :=
  collarCutoff1D time • ∑' mode : ℤ,
    ((Real.exp (-boundaryFrequency (mode, cell) * time) : ℂ) * fourier mode angle) • values (mode, cell)

end Grad.BoundaryLift
