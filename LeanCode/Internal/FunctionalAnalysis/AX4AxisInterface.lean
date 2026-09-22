import AX3AxisStructure

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.AxisCore

open Grad.ClosedJets Grad.CartesianState

/-- The exact COR08 goal: the grade-`q` axis carrier is the literal weighted
sequence Hilbert space with exactly the M16 norm of its coefficients; the
weight multiplication identifies it isometrically with plain `l2`; the single
all-grade axis coefficient core embeds with the same coefficients at every
grade, injectively, with the exact norm and finite-support density; the real
involution is involutive, additive, conjugate-linear, isometric, compatible
with the core and the inclusions; and the same-coefficient inclusions are
contractive and injective. -/
def AxisGradeGoal : Prop :=
  ∀ (parameters : PhaseParameters) (valueDimension : ℕ) (grade : ℕ),
    (∀ field : AxisGrade parameters valueDimension grade,
      ‖field‖ ^ 2 = ∑' cell : ℤ,
        Real.exp (2 * parameters.sigma0 * cellFrequency cell) *
          cellFrequency cell ^ (2 * grade) *
            ‖axisCoefficient parameters grade field cell‖ ^ 2) ∧
    (∀ field : AxisGrade parameters valueDimension grade,
      (∀ cell, (axisWeight parameters grade cell : ℂ) •
          axisCoefficient parameters grade field cell = field cell) ∧
        ‖field‖ ^ 2 = ∑' cell : ℤ, ‖(axisWeight parameters grade cell : ℂ) •
          axisCoefficient parameters grade field cell‖ ^ 2) ∧
    (∀ family : AxisSmoothCore parameters valueDimension,
      (∀ cell, axisCoefficient parameters grade
          (axisEta parameters valueDimension grade family) cell = family.1 cell) ∧
        ‖axisEta parameters valueDimension grade family‖ ^ 2 =
          ∑' cell : ℤ, axisWeight parameters grade cell ^ 2 * ‖family.1 cell‖ ^ 2) ∧
    (∀ first second : AxisSmoothCore parameters valueDimension,
      axisEta parameters valueDimension grade first =
        axisEta parameters valueDimension grade second → first = second) ∧
    (∀ field : AxisGrade parameters valueDimension grade,
      axisInvolution parameters valueDimension grade
          (axisInvolution parameters valueDimension grade field) = field ∧
        ‖axisInvolution parameters valueDimension grade field‖ = ‖field‖) ∧
    (∀ first second : AxisGrade parameters valueDimension grade,
      axisInvolution parameters valueDimension grade (first + second) =
        axisInvolution parameters valueDimension grade first +
          axisInvolution parameters valueDimension grade second) ∧
    (∀ (scalar : ℂ) (field : AxisGrade parameters valueDimension grade),
      axisInvolution parameters valueDimension grade (scalar • field) =
        (starRingEnd ℂ) scalar • axisInvolution parameters valueDimension grade field) ∧
    (∀ family : AxisSmoothCore parameters valueDimension,
      axisCoreInvolution parameters valueDimension
          (axisCoreInvolution parameters valueDimension family) = family ∧
        axisEta parameters valueDimension grade
            (axisCoreInvolution parameters valueDimension family) =
          axisInvolution parameters valueDimension grade
            (axisEta parameters valueDimension grade family)) ∧
    (∀ field : AxisGrade parameters valueDimension grade, ∀ epsilon : ℝ,
      0 < epsilon →
        ∃ core : AxisSmoothCore parameters valueDimension,
          (∃ support : Finset ℤ, ∀ cell ∉ support, core.1 cell = 0) ∧
            ‖field - axisEta parameters valueDimension grade core‖ < epsilon) ∧
    (∀ field : AxisGrade parameters valueDimension (grade + 1),
      (∀ cell, axisCoefficient parameters grade
          (axisInclusion parameters valueDimension grade field) cell =
        axisCoefficient parameters (grade + 1) field cell) ∧
        ‖axisInclusion parameters valueDimension grade field‖ ≤ ‖field‖) ∧
    (∀ first second : AxisGrade parameters valueDimension (grade + 1),
      axisInclusion parameters valueDimension grade first =
        axisInclusion parameters valueDimension grade second → first = second) ∧
    (∀ field : AxisGrade parameters valueDimension (grade + 1),
      axisInvolution parameters valueDimension grade
          (axisInclusion parameters valueDimension grade field) =
        axisInclusion parameters valueDimension grade
          (axisInvolution parameters valueDimension (grade + 1) field))

end Grad.AxisCore
