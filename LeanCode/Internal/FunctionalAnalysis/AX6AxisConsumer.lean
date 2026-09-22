import AX5AxisProof

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.AxisCore.Consumer

open Grad.ClosedJets Grad.CartesianState Grad.AxisCore

/-- The consumer-gate carrier identification: at value dimension two the
grade-`q` axis carrier IS the literal weighted sequence Hilbert space over
`EuclideanSpace ℂ (Fin 2)`, definitionally — not a scalar real placeholder. -/
theorem planar_carrier_literal (parameters : PhaseParameters) (grade : ℕ) :
    AxisGrade parameters 2 grade = lp (fun _ : ℤ => EuclideanSpace ℂ (Fin 2)) 2 := rfl

/-- The literal planar coefficient of a single-cell field: an actual
two-dimensional complex value flows through the weighted identification. -/
theorem planar_single_coefficient (parameters : PhaseParameters) (grade : ℕ)
    (cell : ℤ) (value : EuclideanSpace ℂ (Fin 2)) :
    axisCoefficient parameters grade
        (lp.single 2 cell value : AxisGrade parameters 2 grade) cell =
      ((axisWeight parameters grade cell : ℂ))⁻¹ • value := by
  unfold axisCoefficient
  rw [lp.single_apply_self]

/-- Immediate exact planar consumer of the accepted goal: the full M16 norm
identity, the isometric involution and the finite-support core density,
instantiated at the two-dimensional complex value space. -/
theorem planar_axis_ready (parameters : PhaseParameters) (grade : ℕ)
    (field : AxisGrade parameters 2 grade) (epsilon : ℝ) (positive : 0 < epsilon) :
    ‖field‖ ^ 2 = (∑' cell : ℤ,
      Real.exp (2 * parameters.sigma0 * cellFrequency cell) *
        cellFrequency cell ^ (2 * grade) *
          ‖axisCoefficient parameters grade field cell‖ ^ 2) ∧
    ‖axisInvolution parameters 2 grade field‖ = ‖field‖ ∧
    ∃ core : AxisSmoothCore parameters 2,
      (∃ support : Finset ℤ, ∀ cell ∉ support, core.1 cell = 0) ∧
        ‖field - axisEta parameters 2 grade core‖ < epsilon := by
  obtain ⟨normIdentity, -, -, -, involutionLaws, -, -, -, density, -, -, -⟩ :=
    actualAxisGrade parameters 2 grade
  exact ⟨normIdentity field, (involutionLaws field).2, density field epsilon positive⟩

/-- The contractive grade ladder at the planar value space: descending one
grade never increases the M16 norm, with the same coefficients. -/
theorem planar_inclusion_ladder (parameters : PhaseParameters) (grade : ℕ)
    (field : AxisGrade parameters 2 (grade + 1)) :
    (∀ cell, axisCoefficient parameters grade
        (axisInclusion parameters 2 grade field) cell =
      axisCoefficient parameters (grade + 1) field cell) ∧
      ‖axisInclusion parameters 2 grade field‖ ≤ ‖field‖ := by
  obtain ⟨-, -, -, -, -, -, -, -, -, inclusionLaws, -, -⟩ :=
    actualAxisGrade parameters 2 grade
  exact inclusionLaws field

end Grad.AxisCore.Consumer
