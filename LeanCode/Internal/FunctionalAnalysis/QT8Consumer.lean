import QT7Goal

noncomputable section

namespace Grad.RealFixedRanges

open Grad.CartesianState Grad.Constraints Grad.AxisCore Grad.SmoothingFamily
open Grad.QuotientProjection

/-- Concrete approximation in the actual ambient sum norm, obtained from
the public theorem's density clause without assuming constrained density. -/
theorem stateRealCore_approximates (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (target : stateRange parameters parameter inside grade large) (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ field : stateSmoothRange parameters parameter inside,
      ‖target.val - stateToGrade parameters grade field.val‖ < epsilon := by
  obtain ⟨field, close⟩ := Metric.denseRange_iff.mp
    (actualRealConstrainedDensity parameters parameter inside grade large).1 target epsilon positive
  rw [dist_comm, stateApproximation_error, norm_sub_rev] at close
  exact ⟨field, close⟩

/-- Concrete approximation in the original fourfold Hilbert norm. -/
theorem sourceRealCore_approximates (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade)
    (target : sourceRange parameters grade large) (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ field : sourceSmoothRange parameters,
      ‖target.val - quotientEta parameters grade field.val‖ < epsilon := by
  obtain ⟨field, close⟩ := Metric.denseRange_iff.mp
    (sourceSmoothEmbedding_denseRange parameters grade large) target epsilon positive
  rw [dist_comm, sourceApproximation_error, norm_sub_rev] at close
  exact ⟨field, close⟩

/-- The canonical completion map has the actual state embedding as its
ambient restriction, not an arbitrary isometry between abstract carriers. -/
theorem stateCompletion_ambient_core (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (field : stateSmoothRange parameters parameter inside) :
    stateInclusion parameters parameter inside grade large
      (stateCompletionEquiv parameters parameter inside grade large
        (stateCoreToCompletion parameters parameter inside grade large field)) =
      stateToGrade parameters grade field.val := by
  rw [stateCompletionEquiv_core]
  rfl

theorem sourceCompletion_ambient_core (parameters : PhaseParameters) (grade : ℕ) (large : 3 ≤ grade)
    (field : sourceSmoothRange parameters) :
    sourceInclusion parameters grade large
      (sourceCompletionEquiv parameters grade large (sourceCoreToCompletion parameters grade large field)) =
      quotientEta parameters grade field.val := by
  rw [sourceCompletionEquiv_core]
  rfl

/-- The state core copy has exactly the original axis-q+1, vector-q,
scalar-q sum norm. -/
theorem stateGradeCore_original_sum_norm (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (field : StateGradeCore parameters parameter inside grade large) :
    ‖field‖ = ‖Grad.SmoothingFamily.axisToGrade parameters.sigma0 (grade + 1) field.toCore.val.1‖ +
      ‖aGradeEta (grade := grade) parameters (GradeCore.ofCoreLinear field.toCore.val.2.1)‖ +
        ‖aGradeEta (grade := grade) parameters (GradeCore.ofCoreLinear field.toCore.val.2.2)‖ := by
  rw [stateGradeCore_norm, stateToGrade_embedded_norm]

end Grad.RealFixedRanges
