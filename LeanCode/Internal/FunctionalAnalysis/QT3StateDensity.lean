import QT2SourceDensity
import QR20Consumer

noncomputable section

namespace Grad.RealFixedRanges

open Grad.CartesianState Grad.Constraints Grad.SmoothingFamily Grad.AxisCore
open Grad.Cor18 Grad.CompletedReality

def stateRetraction (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    XAmbient parameters grade →L[ℝ] stateRange parameters parameter inside grade large :=
  realRetraction ((stateProjection parameters parameter inside grade large).restrictScalars ℝ)
    (xConjugation parameters grade).toContinuousLinearEquiv.toContinuousLinearMap
    (stateProjection_idempotent parameters parameter inside grade large)
    (xConjugation_involutive parameters grade)
    (fun point => (canonicalStateProjection_conjugate parameters parameter inside grade large point).symm)

theorem stateRetraction_surjective (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    Function.Surjective (stateRetraction parameters parameter inside grade large) :=
  realRetraction_surjective _ _ _ _ _

def stateRealApproximation (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : StateCore parameters) : StateCore parameters :=
  (1 / 2 : ℝ) • (fullProjection parameters parameter inside field +
    xCoreConjugation parameters (fullProjection parameters parameter inside field))

theorem stateRetraction_eta (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (field : StateCore parameters) :
    (stateRetraction parameters parameter inside grade large (stateToGrade parameters grade field)).val =
      stateToGrade parameters grade (stateRealApproximation parameters parameter inside field) := by
  change (1 / 2 : ℝ) •
    (stateProjection parameters parameter inside grade large (stateToGrade parameters grade field) +
      xConjugation parameters grade
        (stateProjection parameters parameter inside grade large (stateToGrade parameters grade field))) = _
  rw [stateProjection_core, xConjugation_eta]
  change _ = ((stateToGrade parameters grade).restrictScalars ℝ)
    ((1 / 2 : ℝ) • (fullProjection parameters parameter inside field +
      xCoreConjugation parameters (fullProjection parameters parameter inside field)))
  rw [map_smul, map_add]
  rfl

theorem stateRealApproximation_mem (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade)
    (field : StateCore parameters) :
    stateRealApproximation parameters parameter inside field ∈ stateSmoothRange parameters parameter inside := by
  apply (stateToGrade_mem_iff parameters parameter inside grade large _).1
  rw [← stateRetraction_eta]
  exact (stateRetraction parameters parameter inside grade large (stateToGrade parameters grade field)).property

/-- Density of the actual smooth real constrained state core, using the
proved seed-dependent projection and its real involution. -/
theorem stateSmoothEmbedding_denseRange (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (grade : ℕ) (large : 3 ≤ grade) :
    DenseRange (stateSmoothEmbedding parameters parameter inside grade large) := by
  have dense := (stateRetraction_surjective parameters parameter inside grade large).denseRange.comp
    (stateToGrade_denseRange parameters grade)
    (stateRetraction parameters parameter inside grade large).continuous
  apply dense.mono
  rintro _ ⟨field, rfl⟩
  refine ⟨⟨stateRealApproximation parameters parameter inside field,
    stateRealApproximation_mem parameters parameter inside grade large field⟩, ?_⟩
  apply Subtype.ext
  exact (stateRetraction_eta parameters parameter inside grade large field).symm

end Grad.RealFixedRanges
