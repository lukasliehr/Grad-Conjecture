import GaugeCoordinateCore

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers

variable (phase : PhaseParameters) (parameter : Seed.Parameters)

/-- The planar heart of the written N12 poloidal correction: `w ↦ M T (Mᵀ w)`. -/
def poloidalPlanarCore (inside : parameter ∈ Seed.parameterDomain) :
    ACore phase 2 →ₗ[ℂ] ACore phase 2 :=
  (seedMatrixCore phase parameter inside).comp
    ((tangentialCore phase).comp (seedTransposeCore phase parameter inside))

/-- The literal N12 poloidal gauge correction `C_p u = ι M T (Mᵀ u_⊥)`. -/
def poloidalCorrection (inside : parameter ∈ Seed.parameterDomain) :
    ACore phase 3 →ₗ[ℂ] ACore phase 3 :=
  (planarInclusionCore phase).comp
    ((poloidalPlanarCore phase parameter inside).comp (planarPartCore phase))

/-- The toroidal scalar part `Π u_T + L⁻¹ Π (u_⊥ · M' y)` of the written N12
toroidal correction. -/
def toroidalScalarCore (inside : parameter ∈ Seed.parameterDomain) :
    ACore phase 3 →ₗ[ℂ] ACore phase 1 :=
  (angularCore phase 0).comp
    (toroidalPartCore phase +
      (phase.length⁻¹ : ℂ) •
        ((derivativeDotCore phase parameter inside).comp (planarPartCore phase)))

/-- The literal N12 toroidal gauge correction
`C_t u = e_T (Π u_T + L⁻¹ Π (u_⊥ · M' y))`. -/
def toroidalCorrection (inside : parameter ∈ Seed.parameterDomain) :
    ACore phase 3 →ₗ[ℂ] ACore phase 3 :=
  (toroidalInclusionCore phase).comp (toroidalScalarCore phase parameter inside)

/-- The written-order N14 two-gauge projection `Q_g = (I - C_t)(I - C_p)`. -/
def triangularGaugeProjection (inside : parameter ∈ Seed.parameterDomain) :
    ACore phase 3 →ₗ[ℂ] ACore phase 3 :=
  triangularProjection (poloidalCorrection phase parameter inside)
    (toroidalCorrection phase parameter inside)

theorem poloidalCorrection_apply (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 3) :
    poloidalCorrection phase parameter inside field =
      planarInclusionCore phase (seedMatrixCore phase parameter inside
        (tangentialCore phase (seedTransposeCore phase parameter inside
          (planarPartCore phase field)))) := rfl

theorem toroidalCorrection_apply (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 3) :
    toroidalCorrection phase parameter inside field =
      toroidalInclusionCore phase (angularCore phase 0
        (toroidalPartCore phase field +
          (phase.length⁻¹ : ℂ) • derivativeDotCore phase parameter inside
            (planarPartCore phase field))) := rfl

/-- The toroidal correction has literally zero planar part. -/
theorem toroidalCorrection_planar_part (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 3) :
    planarPartCore phase (toroidalCorrection phase parameter inside field) = 0 :=
  planarPartCore_toroidalInclusionCore phase _

/-- The written cross law `C_p C_t = 0`: the poloidal correction annihilates
every toroidal correction output. -/
theorem poloidal_toroidal_cross (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 3) :
    poloidalCorrection phase parameter inside
        (toroidalCorrection phase parameter inside field) = 0 := by
  rw [poloidalCorrection_apply, toroidalCorrection_planar_part]
  rw [map_zero, map_zero, map_zero, map_zero]

/-- The toroidal correction is idempotent: `C_t² = C_t`, using only the
toroidal mean projection law. -/
theorem toroidalCorrection_idempotent (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 3) :
    toroidalCorrection phase parameter inside
        (toroidalCorrection phase parameter inside field) =
      toroidalCorrection phase parameter inside field := by
  rw [toroidalCorrection_apply phase parameter inside field]
  set scalarPart := angularCore phase 0
    (toroidalPartCore phase field +
      (phase.length⁻¹ : ℂ) • derivativeDotCore phase parameter inside
        (planarPartCore phase field)) with scalarPart_def
  rw [toroidalCorrection_apply]
  rw [toroidalPartCore_toroidalInclusionCore, planarPartCore_toroidalInclusionCore,
    map_zero, smul_zero, add_zero]
  have idempotent := angularCore_projection phase 0 0 (toroidalPartCore phase field +
    (phase.length⁻¹ : ℂ) • derivativeDotCore phase parameter inside
      (planarPartCore phase field))
  rw [if_pos rfl] at idempotent
  rw [scalarPart_def, idempotent]

/-- The poloidal correction is idempotent: `C_p² = C_p`, by the literal
N13 trace collapse `T Mᵀ M T = T` from `trace (Mᵀ M) = 2`. -/
theorem poloidalCorrection_idempotent (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 3) :
    poloidalCorrection phase parameter inside
        (poloidalCorrection phase parameter inside field) =
      poloidalCorrection phase parameter inside field := by
  obtain ⟨traceSummable, traceDelta⟩ := seedTrace_delta phase parameter inside
  have collapse : tangentialCore phase (seedTransposeCore phase parameter inside
      (seedMatrixCore phase parameter inside (tangentialCore phase
        (seedTransposeCore phase parameter inside (planarPartCore phase field))))) =
      tangentialCore phase (seedTransposeCore phase parameter inside
        (planarPartCore phase field)) := by
    calc tangentialCore phase (seedTransposeCore phase parameter inside
          (seedMatrixCore phase parameter inside (tangentialCore phase
            (seedTransposeCore phase parameter inside (planarPartCore phase field)))))
        = tangentialCore phase (smoothMultiplier phase (seedTransposeCells parameter)
            (seedTransposeCells_envelope_summable phase parameter inside)
            (smoothMultiplier phase (seedMatrixCells parameter)
              (seedMatrixCells_envelope_summable phase parameter inside)
              (tangentialCore phase (seedTransposeCore phase parameter inside
                (planarPartCore phase field))))) := by
          rw [show seedMatrixCore phase parameter inside (tangentialCore phase
              (seedTransposeCore phase parameter inside (planarPartCore phase field))) =
              smoothMultiplier phase (seedMatrixCells parameter)
                (seedMatrixCells_envelope_summable phase parameter inside)
                (tangentialCore phase (seedTransposeCore phase parameter inside
                  (planarPartCore phase field))) from
            seedMatrixCore_eq_full phase parameter inside _]
          rfl
      _ = tangentialCore phase (seedTransposeCore phase parameter inside
            (planarPartCore phase field)) :=
          tangentialCore_multiplier_sandwich phase (seedTransposeCells parameter)
            (seedMatrixCells parameter)
            (seedTransposeCells_envelope_summable phase parameter inside)
            (seedMatrixCells_envelope_summable phase parameter inside)
            traceSummable traceDelta _
  rw [poloidalCorrection_apply phase parameter inside field, poloidalCorrection_apply,
    planarPartCore_planarInclusionCore]
  exact congrArg (fun value => planarInclusionCore phase
    (seedMatrixCore phase parameter inside value)) collapse

/-- The full written-order N14 algebra for the actual gauge corrections. -/
theorem triangularGaugeProjection_algebra (inside : parameter ∈ Seed.parameterDomain) :
    (∀ field, poloidalCorrection phase parameter inside
        (triangularGaugeProjection phase parameter inside field) = 0) ∧
    (∀ field, toroidalCorrection phase parameter inside
        (triangularGaugeProjection phase parameter inside field) = 0) ∧
    (∀ field, poloidalCorrection phase parameter inside field = 0 →
      toroidalCorrection phase parameter inside field = 0 →
      triangularGaugeProjection phase parameter inside field = field) ∧
    (∀ field, triangularGaugeProjection phase parameter inside
        (triangularGaugeProjection phase parameter inside field) =
      triangularGaugeProjection phase parameter inside field) ∧
    LinearMap.range (triangularGaugeProjection phase parameter inside) =
      LinearMap.ker (poloidalCorrection phase parameter inside) ⊓
        LinearMap.ker (toroidalCorrection phase parameter inside) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro field
    exact triangularProjection_kills_poloidal _ _
      (poloidalCorrection_idempotent phase parameter inside)
      (poloidal_toroidal_cross phase parameter inside) field
  · intro field
    exact triangularProjection_kills_toroidal _ _
      (toroidalCorrection_idempotent phase parameter inside) field
  · intro field poloidalZero toroidalZero
    exact triangularProjection_fixes_kernel _ _ field poloidalZero toroidalZero
  · intro field
    exact triangularProjection_idempotent _ _
      (poloidalCorrection_idempotent phase parameter inside)
      (toroidalCorrection_idempotent phase parameter inside)
      (poloidal_toroidal_cross phase parameter inside) field
  · exact triangularProjection_range _ _
      (poloidalCorrection_idempotent phase parameter inside)
      (toroidalCorrection_idempotent phase parameter inside)
      (poloidal_toroidal_cross phase parameter inside)

end Grad.Constraints.Gauges
