import GaugeInverseRight

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers

/-- The literal poloidal gauge composite `T ∘ G_M = T ∘ Mᵀ ∘ M`. -/
def gaugeComposite (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) : ACore phase 2 →ₗ[ℂ] ACore phase 2 :=
  (tangentialCore phase).comp ((seedTransposeCore phase parameter inside).comp
    (seedMatrixCore phase parameter inside))

theorem gaugeComposite_apply (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore phase 2) :
    gaugeComposite phase parameter inside field =
      tangentialCore phase (seedTransposeCore phase parameter inside
        (seedMatrixCore phase parameter inside field)) := rfl

/-- The general absorption law: any tangential output is fixed by
`T ∘ Mᵀ ∘ M` sandwiching, by the literal N13 trace normalization. -/
theorem tangential_sandwich_absorb (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore phase 2) :
    tangentialCore phase (seedTransposeCore phase parameter inside
        (seedMatrixCore phase parameter inside (tangentialCore phase field))) =
      tangentialCore phase field := by
  obtain ⟨traceSummable, traceDelta⟩ := seedTrace_delta phase parameter inside
  calc tangentialCore phase (seedTransposeCore phase parameter inside
        (seedMatrixCore phase parameter inside (tangentialCore phase field)))
      = tangentialCore phase (smoothMultiplier phase (seedTransposeCells parameter)
          (seedTransposeCells_envelope_summable phase parameter inside)
          (smoothMultiplier phase (seedMatrixCells parameter)
            (seedMatrixCells_envelope_summable phase parameter inside)
            (tangentialCore phase field))) := by
        rw [show seedMatrixCore phase parameter inside (tangentialCore phase field) =
            smoothMultiplier phase (seedMatrixCells parameter)
              (seedMatrixCells_envelope_summable phase parameter inside)
              (tangentialCore phase field) from
          seedMatrixCore_eq_full phase parameter inside _]
        rfl
    _ = tangentialCore phase field :=
        tangentialCore_multiplier_sandwich phase (seedTransposeCells parameter)
          (seedMatrixCells parameter)
          (seedTransposeCells_envelope_summable phase parameter inside)
          (seedMatrixCells_envelope_summable phase parameter inside)
          traceSummable traceDelta _

/-- Mixed-seed absorption `(T G_N)(T G_M) = T G_M` of the written N17 product
computation, valid for any two actual admissible seeds. -/
theorem gaugeComposite_absorb (phase : PhaseParameters)
    (parameterN : Seed.Parameters) (insideN : parameterN ∈ Seed.parameterDomain)
    (parameterM : Seed.Parameters) (insideM : parameterM ∈ Seed.parameterDomain)
    (field : ACore phase 2) :
    gaugeComposite phase parameterN insideN (gaugeComposite phase parameterM insideM field) =
      gaugeComposite phase parameterM insideM field := by
  rw [gaugeComposite_apply phase parameterM insideM, gaugeComposite_apply]
  exact tangential_sandwich_absorb phase parameterN insideN _

/-- The literal N16 slice projection `R_M = I - T (Mᵀ M ·)`. -/
def sliceProjection (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) : ACore phase 2 →ₗ[ℂ] ACore phase 2 :=
  LinearMap.id - gaugeComposite phase parameter inside

theorem sliceProjection_apply (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore phase 2) :
    sliceProjection phase parameter inside field =
      field - gaugeComposite phase parameter inside field := rfl

/-- The gauge composite annihilates every slice projection output. -/
theorem gaugeComposite_sliceProjection (phase : PhaseParameters)
    (parameterM : Seed.Parameters) (insideM : parameterM ∈ Seed.parameterDomain)
    (field : ACore phase 2) :
    gaugeComposite phase parameterM insideM
        (sliceProjection phase parameterM insideM field) = 0 := by
  rw [sliceProjection_apply, map_sub,
    gaugeComposite_absorb phase parameterM insideM parameterM insideM, sub_self]

/-- The written N17 product law `R_N R_M = R_N` for any two actual seeds. -/
theorem sliceProjection_absorb (phase : PhaseParameters)
    (parameterN : Seed.Parameters) (insideN : parameterN ∈ Seed.parameterDomain)
    (parameterM : Seed.Parameters) (insideM : parameterM ∈ Seed.parameterDomain)
    (field : ACore phase 2) :
    sliceProjection phase parameterN insideN
        (sliceProjection phase parameterM insideM field) =
      sliceProjection phase parameterN insideN field := by
  rw [sliceProjection_apply phase parameterN insideN
    (sliceProjection phase parameterM insideM field),
    sliceProjection_apply phase parameterM insideM field, map_sub,
    gaugeComposite_absorb phase parameterN insideN parameterM insideM,
    sliceProjection_apply]
  abel

/-- The written N17 idempotence `R_M² = R_M`. -/
theorem sliceProjection_idempotent (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore phase 2) :
    sliceProjection phase parameter inside (sliceProjection phase parameter inside field) =
      sliceProjection phase parameter inside field :=
  sliceProjection_absorb phase parameter inside parameter inside field

/-- The exact N17 range law: the slice projection ranges over precisely the
kernel of the poloidal gauge composite. -/
theorem sliceProjection_range (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    LinearMap.range (sliceProjection phase parameter inside) =
      LinearMap.ker (gaugeComposite phase parameter inside) := by
  ext field
  constructor
  · rintro ⟨source, rfl⟩
    exact LinearMap.mem_ker.mpr
      (gaugeComposite_sliceProjection phase parameter inside source)
  · intro membership
    refine ⟨field, ?_⟩
    rw [sliceProjection_apply, LinearMap.mem_ker.mp membership, sub_zero]

end Grad.Constraints.Gauges
