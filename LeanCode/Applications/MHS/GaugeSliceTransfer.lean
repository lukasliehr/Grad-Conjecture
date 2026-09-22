import GaugeSliceProjection

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers

variable (phase : PhaseParameters)
variable (parameterM : Seed.Parameters) (insideM : parameterM ∈ Seed.parameterDomain)
variable (parameterN : Seed.Parameters) (insideN : parameterN ∈ Seed.parameterDomain)

/-- The planar half of the literal N18 transfer: `w ↦ N R_N (M⁻¹ w)`. -/
def planarTransfer : ACore phase 2 →ₗ[ℂ] ACore phase 2 :=
  (seedMatrixCore phase parameterN insideN).comp
    ((sliceProjection phase parameterN insideN).comp
      (seedInverseCore phase parameterM insideM))

theorem planarTransfer_apply (field : ACore phase 2) :
    planarTransfer phase parameterM insideM parameterN insideN field =
      seedMatrixCore phase parameterN insideN (sliceProjection phase parameterN insideN
        (seedInverseCore phase parameterM insideM field)) := rfl

/-- The tangential half of the literal N18 transfer:
`u_T ↦ (I - Π) u_T - L⁻¹ Π (û_⊥ · N' y)`. -/
def transferToroidalComponent : ACore phase 3 →ₗ[ℂ] ACore phase 1 :=
  ((toroidalPartCore phase) - (angularCore phase 0).comp (toroidalPartCore phase)) -
    (phase.length⁻¹ : ℂ) • ((angularCore phase 0).comp
      ((derivativeDotCore phase parameterN insideN).comp
        ((planarTransfer phase parameterM insideM parameterN insideN).comp
          (planarPartCore phase))))

/-- The complete literal N18 seed transfer on three-component fields. -/
def seedTransfer : ACore phase 3 →ₗ[ℂ] ACore phase 3 :=
  (planarInclusionCore phase).comp
      ((planarTransfer phase parameterM insideM parameterN insideN).comp
        (planarPartCore phase)) +
    (toroidalInclusionCore phase).comp
      (transferToroidalComponent phase parameterM insideM parameterN insideN)

theorem seedTransfer_planar_part (field : ACore phase 3) :
    planarPartCore phase (seedTransfer phase parameterM insideM parameterN insideN field) =
      planarTransfer phase parameterM insideM parameterN insideN
        (planarPartCore phase field) := by
  change planarPartCore phase
    (planarInclusionCore phase (planarTransfer phase parameterM insideM parameterN insideN
        (planarPartCore phase field)) +
      toroidalInclusionCore phase (transferToroidalComponent phase parameterM insideM
        parameterN insideN field)) = _
  rw [map_add, planarPartCore_planarInclusionCore, planarPartCore_toroidalInclusionCore,
    add_zero]

theorem seedTransfer_toroidal_part (field : ACore phase 3) :
    toroidalPartCore phase (seedTransfer phase parameterM insideM parameterN insideN field) =
      transferToroidalComponent phase parameterM insideM parameterN insideN field := by
  change toroidalPartCore phase
    (planarInclusionCore phase (planarTransfer phase parameterM insideM parameterN insideN
        (planarPartCore phase field)) +
      toroidalInclusionCore phase (transferToroidalComponent phase parameterM insideM
        parameterN insideN field)) = _
  rw [map_add, toroidalPartCore_planarInclusionCore, toroidalPartCore_toroidalInclusionCore,
    zero_add]

/-- The transferred field lies in the target poloidal gauge kernel. -/
theorem seedTransfer_poloidal_gauge (field : ACore phase 3) :
    poloidalCorrection phase parameterN insideN
        (seedTransfer phase parameterM insideM parameterN insideN field) = 0 := by
  rw [poloidalCorrection_apply, seedTransfer_planar_part, planarTransfer_apply,
    ← gaugeComposite_apply, gaugeComposite_sliceProjection, map_zero, map_zero]

/-- The transferred field lies in the target toroidal gauge kernel. -/
theorem seedTransfer_toroidal_gauge (field : ACore phase 3) :
    toroidalCorrection phase parameterN insideN
        (seedTransfer phase parameterM insideM parameterN insideN field) = 0 := by
  rw [toroidalCorrection_apply, seedTransfer_toroidal_part, seedTransfer_planar_part]
  set meanDot := angularCore phase 0 (derivativeDotCore phase parameterN insideN
    (planarTransfer phase parameterM insideM parameterN insideN (planarPartCore phase field)))
    with meanDot_def
  have componentExpand : transferToroidalComponent phase parameterM insideM parameterN insideN
      field =
      (toroidalPartCore phase field - angularCore phase 0 (toroidalPartCore phase field)) -
        (phase.length⁻¹ : ℂ) • meanDot := rfl
  rw [componentExpand]
  have angularSplit : angularCore phase 0
      ((toroidalPartCore phase field - angularCore phase 0 (toroidalPartCore phase field)) -
          (phase.length⁻¹ : ℂ) • meanDot +
        (phase.length⁻¹ : ℂ) • derivativeDotCore phase parameterN insideN
          (planarTransfer phase parameterM insideM parameterN insideN
            (planarPartCore phase field))) =
      (angularCore phase 0 (toroidalPartCore phase field) -
          angularCore phase 0 (angularCore phase 0 (toroidalPartCore phase field))) -
        (phase.length⁻¹ : ℂ) • angularCore phase 0 meanDot +
        (phase.length⁻¹ : ℂ) • meanDot := by
    rw [map_add, map_sub, map_sub, map_smul, map_smul]
  rw [angularSplit]
  have firstCollapse := angularCore_projection phase 0 0 (toroidalPartCore phase field)
  rw [if_pos rfl] at firstCollapse
  have secondCollapse := angularCore_projection phase 0 0 (derivativeDotCore phase
    parameterN insideN (planarTransfer phase parameterM insideM parameterN insideN
      (planarPartCore phase field)))
  rw [if_pos rfl] at secondCollapse
  rw [firstCollapse, meanDot_def, secondCollapse]
  rw [sub_self, zero_sub, neg_add_cancel, map_zero]

/-- The non-mean tangential component is literally preserved. -/
theorem seedTransfer_nonmean (field : ACore phase 3) :
    toroidalPartCore phase (seedTransfer phase parameterM insideM parameterN insideN field) -
        angularCore phase 0 (toroidalPartCore phase
          (seedTransfer phase parameterM insideM parameterN insideN field)) =
      toroidalPartCore phase field -
        angularCore phase 0 (toroidalPartCore phase field) := by
  rw [seedTransfer_toroidal_part]
  set meanDot := angularCore phase 0 (derivativeDotCore phase parameterN insideN
    (planarTransfer phase parameterM insideM parameterN insideN (planarPartCore phase field)))
  have componentExpand : transferToroidalComponent phase parameterM insideM parameterN insideN
      field =
      (toroidalPartCore phase field - angularCore phase 0 (toroidalPartCore phase field)) -
        (phase.length⁻¹ : ℂ) • meanDot := rfl
  rw [componentExpand, map_sub, map_sub, map_smul]
  have firstCollapse := angularCore_projection phase 0 0 (toroidalPartCore phase field)
  rw [if_pos rfl] at firstCollapse
  have secondCollapse := angularCore_projection phase 0 0 (derivativeDotCore phase
    parameterN insideN (planarTransfer phase parameterM insideM parameterN insideN
      (planarPartCore phase field)))
  rw [if_pos rfl] at secondCollapse
  rw [firstCollapse, secondCollapse]
  abel

/-- The exact N19 outer radial law: the seed-inverted radial component of the
transferred planar part equals the original seed-inverted radial component at
every closed polar point. -/
theorem seedTransfer_radial (field : ACore phase 3) (cell : ℤ) (radius : ℝ)
    (bounded : |radius| ≤ 1) (angle : ℝ) :
    radialComponentAt angle (((seedInverseCore phase parameterN insideN
        (planarPartCore phase (seedTransfer phase parameterM insideM parameterN insideN
          field))).1 cell).value (polarClosedPoint radius bounded angle)) =
      radialComponentAt angle (((seedInverseCore phase parameterM insideM
        (planarPartCore phase field)).1 cell).value
          (polarClosedPoint radius bounded angle)) := by
  rw [seedTransfer_planar_part, planarTransfer_apply,
    seedInverse_seedMatrix_core phase parameterN insideN, sliceProjection_apply,
    gaugeComposite_apply]
  set original := seedInverseCore phase parameterM insideM (planarPartCore phase field)
    with original_def
  have valueSplit : ((original - tangentialCore phase (seedTransposeCore phase parameterN
        insideN (seedMatrixCore phase parameterN insideN original))).1 cell).value
          (polarClosedPoint radius bounded angle) =
      (original.1 cell).value (polarClosedPoint radius bounded angle) -
        ((tangentialCore phase (seedTransposeCore phase parameterN insideN
          (seedMatrixCore phase parameterN insideN original))).1 cell).value
            (polarClosedPoint radius bounded angle) := by
    change ((original.1 cell) - (tangentialCore phase (seedTransposeCore phase parameterN
      insideN (seedMatrixCore phase parameterN insideN original))).1 cell).value
        (polarClosedPoint radius bounded angle) = _
    rw [sub_eq_add_neg, closedJet_value_add, ContinuousMap.add_apply, closedJet_value_neg,
      ContinuousMap.neg_apply, ← sub_eq_add_neg]
  rw [valueSplit, radialComponentAt_sub, tangentialCore_radial_component_zero, sub_zero]

end Grad.Constraints.Gauges
