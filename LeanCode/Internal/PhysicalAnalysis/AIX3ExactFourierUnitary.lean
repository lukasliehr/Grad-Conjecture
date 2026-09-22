import AIX2FullDisplacementMultipliers

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKernelOrbit

section Unitary
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The two commuting original Fourier translations on any stored Hilbert
sequence. All radial/phase/grade weights remain on the same mode. -/
def orbitLpLinear (tau : OrbitParameter) :
    lp (fun _ : ℤ × ℤ => E) 2 →ₗ[ℂ] lp (fun _ : ℤ × ℤ => E) 2 where
  toFun field := ⟨fun mode => orbitCharacter tau mode • field mode,
    field.property.mono' (fun mode => by rw [norm_smul, orbitCharacter_norm, one_mul])⟩
  map_add' first second := by
    apply lp.ext
    funext mode
    exact smul_add _ _ _
  map_smul' scalar field := by
    apply lp.ext
    funext mode
    exact smul_comm _ _ _

theorem orbitLpLinear_norm (tau : OrbitParameter) (field : lp (fun _ : ℤ × ℤ => E) 2) :
    ‖orbitLpLinear E tau field‖ = ‖field‖ := by
  have point (mode : ℤ × ℤ) : ‖orbitLpLinear E tau field mode‖ = ‖field mode‖ := by
    change ‖orbitCharacter tau mode • field mode‖ = _
    rw [norm_smul, orbitCharacter_norm, one_mul]
  exact le_antisymm (lp.norm_mono (by norm_num) (fun mode => (point mode).le))
    (lp.norm_mono (by norm_num) (fun mode => (point mode).ge))

def orbitLpEquivalence (tau : OrbitParameter) :
    lp (fun _ : ℤ × ℤ => E) 2 ≃ₗᵢ[ℂ] lp (fun _ : ℤ × ℤ => E) 2 where
  toLinearEquiv :=
    { orbitLpLinear E tau with
      invFun := orbitLpLinear E (-tau)
      left_inv := by
        intro field
        apply lp.ext
        funext mode
        change orbitCharacter (-tau) mode • (orbitCharacter tau mode • field mode) = field mode
        rw [smul_smul, mul_comm, orbitCharacter_inverse, one_smul]
      right_inv := by
        intro field
        apply lp.ext
        funext mode
        change orbitCharacter tau mode • (orbitCharacter (-tau) mode • field mode) = field mode
        rw [smul_smul, orbitCharacter_inverse, one_smul] }
  norm_map' := orbitLpLinear_norm E tau

def orbitLpAction (tau : OrbitParameter) :
    lp (fun _ : ℤ × ℤ => E) 2 →L[ℂ] lp (fun _ : ℤ × ℤ => E) 2 :=
  (orbitLpEquivalence E tau).toContinuousLinearEquiv.toContinuousLinearMap

@[simp] theorem orbitLpAction_apply (tau : OrbitParameter)
    (field : lp (fun _ : ℤ × ℤ => E) 2) (mode : ℤ × ℤ) :
    orbitLpAction E tau field mode = orbitCharacter tau mode • field mode := rfl

theorem orbitLpAction_add (tau sigma : OrbitParameter) (field : lp (fun _ : ℤ × ℤ => E) 2) :
    orbitLpAction E (tau + sigma) field = orbitLpAction E tau (orbitLpAction E sigma field) := by
  apply lp.ext
  funext mode
  rw [orbitLpAction_apply, orbitLpAction_apply, orbitLpAction_apply,
    smul_smul, orbitCharacter_add]

theorem orbitLpAction_inverse (tau : OrbitParameter) (field : lp (fun _ : ℤ × ℤ => E) 2) :
    orbitLpAction E tau (orbitLpAction E (-tau) field) = field :=
  (orbitLpEquivalence E tau).apply_symm_apply field

end Unitary
end Grad.AnnularKernelOrbit
