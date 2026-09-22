import QR1CoefficientReality

noncomputable section

open scoped BigOperators

namespace Grad.CompletedReality

open Grad.ClosedJets Grad.CartesianState Grad.AxisCore Grad.SmoothingFamily
open Grad.ImplementationReadiness

/-- The quotient's real symmetry swaps `gplus` and `gminus`, fixing `g3,h`. -/
def spinSwap : Equiv.Perm (Fin 4) := Equiv.swap 0 1

theorem spinSwap_involutive (coordinate : Fin 4) : spinSwap (spinSwap coordinate) = coordinate := by
  fin_cases coordinate <;> decide

def zConjugationLinear (parameters : PhaseParameters) (grade : ℕ) :
    ZAmbient parameters grade →ₗ[ℝ] ZAmbient parameters grade where
  toFun field := WithLp.toLp 2 (fun coordinate =>
    aGradeConjugation parameters 1 grade (field (spinSwap coordinate)))
  map_add' first second := by
    apply PiLp.ext
    intro coordinate
    exact (aGradeConjugation parameters 1 grade).map_add _ _
  map_smul' scalar field := by
    apply PiLp.ext
    intro coordinate
    exact (aGradeConjugation parameters 1 grade).map_smul scalar _

theorem zConjugation_apply (parameters : PhaseParameters) (grade : ℕ)
    (field : ZAmbient parameters grade) (coordinate : Fin 4) :
    zConjugationLinear parameters grade field coordinate =
      aGradeConjugation parameters 1 grade (field (spinSwap coordinate)) := rfl

theorem zConjugation_involutive (parameters : PhaseParameters) (grade : ℕ) :
    Function.Involutive (zConjugationLinear parameters grade) := by
  intro field
  apply PiLp.ext
  intro coordinate
  simp only [zConjugation_apply, spinSwap_involutive]
  exact aGradeConjugation_involutive parameters 1 grade _

theorem zConjugation_norm (parameters : PhaseParameters) (grade : ℕ)
    (field : ZAmbient parameters grade) :
    ‖zConjugationLinear parameters grade field‖ = ‖field‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [zAmbient_norm_sq, zConjugation_apply, LinearIsometryEquiv.norm_map]
  exact Equiv.sum_comp spinSwap (fun coordinate => ‖field coordinate‖ ^ 2)

/-- The actual swapped isometric real involution on the original fourfold Hilbert carrier. -/
def zConjugation (parameters : PhaseParameters) (grade : ℕ) :
    ZAmbient parameters grade ≃ₗᵢ[ℝ] ZAmbient parameters grade :=
  { zConjugationLinear parameters grade with
    invFun := zConjugationLinear parameters grade
    left_inv := zConjugation_involutive parameters grade
    right_inv := zConjugation_involutive parameters grade
    norm_map' := zConjugation_norm parameters grade }

def xConjugationLinear (parameters : PhaseParameters) (grade : ℕ) :
    XAmbient parameters grade →ₗ[ℝ] XAmbient parameters grade where
  toFun field := statePack
    (axisConjugation parameters 2 (grade + 1) field.ofLp.1)
    (aGradeConjugation parameters 3 grade field.ofLp.2.ofLp.1)
    (aGradeConjugation parameters 1 grade field.ofLp.2.ofLp.2)
  map_add' first second := by
    apply (WithLp.equiv 1 _).injective
    apply Prod.ext
    · exact (axisConjugation parameters 2 (grade + 1)).map_add _ _
    · apply (WithLp.equiv 1 _).injective
      exact Prod.ext ((aGradeConjugation parameters 3 grade).map_add _ _)
        ((aGradeConjugation parameters 1 grade).map_add _ _)
  map_smul' scalar field := by
    apply (WithLp.equiv 1 _).injective
    apply Prod.ext
    · exact (axisConjugation parameters 2 (grade + 1)).map_smul scalar _
    · apply (WithLp.equiv 1 _).injective
      exact Prod.ext ((aGradeConjugation parameters 3 grade).map_smul scalar _)
        ((aGradeConjugation parameters 1 grade).map_smul scalar _)

theorem xConjugation_involutive (parameters : PhaseParameters) (grade : ℕ) :
    Function.Involutive (xConjugationLinear parameters grade) := by
  intro field
  apply (WithLp.equiv 1 _).injective
  apply Prod.ext
  · exact axisInvolution_involutive parameters 2 (grade + 1) field.ofLp.1
  · apply (WithLp.equiv 1 _).injective
    exact Prod.ext (aGradeConjugation_involutive parameters 3 grade field.ofLp.2.ofLp.1)
      (aGradeConjugation_involutive parameters 1 grade field.ofLp.2.ofLp.2)

theorem xConjugation_norm (parameters : PhaseParameters) (grade : ℕ)
    (field : XAmbient parameters grade) :
    ‖xConjugationLinear parameters grade field‖ = ‖field‖ := by
  change ‖statePack _ _ _‖ = ‖field‖
  rw [statePack_norm, xAmbient_norm, LinearIsometryEquiv.norm_map,
    LinearIsometryEquiv.norm_map, LinearIsometryEquiv.norm_map]

/-- The actual componentwise isometric real involution on the sum-norm state carrier,
including the original axis grade `q + 1`. -/
def xConjugation (parameters : PhaseParameters) (grade : ℕ) :
    XAmbient parameters grade ≃ₗᵢ[ℝ] XAmbient parameters grade :=
  { xConjugationLinear parameters grade with
    invFun := xConjugationLinear parameters grade
    left_inv := xConjugation_involutive parameters grade
    right_inv := xConjugation_involutive parameters grade
    norm_map' := xConjugation_norm parameters grade }

end Grad.CompletedReality
