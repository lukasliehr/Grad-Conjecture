import GC18APFixedJet
import GC18APFiniteDensity
import CQ1DenseExtension

noncomputable section

set_option maxHeartbeats 1200000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState

theorem apComplement_exists (L sigma gamma ell : ℝ) (grade : ℕ) :
    ∃ completed : apGrade L sigma gamma ell 3 grade →L[ℂ] apGrade L sigma gamma ell 3 grade,
      (∀ field : ℤ →₀ ClosedJet 3, completed (apFiniteInto L sigma gamma ell field) =
        apFiniteInto L sigma gamma ell (apFiniteJetMap fixedComplementJet field)) ∧
      (∀ field, ‖completed field‖ ≤ apComplementConstant grade * ‖field‖) ∧
      (∀ field, completed (completed field) = completed field) ∧
      (∀ other : apGrade L sigma gamma ell 3 grade →L[ℂ] apGrade L sigma gamma ell 3 grade,
        (∀ field : ℤ →₀ ClosedJet 3, other (apFiniteInto L sigma gamma ell field) =
          apFiniteInto L sigma gamma ell (apFiniteJetMap fixedComplementJet field)) → other = completed) := by
  apply Grad.Cor18.dense_core_projection_extension (apFiniteInto L sigma gamma ell)
    (apFiniteInto_injective L sigma gamma ell) (apFiniteInto_denseRange L sigma gamma ell)
    (apFiniteJetMap fixedComplementJet) (apComplementConstant grade) (apComplementConstant_nonnegative grade)
    (apFiniteJetMap_bound L sigma gamma ell fixedComplementJet _ (apComplementConstant_nonnegative grade)
      (apFixedComplement_bound L sigma gamma ell grade))
  intro field
  apply Finsupp.ext
  intro cell
  exact fixedComplementJet_idempotent (field cell)

/-- The actual nonsingular C0=diag(T,Pi) on the exact original AP2
completion. Its range below, not a tangency-only carrier, is V. -/
def apComplement (L sigma gamma ell : ℝ) (grade : ℕ) :
    apGrade L sigma gamma ell 3 grade →L[ℂ] apGrade L sigma gamma ell 3 grade :=
  (apComplement_exists L sigma gamma ell grade).choose

theorem apComplement_core (L sigma gamma ell : ℝ) (grade : ℕ) (field : ℤ →₀ ClosedJet 3) :
    apComplement L sigma gamma ell grade (apFiniteInto L sigma gamma ell field) =
      apFiniteInto L sigma gamma ell (apFiniteJetMap fixedComplementJet field) :=
  (apComplement_exists L sigma gamma ell grade).choose_spec.1 field

theorem apComplement_bound (L sigma gamma ell : ℝ) (grade : ℕ) (field : apGrade L sigma gamma ell 3 grade) :
    ‖apComplement L sigma gamma ell grade field‖ ≤ apComplementConstant grade * ‖field‖ :=
  (apComplement_exists L sigma gamma ell grade).choose_spec.2.1 field

theorem apComplement_idempotent (L sigma gamma ell : ℝ) (grade : ℕ) (field : apGrade L sigma gamma ell 3 grade) :
    apComplement L sigma gamma ell grade (apComplement L sigma gamma ell grade field) = apComplement L sigma gamma ell grade field :=
  (apComplement_exists L sigma gamma ell grade).choose_spec.2.2.1 field

def apComplementRange (L sigma gamma ell : ℝ) (grade : ℕ) : Submodule ℂ (apGrade L sigma gamma ell 3 grade) :=
  LinearMap.range (apComplement L sigma gamma ell grade).toLinearMap

theorem apComplementRange_mem_iff (L sigma gamma ell : ℝ) (grade : ℕ) (field : apGrade L sigma gamma ell 3 grade) :
    field ∈ apComplementRange L sigma gamma ell grade ↔ apComplement L sigma gamma ell grade field = field := by
  constructor
  · rintro ⟨input, rfl⟩
    exact apComplement_idempotent L sigma gamma ell grade input
  · intro fixed
    exact ⟨field, fixed⟩

theorem apComplementRange_closed (L sigma gamma ell : ℝ) (grade : ℕ) :
    IsClosed (apComplementRange L sigma gamma ell grade : Set (apGrade L sigma gamma ell 3 grade)) := by
  have equality : (apComplementRange L sigma gamma ell grade : Set (apGrade L sigma gamma ell 3 grade)) =
      {field | apComplement L sigma gamma ell grade field = field} := Set.ext (apComplementRange_mem_iff L sigma gamma ell grade)
  rw [equality]
  exact isClosed_eq (apComplement L sigma gamma ell grade).continuous continuous_id

instance apComplementRange_complete (L sigma gamma ell : ℝ) (grade : ℕ) :
    CompleteSpace (apComplementRange L sigma gamma ell grade) :=
  (apComplementRange_closed L sigma gamma ell grade).completeSpace_coe

end Grad.GaugeCoefficients.Physical.RadialLedger
