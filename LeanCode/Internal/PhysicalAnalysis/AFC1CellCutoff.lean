import AFM1ActualLinearData
import GQF29CompletedRange

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 3000
open scoped Topology
namespace Grad.ActualBandCompletion
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Envelope
open Grad.FullReferenceLinearity Grad.BoundedScalarInverse
attribute [local instance] apNormedSpace Classical.propDecidable

def lpCut {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (keep : Set I) :
    lp (fun _ : I => E) 2 →L[ℂ] lp (fun _ : I => E) 2 := by
  classical
  let linear : lp (fun _ : I => E) 2 →ₗ[ℂ] lp (fun _ : I => E) 2 :=
    { toFun := fun field => ⟨fun i => if i ∈ keep then field i else 0,
        field.property.mono' (fun i => by split_ifs <;> simp)⟩
      map_add' := fun first second => by apply Subtype.ext; funext i; change (if i ∈ keep then first i + second i else 0) = (if i ∈ keep then first i else 0) + (if i ∈ keep then second i else 0); split_ifs <;> simp_all
      map_smul' := fun scalar field => by apply Subtype.ext; funext i; change (if i ∈ keep then scalar • field i else 0) = _; split_ifs <;> simp_all }
  exact linear.mkContinuous 1 (fun field => by
    rw [one_mul]
    apply lp.norm_mono (by norm_num)
    intro i
    change ‖if i ∈ keep then field i else 0‖ ≤ ‖field i‖
    split_ifs <;> simp)

theorem lpCut_apply {I E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (keep : Set I) (field : lp (fun _ : I => E) 2) (i : I) :
    lpCut keep field i = if i ∈ keep then field i else 0 := rfl

variable {L sigma gamma ell : ℝ}

theorem apCut_mem (keep : Set ℤ) (dimension grade : ℕ)
    (field : apGrade L sigma gamma ell dimension grade) :
    lpCut keep field.val ∈ apGrade L sigma gamma ell dimension grade := by
  classical
  apply isClosed_property (apFiniteInto_denseRange (dimension := dimension) (grade := grade) L sigma gamma ell)
    (((apSmoothCore L sigma gamma ell dimension grade).isClosed_topologicalClosure).preimage
      ((lpCut keep).continuous.comp continuous_subtype_val)) _ field
  intro core
  have identity : lpCut keep (apFiniteInto (grade := grade) L sigma gamma ell core).val =
      (apFiniteInto (grade := grade) L sigma gamma ell (core.filter (· ∈ keep))).val := by
    apply lp.ext
    funext cell
    change lpCut keep (apFiniteEmbed L sigma gamma ell core) cell = apFiniteEmbed L sigma gamma ell _ cell
    rw [lpCut_apply, apFiniteEmbed_apply, apFiniteEmbed_apply, Finsupp.filter_apply]
    split_ifs <;> simp
  change lpCut keep (apFiniteInto (grade := grade) L sigma gamma ell core).val ∈ apGrade L sigma gamma ell dimension grade
  rw [identity]
  exact (apFiniteInto (grade := grade) L sigma gamma ell (core.filter (· ∈ keep))).property

def apCut (keep : Set ℤ) (dimension grade : ℕ) :
    apGrade L sigma gamma ell dimension grade →L[ℂ] apGrade L sigma gamma ell dimension grade :=
  ((lpCut keep).comp (apGrade L sigma gamma ell dimension grade).subtypeL).codRestrict _
    (apCut_mem keep dimension grade)

theorem apCut_apply (keep : Set ℤ) (dimension grade : ℕ)
    (field : apGrade L sigma gamma ell dimension grade) (cell : ℤ) :
    (apCut keep dimension grade field).val cell = if cell ∈ keep then field.val cell else 0 := rfl

def apSmoothCut (admissible : Admissible L sigma gamma ell) (keep : Set ℤ) (dimension : ℕ) :
    APSmooth L sigma gamma ell dimension →ₗ[ℂ] APSmooth L sigma gamma ell dimension := by
  classical
  let cut (field : APSmooth L sigma gamma ell dimension) : APSmooth L sigma gamma ell dimension :=
    apLiteralSmooth L sigma gamma ell (fun cell => if cell ∈ keep then apSmoothJet admissible dimension cell field else 0)
      (fun grade => (apSmoothJet_summable admissible field grade).mono' (fun cell => by split_ifs <;> simp))
  refine { toFun := cut, map_add' := ?_, map_smul' := ?_ }
  · intro first second
    apply Subtype.ext
    funext grade
    apply Subtype.ext
    apply lp.ext
    funext cell
    change apRowLinear L sigma gamma ell cell (if cell ∈ keep then apSmoothJet admissible dimension cell (first + second) else 0) =
      apRowLinear L sigma gamma ell cell (if cell ∈ keep then apSmoothJet admissible dimension cell first else 0) +
      apRowLinear L sigma gamma ell cell (if cell ∈ keep then apSmoothJet admissible dimension cell second else 0)
    split_ifs <;> simp [map_add]
  · intro scalar field
    apply Subtype.ext
    funext grade
    apply Subtype.ext
    apply lp.ext
    funext cell
    change apRowLinear L sigma gamma ell cell (if cell ∈ keep then apSmoothJet admissible dimension cell (scalar • field) else 0) =
      scalar • apRowLinear L sigma gamma ell cell (if cell ∈ keep then apSmoothJet admissible dimension cell field else 0)
    split_ifs <;> simp [map_smul]

theorem apSmoothCut_grade (admissible : Admissible L sigma gamma ell) (keep : Set ℤ)
    (dimension grade : ℕ) (field : APSmooth L sigma gamma ell dimension) :
    apSmoothGrade L sigma gamma ell dimension grade (apSmoothCut admissible keep dimension field) =
      apCut keep dimension grade (apSmoothGrade L sigma gamma ell dimension grade field) := by
  classical
  apply Subtype.ext
  apply lp.ext
  funext cell
  change apRowLinear L sigma gamma ell cell (if cell ∈ keep then apSmoothJet admissible dimension cell field else 0) = _
  rw [apCut_apply]
  split_ifs <;> simp [apSmoothJet_row]

theorem apSmoothCut_jet (admissible : Admissible L sigma gamma ell) (keep : Set ℤ)
    (dimension : ℕ) (field : APSmooth L sigma gamma ell dimension) (cell : ℤ) :
    apSmoothJet admissible dimension cell (apSmoothCut admissible keep dimension field) =
      if cell ∈ keep then apSmoothJet admissible dimension cell field else 0 := by
  classical
  apply apRowLinear_injective (grade := 0) L sigma gamma ell cell
  rw [apSmoothJet_row, apSmoothCut_grade, apCut_apply]
  split_ifs <;> simp [apSmoothJet_row]

end Grad.ActualBandCompletion
