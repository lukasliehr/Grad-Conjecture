import AAT1RealFourierDiagonal

noncomputable section
set_option maxHeartbeats 800000

open scoped Topology

namespace Grad.AnnularGrades

open Grad.AnnularVariational Grad.ClosedJets

section Finite
variable {Index C : Type*} [AddCommMonoid C] [Module ℂ C]

def finiteRealDiagonal (coefficient : Index → ℝ) : (Index →₀ C) →ₗ[ℂ] (Index →₀ C) :=
  Finsupp.lsum ℂ (fun index => (Finsupp.lsingle index).comp ((coefficient index : ℂ) • LinearMap.id))

theorem finiteRealDiagonal_apply (coefficient : Index → ℝ) (core : Index →₀ C) (index : Index) :
    finiteRealDiagonal coefficient core index = (coefficient index : ℂ) • core index := by
  classical
  rw [finiteRealDiagonal, Finsupp.lsum_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply, Finsupp.lsingle_apply,
    Finsupp.single_apply]
  rw [Finset.sum_eq_single index]
  · simp only [ite_true]
  · intro other _ different
    exact if_neg different
  · intro missing
    rw [Finsupp.notMem_support_iff.mp missing, smul_zero]
    simp

end Finite

section Energy
variable (lower length : ℝ) (positive : 0 < lower)
    (coefficient : HighAnnularMode → ℝ) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bounded : ∀ index, |coefficient index| ≤ constant)

theorem annularDiagonal_core (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    realLpDiagonal coefficient constant nonnegative bounded (finiteAnnularEnergyCore lower length positive core) =
      finiteAnnularEnergyCore lower length positive (finiteRealDiagonal coefficient core) := by
  apply lp.ext
  funext mode
  rw [realLpDiagonal_apply, finiteAnnularEnergyCore_apply, finiteAnnularEnergyCore_apply,
    finiteRealDiagonal_apply, map_smul]

theorem annularDiagonal_mem (field : annularEnergySpace lower length positive) :
    realLpDiagonal coefficient constant nonnegative bounded field.val ∈ annularEnergySpace lower length positive := by
  apply isClosed_property (annularEnergyCoreInto_denseRange lower length positive)
    ((LinearMap.range (finiteAnnularEnergyCore lower length positive)).isClosed_topologicalClosure.preimage
      ((realLpDiagonal coefficient constant nonnegative bounded).continuous.comp continuous_subtype_val)) _ field
  intro core
  change realLpDiagonal coefficient constant nonnegative bounded (finiteAnnularEnergyCore lower length positive core) ∈ _
  rw [annularDiagonal_core]
  exact (annularEnergyCoreInto lower length positive (finiteRealDiagonal coefficient core)).property

/-- The genuine bounded diagonal acts on the original completed energy
carrier; preservation is proved from the actual smooth core. -/
def annularEnergyDiagonal : annularEnergySpace lower length positive →L[ℂ] annularEnergySpace lower length positive :=
  ((realLpDiagonal coefficient constant nonnegative bounded).comp
    (annularEnergySpace lower length positive).subtypeL).codRestrict _
      (annularDiagonal_mem lower length positive coefficient constant nonnegative bounded)

theorem annularEnergyDiagonal_apply (field : annularEnergySpace lower length positive) (mode : HighAnnularMode) :
    (annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded field).val mode =
      (coefficient mode : ℂ) • field.val mode := rfl

theorem annularEnergyDiagonal_core (core : HighAnnularMode →₀ complexSmoothRadialCore 1) :
    annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded
      (annularEnergyCoreInto lower length positive core) =
        annularEnergyCoreInto lower length positive (finiteRealDiagonal coefficient core) :=
  Subtype.ext (annularDiagonal_core lower length positive coefficient constant nonnegative bounded core)

theorem annularEnergyDiagonal_bound (field : annularEnergySpace lower length positive) :
    ‖annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded field‖ ≤ constant * ‖field‖ := by
  change ‖realLpDiagonal coefficient constant nonnegative bounded field.val‖ ≤ constant * ‖field.val‖
  exact realLpDiagonal_bound coefficient constant nonnegative bounded field.val

theorem annularEnergyDiagonal_adjoint (first second : annularEnergySpace lower length positive) :
    inner ℂ (annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded first) second =
      inner ℂ first (annularEnergyDiagonal lower length positive coefficient constant nonnegative bounded second) := by
  change inner ℂ (realLpDiagonal coefficient constant nonnegative bounded first.val) second.val =
    inner ℂ first.val (realLpDiagonal coefficient constant nonnegative bounded second.val)
  exact realLpDiagonal_adjoint coefficient constant nonnegative bounded first.val second.val

end Energy

end Grad.AnnularGrades
