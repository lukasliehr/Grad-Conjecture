import AXF32PublicBoundary
import MultiplierInterface

noncomputable section

namespace Grad.RawSourceFaithfulness

open Grad.ClosedJets Grad.CartesianState Grad.Constraints.Multipliers

theorem completedCoordinates_norm {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : AGrade parameters dimension grade) :
    ‖completedCoordinates parameters field‖ = ‖field‖ := by
  apply isClosed_property (aGradeEta_denseRange parameters)
    (isClosed_eq (completedCoordinates parameters).continuous.norm continuous_norm) _ field
  intro core
  rw [completedCoordinates_eta, LinearIsometry.norm_map, aGradeEta_norm]

theorem completedCoordinates_injective {dimension grade : ℕ} (parameters : PhaseParameters) :
    Function.Injective (completedCoordinates (dimension := dimension) (grade := grade) parameters) := by
  intro first second equality
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  rw [← completedCoordinates_norm parameters, map_sub, equality, sub_self, norm_zero]

def zeroIndex : GradeMultiIndex 0 := ⟨(0, 0), by decide⟩

theorem index_zero_eq (index : GradeMultiIndex 0) : index = zeroIndex := by
  apply Subtype.ext
  apply Prod.ext <;> apply Fin.ext <;> omega

/-- All literal grade-zero coordinates, one original phase-weighted L2
function in every cell. The only spatial multi-index here is (0,0). -/
def zeroCell {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ) :
    AGrade parameters dimension 0 →L[ℂ] DiskL2 dimension :=
  (PiLp.proj (𝕜 := ℂ) 2 (fun _ : GradeMultiIndex 0 => DiskL2 dimension) zeroIndex).comp
    ((lp.evalCLM ℂ (fun _ : ℤ => CartesianGradeRow dimension 0) 2 cell).comp
      (completedCoordinates parameters))

theorem zeroCell_core {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (field : ACore parameters dimension) :
    zeroCell parameters cell (aGradeEta parameters (GradeCore.ofCoreLinear field)) =
      closedContinuousToDiskL2 (phaseWeightedJet parameters cell (field.val cell)).value := by
  change completedCoordinates parameters (aGradeEta parameters (GradeCore.ofCoreLinear field))
    cell zeroIndex = _
  rw [completedCoordinates_eta]
  change (cellFrequency cell : ℂ) ^ (0 - 0) •
    closedContinuousToDiskL2 (closedMultiDerivative
      (phaseWeightedJet parameters cell (field.val cell)) (0, 0)) = _
  simp only [Nat.sub_zero, pow_zero, one_smul]
  congr 1
  exact closedDerivative_zero_order _

theorem zeroCell_ext {dimension : ℕ} (parameters : PhaseParameters)
    {first second : AGrade parameters dimension 0}
    (equality : ∀ cell, zeroCell parameters cell first = zeroCell parameters cell second) :
    first = second := by
  apply completedCoordinates_injective parameters
  apply lp.ext
  funext cell
  apply PiLp.ext
  intro index
  rw [index_zero_eq index]
  exact equality cell

end Grad.RawSourceFaithfulness
