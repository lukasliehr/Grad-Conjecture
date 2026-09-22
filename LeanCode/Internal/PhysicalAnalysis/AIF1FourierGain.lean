import FTP1315Proof

noncomputable section

namespace Grad.InteriorFourier

open Grad.FourierGrade

universe u
variable {Value : Type u} [NormedAddCommGroup Value] [NormedSpace ℂ Value]

/-- The squared physical disk frequency on the period-four torus. -/
def diskFrequencySquare (mode : FourierMode) : ℝ :=
  coordinateSquare mode 0 + coordinateSquare mode 1

/-- The squared inhomogeneous cell frequency, exactly 1+n². -/
def cellFrequencySquare (mode : FourierMode) : ℝ :=
  1 + coordinateSquare mode 2

theorem frequencySquare_decomposition (mode : FourierMode) :
    frequencyWeight mode ^ 2 = diskFrequencySquare mode + cellFrequencySquare mode := by
  rw [frequencyWeight_sq_expanded]
  unfold diskFrequencySquare cellFrequencySquare
  ring

/-- Division by Lambda² between the literal weighted Fourier grades.
The weighted coordinates are identical, so this preserves the norm.
It constructs the higher-grade element without presupposing regularity. -/
def ellipticLift (grade : ℕ) : JGrade Value grade →L[ℂ] JGrade Value (grade + 2) :=
  ContinuousLinearMap.id ℂ _

theorem ellipticLift_norm (grade : ℕ) (field : JGrade Value grade) :
    ‖ellipticLift grade field‖ = ‖field‖ := rfl

theorem ellipticLift_coefficient (grade : ℕ) (field : JGrade Value grade) (mode : FourierMode) :
    (frequencyWeight mode : ℂ) ^ 2 • coefficient (grade + 2) (ellipticLift grade field) mode =
      coefficient grade field mode := by
  change (frequencyWeight mode : ℂ) ^ 2 •
    (((frequencyWeight mode : ℂ) ^ (grade + 2))⁻¹ • field mode) = _
  rw [smul_smul]
  change _ = (((frequencyWeight mode : ℂ) ^ grade)⁻¹) • field mode
  congr 1
  have nonzero : (frequencyWeight mode : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (frequencyWeight_ne_zero mode)
  rw [pow_add]
  field_simp

/-- V11: the Fourier identity for the weak disk Laplacian and lambda²h
constructs the missing grade q+2 of the same base field, with the exact
sum of the two grade-q norms. -/
theorem gainTwo_from_spectralEquation (grade : ℕ)
    (field : JGrade Value 0) (laplacian cellMass : JGrade Value grade)
    (equation : ∀ mode : FourierMode,
      (frequencyWeight mode : ℂ) ^ 2 • coefficient 0 field mode =
        coefficient grade cellMass mode - coefficient grade laplacian mode) :
    ∃ higher : JGrade Value (grade + 2),
      inclusion (grade + 2) 0 (by omega) higher = field ∧
      ‖higher‖ ≤ ‖laplacian‖ + ‖cellMass‖ := by
  refine ⟨ellipticLift grade (cellMass - laplacian), ?_, ?_⟩
  · apply ext_coefficients
    intro mode
    rw [inclusion_coefficient]
    have identity := ellipticLift_coefficient grade (cellMass - laplacian) mode
    have difference : coefficient grade (cellMass - laplacian) mode =
        coefficient grade cellMass mode - coefficient grade laplacian mode := by
      change _ • (cellMass mode - laplacian mode) = _
      exact smul_sub _ _ _
    rw [difference, ← equation mode] at identity
    have nonzero : (frequencyWeight mode : ℂ) ^ 2 ≠ 0 :=
      pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (frequencyWeight_ne_zero mode))
    exact (smul_right_injective _ nonzero) identity
  · rw [ellipticLift_norm]
    exact (norm_sub_le _ _).trans_eq (add_comm _ _)

end Grad.InteriorFourier
