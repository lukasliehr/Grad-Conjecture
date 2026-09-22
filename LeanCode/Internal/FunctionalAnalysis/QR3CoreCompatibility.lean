import QR2AmbientReality

noncomputable section

namespace Grad.CompletedReality

open Grad.ClosedJets Grad.CartesianState Grad.AxisCore Grad.SmoothingFamily
open Grad.ImplementationReadiness

/-- The same integer-cell symmetry on the actual all-grade axis family. -/
def smoothAxisConjugation (parameters : PhaseParameters) (dimension : ℕ) :
    Grad.SmoothingFamily.AxisCore parameters.sigma0 (ComplexEuclidean dimension) →ₗ[ℝ]
      Grad.SmoothingFamily.AxisCore parameters.sigma0 (ComplexEuclidean dimension) where
  toFun field := ⟨fun cell => cartesianPhysicalConjugation dimension (field.1 (-cell)), by
    intro grade
    have member := lp.memℓp (axisInvolution parameters dimension grade
      (axisToGrade parameters.sigma0 grade field))
    convert member using 1
    funext cell
    change (Grad.AxisCore.axisWeight parameters grade cell : ℂ) •
      cartesianPhysicalConjugation dimension (field.1 (-cell)) =
      cartesianPhysicalConjugation dimension
        ((Grad.AxisCore.axisWeight parameters grade (-cell) : ℂ) • field.1 (-cell))
    rw [axisConjugation_real_smul, Grad.AxisCore.axisWeight_even]⟩
  map_add' first second := by
    apply Subtype.ext
    funext cell
    exact (cartesianPhysicalConjugation dimension).map_add _ _
  map_smul' scalar field := by
    apply Subtype.ext
    funext cell
    exact (cartesianPhysicalConjugation dimension).map_smul scalar _

theorem smoothAxisConjugation_involutive (parameters : PhaseParameters) (dimension : ℕ) :
    Function.Involutive (smoothAxisConjugation parameters dimension) := by
  intro field
  apply Subtype.ext
  funext cell
  change cartesianPhysicalConjugation dimension
    (cartesianPhysicalConjugation dimension (field.1 (-(-cell)))) = field.1 cell
  rw [neg_neg, cartesianPhysicalConjugation_involutive]

theorem smoothAxisConjugation_eta (parameters : PhaseParameters) (dimension grade : ℕ)
    (field : Grad.SmoothingFamily.AxisCore parameters.sigma0 (ComplexEuclidean dimension)) :
    axisConjugation parameters dimension grade (axisToGrade parameters.sigma0 grade field) =
      axisToGrade parameters.sigma0 grade (smoothAxisConjugation parameters dimension field) := by
  apply lp.ext
  funext cell
  change cartesianPhysicalConjugation dimension
    ((Grad.AxisCore.axisWeight parameters grade (-cell) : ℂ) • field.1 (-cell)) =
    (Grad.AxisCore.axisWeight parameters grade cell : ℂ) •
      cartesianPhysicalConjugation dimension (field.1 (-cell))
  rw [axisConjugation_real_smul, Grad.AxisCore.axisWeight_even]

/-- Ordinary component conjugation on the actual smooth state core. -/
def xCoreConjugation (parameters : PhaseParameters) :
    StateCore parameters →ₗ[ℝ] StateCore parameters :=
  (smoothAxisConjugation parameters 2).prodMap
    ((cartesianCoreConjugation parameters).prodMap (cartesianCoreConjugation parameters))

theorem xConjugation_eta (parameters : PhaseParameters) (grade : ℕ)
    (field : StateCore parameters) :
    xConjugation parameters grade (stateToGrade parameters grade field) =
      stateToGrade parameters grade (xCoreConjugation parameters field) := by
  apply (WithLp.equiv 1 _).injective
  apply Prod.ext
  · exact smoothAxisConjugation_eta parameters 2 (grade + 1) field.1
  · apply (WithLp.equiv 1 _).injective
    apply Prod.ext
    · exact aGradeConjugation_eta parameters 3 grade (GradeCore.ofCoreLinear field.2.1)
    · exact aGradeConjugation_eta parameters 1 grade (GradeCore.ofCoreLinear field.2.2)

/-- The swapped real symmetry on the four actual all-grade scalar cores. -/
def zCoreConjugation (parameters : PhaseParameters) :
    (Fin 4 → ACore parameters 1) →ₗ[ℝ] (Fin 4 → ACore parameters 1) where
  toFun field coordinate := cartesianCoreConjugation parameters (field (spinSwap coordinate))
  map_add' first second := by
    funext coordinate
    exact (cartesianCoreConjugation parameters).map_add _ _
  map_smul' scalar field := by
    funext coordinate
    exact (cartesianCoreConjugation parameters).map_smul scalar _

theorem zCoreConjugation_coefficient (parameters : PhaseParameters)
    (field : Fin 4 → ACore parameters 1) (coordinate : Fin 4) (cell : ℤ) :
    (zCoreConjugation parameters field coordinate).1 cell =
      closedJetConjugate ((field (spinSwap coordinate)).1 (-cell)) := rfl

theorem zCoreConjugation_involutive (parameters : PhaseParameters) :
    Function.Involutive (zCoreConjugation parameters) := by
  intro field
  funext coordinate
  change cartesianCoreConjugation parameters
    (cartesianCoreConjugation parameters (field (spinSwap (spinSwap coordinate)))) = field coordinate
  rw [spinSwap_involutive, cartesianCoreConjugation_involutive]

theorem zConjugation_eta (parameters : PhaseParameters) (grade : ℕ)
    (field : Fin 4 → ACore parameters 1) :
    zConjugation parameters grade
        (zEmbedding parameters grade (fun coordinate => GradeCore.ofCoreLinear (field coordinate))) =
      zEmbedding parameters grade
        (fun coordinate => GradeCore.ofCoreLinear (zCoreConjugation parameters field coordinate)) := by
  apply PiLp.ext
  intro coordinate
  exact aGradeConjugation_eta parameters 1 grade
    (GradeCore.ofCoreLinear (field (spinSwap coordinate)))

end Grad.CompletedReality
