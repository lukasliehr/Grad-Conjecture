import FC7Proof

noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators Topology

namespace Grad.CartesianState

open Grad.ClosedJets

/-- Positivity of the phase gives coefficientwise injectivity. -/
theorem phaseWeightedJet_injective {dimension : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) :
    Function.Injective (@phaseWeightedJet dimension parameters cell) := by
  intro first second equality
  calc
    first = phaseInverseWeightedJet parameters cell
        (phaseWeightedJet parameters cell first) :=
      (phaseWeightedJet_inverse_right parameters cell first).symm
    _ = phaseInverseWeightedJet parameters cell
        (phaseWeightedJet parameters cell second) := by rw [equality]
    _ = second := phaseWeightedJet_inverse_right parameters cell second

/-- The inverse phase multiplier is complex linear on the actual closed-jet
carrier. -/
theorem phaseInverseWeightedJet_add {dimension : ℕ}
    (parameters : PhaseParameters) (cell : ℤ)
    (first second : ClosedJet dimension) :
    phaseInverseWeightedJet parameters cell (first + second) =
      phaseInverseWeightedJet parameters cell first +
        phaseInverseWeightedJet parameters cell second := by
  apply phaseWeightedJet_injective parameters cell
  rw [phaseWeightedJet_inverse_left]
  change first + second = phaseWeightedJet parameters cell
    (closedJetAdd (phaseInverseWeightedJet parameters cell first)
      (phaseInverseWeightedJet parameters cell second))
  rw [phaseWeightedJet_add,
    phaseWeightedJet_inverse_left, phaseWeightedJet_inverse_left]
  rfl

theorem phaseInverseWeightedJet_complex_smul {dimension : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (scalar : ℂ)
    (field : ClosedJet dimension) :
    phaseInverseWeightedJet parameters cell (scalar • field) =
      scalar • phaseInverseWeightedJet parameters cell field := by
  apply phaseWeightedJet_injective parameters cell
  rw [phaseWeightedJet_inverse_left]
  change scalar • field = phaseWeightedJet parameters cell
    (closedJetSmul scalar (phaseInverseWeightedJet parameters cell field))
  rw [phaseWeightedJet_complex_smul,
    phaseWeightedJet_inverse_left]
  rfl

/-- Multiplication by `exp (-Phi_n)` as a complex-linear map of closed jets. -/
def phaseInverseWeightedJetLinear {dimension : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) :
    ClosedJet dimension →ₗ[ℂ] ClosedJet dimension where
  toFun := phaseInverseWeightedJet parameters cell
  map_add' := phaseInverseWeightedJet_add parameters cell
  map_smul' := phaseInverseWeightedJet_complex_smul parameters cell

/-- One ordinary (phase-zero) Cartesian derivative coordinate at grade `q`. -/
def ordinaryGradeDerivativeL2 {dimension grade : ℕ} (cell : ℤ)
    (index : GradeMultiIndex grade) :
    ClosedJet dimension →ₗ[ℂ] DiskL2 dimension :=
  ((cellFrequency cell : ℂ) ^
      (grade - cartesianOrder index.toCartesian)) •
    closedDerivativeL2 index.toCartesian

/-- The finite ordinary M1 row at one cell Fourier index. -/
def ordinaryCellGradeRowLinear {dimension grade : ℕ} (cell : ℤ) :
    ClosedJet dimension →ₗ[ℂ] CartesianGradeRow dimension grade where
  toFun field := WithLp.toLp 2
    (fun index => ordinaryGradeDerivativeL2 cell index field)
  map_add' first second := by
    apply PiLp.ext
    intro index
    exact (ordinaryGradeDerivativeL2 cell index).map_add first second
  map_smul' scalar field := by
    apply PiLp.ext
    intro index
    exact (ordinaryGradeDerivativeL2 cell index).map_smul scalar field

theorem ordinaryCellGradeRowLinear_apply {dimension grade : ℕ} (cell : ℤ)
    (field : ClosedJet dimension) (index : GradeMultiIndex grade) :
    ordinaryCellGradeRowLinear cell field index =
      (cellFrequency cell : ℂ) ^
          (grade - cartesianOrder index.toCartesian) •
        closedContinuousToDiskL2
          (closedMultiDerivative field index.toCartesian) := rfl

/-- Literal ordinary (phase-zero) grade coordinates for a cell-coefficient
family. -/
def ordinaryRawGradeCoordinates {dimension : ℕ} (grade : ℕ)
    (coefficients : ℤ → ClosedJet dimension) :
    ℤ → CartesianGradeRow dimension grade :=
  fun cell => ordinaryCellGradeRowLinear cell (coefficients cell)

theorem ordinaryRawGradeCoordinates_add {dimension : ℕ} (grade : ℕ)
    (first second : ℤ → ClosedJet dimension) :
    ordinaryRawGradeCoordinates grade (first + second) =
      ordinaryRawGradeCoordinates grade first +
        ordinaryRawGradeCoordinates grade second := by
  funext cell
  exact (ordinaryCellGradeRowLinear cell).map_add (first cell) (second cell)

theorem ordinaryRawGradeCoordinates_smul {dimension : ℕ} (grade : ℕ)
    (scalar : ℂ) (coefficients : ℤ → ClosedJet dimension) :
    ordinaryRawGradeCoordinates grade (scalar • coefficients) =
      scalar • ordinaryRawGradeCoordinates grade coefficients := by
  funext cell
  exact (ordinaryCellGradeRowLinear cell).map_smul scalar (coefficients cell)

/-- The literal all-grade phase-zero coefficient core.  Unlike `ACore`, its
definition is independent of the analytic phase parameters. -/
def ordinaryCoefficientCoreSubmodule (dimension : ℕ) :
    Submodule ℂ (ℤ → ClosedJet dimension) where
  carrier coefficients := ∀ grade : ℕ,
    Memℓp (ordinaryRawGradeCoordinates grade coefficients) 2
  zero_mem' := by
    intro grade
    have member : Memℓp
        (0 : ℤ → CartesianGradeRow dimension grade) 2 := zero_memℓp
    convert member using 1
    funext cell
    exact (ordinaryCellGradeRowLinear cell).map_zero
  add_mem' := by
    intro first second firstMember secondMember grade
    rw [ordinaryRawGradeCoordinates_add]
    exact (firstMember grade).add (secondMember grade)
  smul_mem' := by
    intro scalar coefficients member grade
    rw [ordinaryRawGradeCoordinates_smul]
    exact (member grade).const_smul scalar

abbrev OrdinaryCoefficientCore (dimension : ℕ) :=
  ordinaryCoefficientCoreSubmodule dimension

/-- Literal coefficientwise `W_gamma`. -/
def phaseWeightedCoefficientLinear {dimension : ℕ}
    (parameters : PhaseParameters) :
    (ℤ → ClosedJet dimension) →ₗ[ℂ] (ℤ → ClosedJet dimension) where
  toFun coefficients cell := phaseWeightedJet parameters cell (coefficients cell)
  map_add' first second := by
    funext cell
    exact phaseWeightedJet_add parameters cell (first cell) (second cell)
  map_smul' scalar coefficients := by
    funext cell
    exact phaseWeightedJet_complex_smul parameters cell scalar (coefficients cell)

/-- Literal coefficientwise `W_gamma⁻¹`. -/
def phaseInverseWeightedCoefficientLinear {dimension : ℕ}
    (parameters : PhaseParameters) :
    (ℤ → ClosedJet dimension) →ₗ[ℂ] (ℤ → ClosedJet dimension) where
  toFun coefficients cell :=
    phaseInverseWeightedJet parameters cell (coefficients cell)
  map_add' first second := by
    funext cell
    exact phaseInverseWeightedJet_add parameters cell (first cell) (second cell)
  map_smul' scalar coefficients := by
    funext cell
    exact phaseInverseWeightedJet_complex_smul parameters cell scalar
      (coefficients cell)

theorem ordinary_coordinates_phaseWeighted {dimension grade : ℕ}
    (parameters : PhaseParameters) (coefficients : ℤ → ClosedJet dimension) :
    ordinaryRawGradeCoordinates grade
        (phaseWeightedCoefficientLinear parameters coefficients) =
      rawCartesianGradeCoordinates parameters grade coefficients := rfl

theorem weighted_coordinates_phaseInverse {dimension grade : ℕ}
    (parameters : PhaseParameters) (coefficients : ℤ → ClosedJet dimension) :
    rawCartesianGradeCoordinates parameters grade
        (phaseInverseWeightedCoefficientLinear parameters coefficients) =
      ordinaryRawGradeCoordinates grade coefficients := by
  funext cell
  apply PiLp.ext
  intro index
  change
    (cellFrequency cell : ℂ) ^
        (grade - cartesianOrder index.toCartesian) •
      closedContinuousToDiskL2
        (closedMultiDerivative
          (phaseWeightedJet parameters cell
            (phaseInverseWeightedJet parameters cell (coefficients cell)))
          index.toCartesian) = _
  rw [phaseWeightedJet_inverse_left]
  rfl

/-- The actual coefficientwise phase multiplication is a complex-linear
bijection between the original all-grade coefficient core and the literal
phase-zero all-grade coefficient core. -/
def weightedCoefficientCoreEquiv {dimension : ℕ}
    (parameters : PhaseParameters) :
    ACore parameters dimension ≃ₗ[ℂ] OrdinaryCoefficientCore dimension where
  toFun field := ⟨phaseWeightedCoefficientLinear parameters field.1, by
    intro grade
    rw [ordinary_coordinates_phaseWeighted]
    exact field.property grade⟩
  invFun field := ⟨phaseInverseWeightedCoefficientLinear parameters field.1, by
    intro grade
    rw [weighted_coordinates_phaseInverse]
    exact field.property grade⟩
  left_inv field := by
    apply Subtype.ext
    funext cell
    exact phaseWeightedJet_inverse_right parameters cell (field.1 cell)
  right_inv field := by
    apply Subtype.ext
    funext cell
    exact phaseWeightedJet_inverse_left parameters cell (field.1 cell)
  map_add' first second := by
    apply Subtype.ext
    exact (phaseWeightedCoefficientLinear parameters).map_add first.1 second.1
  map_smul' scalar field := by
    apply Subtype.ext
    exact (phaseWeightedCoefficientLinear parameters).map_smul scalar field.1

@[simp] theorem weightedCoefficientCoreEquiv_apply {dimension : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (cell : ℤ) :
    (weightedCoefficientCoreEquiv parameters field).1 cell =
      phaseWeightedJet parameters cell (field.1 cell) := rfl

@[simp] theorem weightedCoefficientCoreEquiv_symm_apply {dimension : ℕ}
    (parameters : PhaseParameters) (field : OrdinaryCoefficientCore dimension)
    (cell : ℤ) :
    ((weightedCoefficientCoreEquiv parameters).symm field).1 cell =
      phaseInverseWeightedJet parameters cell (field.1 cell) := rfl

end Grad.CartesianState
