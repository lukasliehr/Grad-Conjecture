import FP17Decay

noncomputable section

open Set MeasureTheory
open scoped BigOperators Topology

namespace Grad.CartesianState

open Grad.ClosedJets

/-! The actual disk-cell smooth carrier inherits its complex vector-space
structure from its value map.  The closed-jet laws make the value map
injective, so no quotient or auxiliary carrier is introduced here. -/

instance diskCellClosedJetZeroInstance (dimension : ℕ) :
    Zero (DiskCellClosedJet dimension) :=
  ⟨diskCellClosedJetZero dimension⟩

instance diskCellClosedJetAddInstance (dimension : ℕ) :
    Add (DiskCellClosedJet dimension) :=
  ⟨diskCellClosedJetAdd⟩

instance diskCellClosedJetNegInstance (dimension : ℕ) :
    Neg (DiskCellClosedJet dimension) :=
  ⟨fun field => diskCellClosedJetSmul (-1) field⟩

instance diskCellClosedJetSubInstance (dimension : ℕ) :
    Sub (DiskCellClosedJet dimension) :=
  ⟨fun first second => first + -second⟩

instance diskCellClosedJetNatSMulInstance (dimension : ℕ) :
    SMul ℕ (DiskCellClosedJet dimension) :=
  ⟨nsmulRec⟩

instance diskCellClosedJetIntSMulInstance (dimension : ℕ) :
    SMul ℤ (DiskCellClosedJet dimension) :=
  ⟨zsmulRec⟩

instance diskCellClosedJetComplexSMulInstance (dimension : ℕ) :
    SMul ℂ (DiskCellClosedJet dimension) :=
  ⟨diskCellClosedJetSmul⟩

@[simp] theorem diskCellClosedJet_value_zero (dimension : ℕ) :
    (0 : DiskCellClosedJet dimension).value = 0 := rfl

@[simp] theorem diskCellClosedJet_value_add {dimension : ℕ}
    (first second : DiskCellClosedJet dimension) :
    (first + second).value = first.value + second.value := rfl

@[simp] theorem diskCellClosedJet_value_neg {dimension : ℕ}
    (field : DiskCellClosedJet dimension) :
    (-field).value = -field.value := by
  apply ContinuousMap.ext
  intro point
  change (-1 : ℂ) • field.value point = -field.value point
  exact neg_one_smul ℂ (field.value point)

@[simp] theorem diskCellClosedJet_value_smul {dimension : ℕ} (scalar : ℂ)
    (field : DiskCellClosedJet dimension) :
    (scalar • field).value = scalar • field.value := rfl

instance diskCellClosedJetAddCommGroup (dimension : ℕ) :
    AddCommGroup (DiskCellClosedJet dimension) where
  add_assoc first second third := by
    apply diskCellClosedJet_eq_of_value_eq
    ext point
    exact add_assoc _ _ _
  zero_add field := by
    apply diskCellClosedJet_eq_of_value_eq
    ext point
    exact zero_add _
  add_zero field := by
    apply diskCellClosedJet_eq_of_value_eq
    ext point
    exact add_zero _
  add_comm first second := by
    apply diskCellClosedJet_eq_of_value_eq
    ext point
    exact add_comm _ _
  neg_add_cancel field := by
    apply diskCellClosedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    change (-1 : ℂ) • field.value point + field.value point = 0
    rw [neg_one_smul, neg_add_cancel]

instance diskCellClosedJetModule (dimension : ℕ) :
    Module ℂ (DiskCellClosedJet dimension) where
  one_smul field := by
    apply diskCellClosedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact one_smul ℂ (field.value point)
  mul_smul first second field := by
    apply diskCellClosedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact mul_smul first second (field.value point)
  smul_zero scalar := by
    apply diskCellClosedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact smul_zero scalar
  smul_add scalar first second := by
    apply diskCellClosedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact smul_add scalar (first.value point) (second.value point)
  add_smul first second field := by
    apply diskCellClosedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact add_smul first second (field.value point)
  zero_smul field := by
    apply diskCellClosedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact zero_smul ℂ (field.value point)

theorem ordinaryDiskCellTerm_add {dimension : ℕ} (cell : ℤ)
    (first second : ClosedJet dimension) :
    ordinaryDiskCellTerm cell (first + second) =
      ordinaryDiskCellTerm cell first + ordinaryDiskCellTerm cell second := by
  apply ContinuousMap.ext
  intro point
  simp only [ordinaryDiskCellTerm_apply, closedJet_value_add,
    ContinuousMap.add_apply, smul_add]

theorem ordinaryDiskCellTerm_smul {dimension : ℕ} (cell : ℤ)
    (scalar : ℂ) (field : ClosedJet dimension) :
    ordinaryDiskCellTerm cell (scalar • field) =
      scalar • ordinaryDiskCellTerm cell field := by
  apply ContinuousMap.ext
  intro point
  simp only [ordinaryDiskCellTerm_apply, closedJet_value_smul,
    ContinuousMap.smul_apply, smul_smul]
  rw [mul_comm]

theorem ordinaryReconstructedValue_add {dimension : ℕ}
    (first second : OrdinaryCoefficientCore dimension) :
    ordinaryReconstructedValue (first + second) =
      ordinaryReconstructedValue first + ordinaryReconstructedValue second := by
  apply (hasSum_ordinaryDiskCellTerm (first + second)).unique
  apply ((hasSum_ordinaryDiskCellTerm first).add
    (hasSum_ordinaryDiskCellTerm second)).congr_fun
  intro cell
  change ordinaryDiskCellTerm cell ((first + second).1 cell) =
    ordinaryDiskCellTerm cell (first.1 cell) +
      ordinaryDiskCellTerm cell (second.1 cell)
  exact ordinaryDiskCellTerm_add cell (first.1 cell) (second.1 cell)

theorem ordinaryReconstructedValue_smul {dimension : ℕ} (scalar : ℂ)
    (field : OrdinaryCoefficientCore dimension) :
    ordinaryReconstructedValue (scalar • field) =
      scalar • ordinaryReconstructedValue field := by
  apply (hasSum_ordinaryDiskCellTerm (scalar • field)).unique
  apply ((hasSum_ordinaryDiskCellTerm field).const_smul scalar).congr_fun
  intro cell
  change ordinaryDiskCellTerm cell ((scalar • field).1 cell) =
    scalar • ordinaryDiskCellTerm cell (field.1 cell)
  exact ordinaryDiskCellTerm_smul cell scalar (field.1 cell)

theorem ordinaryReconstructedClosedJet_add {dimension : ℕ}
    (first second : OrdinaryCoefficientCore dimension) :
    ordinaryReconstructedClosedJet (first + second) =
      ordinaryReconstructedClosedJet first +
        ordinaryReconstructedClosedJet second := by
  apply diskCellClosedJet_eq_of_value_eq
  simpa only [ordinaryReconstructedClosedJet_value,
    diskCellClosedJet_value_add] using
      ordinaryReconstructedValue_add first second

theorem ordinaryReconstructedClosedJet_smul {dimension : ℕ} (scalar : ℂ)
    (field : OrdinaryCoefficientCore dimension) :
    ordinaryReconstructedClosedJet (scalar • field) =
      scalar • ordinaryReconstructedClosedJet field := by
  apply diskCellClosedJet_eq_of_value_eq
  simpa only [ordinaryReconstructedClosedJet_value,
    diskCellClosedJet_value_smul] using
      ordinaryReconstructedValue_smul scalar field

/-- Uniform Fourier reconstruction as a complex-linear map into the actual
disk-cell smooth closed-jet carrier. -/
def ordinaryReconstructedClosedJetLinear {dimension : ℕ} :
    OrdinaryCoefficientCore dimension →ₗ[ℂ] DiskCellClosedJet dimension where
  toFun := ordinaryReconstructedClosedJet
  map_add' := ordinaryReconstructedClosedJet_add
  map_smul' := ordinaryReconstructedClosedJet_smul

/-- Exact Fourier synthesis/analysis equivalence between ordinary all-grade
coefficients and the actual disk-cell smooth closed-jet space. -/
def ordinaryCoefficientClosedJetEquiv {dimension : ℕ} :
    OrdinaryCoefficientCore dimension ≃ₗ[ℂ] DiskCellClosedJet dimension where
  toLinearMap := ordinaryReconstructedClosedJetLinear
  invFun := ordinaryFourierCoefficientCore
  left_inv := ordinaryFourierCoefficientCore_reconstruction_left
  right_inv := ordinaryReconstructedClosedJet_fourierCoefficientCore

@[simp] theorem ordinaryCoefficientClosedJetEquiv_apply {dimension : ℕ}
    (coefficients : OrdinaryCoefficientCore dimension) :
    ordinaryCoefficientClosedJetEquiv coefficients =
      ordinaryReconstructedClosedJet coefficients := rfl

@[simp] theorem ordinaryCoefficientClosedJetEquiv_symm_apply {dimension : ℕ}
    (field : DiskCellClosedJet dimension) :
    (ordinaryCoefficientClosedJetEquiv.symm field).1 =
      (ordinaryFourierCoefficientCore field).1 := rfl

/-- The literal coefficientwise `W_gamma`, followed by uniform Fourier
reconstruction, as a complex-linear bijection onto the actual smooth space. -/
def weightedSmoothEquiv {dimension : ℕ} (parameters : PhaseParameters) :
    ACore parameters dimension ≃ₗ[ℂ] DiskCellClosedJet dimension :=
  (weightedCoefficientCoreEquiv parameters).trans
    ordinaryCoefficientClosedJetEquiv

@[simp] theorem diskCellFourierCoefficientJet_weightedSmoothEquiv
    {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (cell : ℤ) :
    diskCellFourierCoefficientJet (weightedSmoothEquiv parameters field) cell =
      phaseWeightedJet parameters cell (field.1 cell) := by
  change diskCellFourierCoefficientJet
      (ordinaryReconstructedClosedJet
        (weightedCoefficientCoreEquiv parameters field)) cell = _
  rw [diskCellFourierCoefficientJet_ordinaryReconstructedClosedJet]
  rfl

@[simp] theorem weightedSmoothEquiv_symm_apply
    {dimension : ℕ} (parameters : PhaseParameters)
    (field : DiskCellClosedJet dimension) (cell : ℤ) :
    ((weightedSmoothEquiv parameters).symm field).1 cell =
      phaseInverseWeightedJet parameters cell
        (diskCellFourierCoefficientJet field cell) := by
  rfl

end Grad.CartesianState
