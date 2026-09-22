import COR01Topology

noncomputable section

open Set
open scoped ContDiff Topology

namespace Grad.ClosedJets

theorem closedJet_eq_of_value_eq {dimension : ℕ}
    (first second : ClosedJet dimension) (equality : first.value = second.value) :
    first = second := by
  cases first
  cases second
  cases equality
  rfl

theorem closedDerivative_spec {dimension : ℕ} (field : ClosedJet dimension)
    (order : ℕ) (word : CartesianWord order) :
    IsCartesianExtension field.value order word (closedDerivative field order word) :=
  Classical.choose_spec (field.derivativeExists order word)

theorem cartesianExtension_unique {dimension : ℕ} (field : ClosedJet dimension)
    (order : ℕ) (word : CartesianWord order)
    (extension : ContinuousMap ClosedDisk (ComplexEuclidean dimension))
    (extension_spec : IsCartesianExtension field.value order word extension) :
    extension = closedDerivative field order word := by
  apply continuousMap_eq_of_openDisk
  intro point membership
  rw [extension_spec point membership, closedDerivative_spec field order word point membership]

theorem closedDerivative_zero_order {dimension : ℕ} (field : ClosedJet dimension) :
    closedDerivative field 0 emptyCartesianWord = field.value := by
  symm
  apply cartesianExtension_unique field 0 emptyCartesianWord
  intro point membership
  simp only [cartesianDerivative, iteratedFDeriv_zero_apply]
  simp [closedDiskLift, point.property]

def closedJetZeroValue (dimension : ℕ) :
    ContinuousMap ClosedDisk (ComplexEuclidean dimension) where
  toFun := fun _ => 0
  continuous_toFun := continuous_const

def closedJetAddValue {dimension : ℕ} (first second : ClosedJet dimension) :
    ContinuousMap ClosedDisk (ComplexEuclidean dimension) where
  toFun := fun point => first.value point + second.value point
  continuous_toFun := first.value.continuous.add second.value.continuous

def closedJetSmulValue {dimension : ℕ} (scalar : ℂ) (field : ClosedJet dimension) :
    ContinuousMap ClosedDisk (ComplexEuclidean dimension) where
  toFun := fun point => scalar • field.value point
  continuous_toFun := field.value.continuous.const_smul scalar

theorem closedDiskLift_zero_value (dimension : ℕ) :
    closedDiskLift (closedJetZeroValue dimension) =
      (0 : SpatialPlane → ComplexEuclidean dimension) := by
  funext point
  simp [closedDiskLift, closedJetZeroValue]

theorem closedDiskLift_add_value {dimension : ℕ} (first second : ClosedJet dimension) :
    closedDiskLift (closedJetAddValue first second) =
      closedDiskLift first.value + closedDiskLift second.value := by
  funext point
  by_cases membership : point ∈ closedUnitDisk <;>
    simp [closedDiskLift, closedJetAddValue, membership]

theorem closedDiskLift_smul_value {dimension : ℕ} (scalar : ℂ)
    (field : ClosedJet dimension) :
    closedDiskLift (closedJetSmulValue scalar field) =
      scalar • closedDiskLift field.value := by
  funext point
  by_cases membership : point ∈ closedUnitDisk <;>
    simp [closedDiskLift, closedJetSmulValue, membership]

def closedDerivativeAddValue {dimension : ℕ} (first second : ClosedJet dimension)
    (order : ℕ) (word : CartesianWord order) :
    ContinuousMap ClosedDisk (ComplexEuclidean dimension) where
  toFun := fun point =>
    closedDerivative first order word point + closedDerivative second order word point
  continuous_toFun :=
    (closedDerivative first order word).continuous.add
      (closedDerivative second order word).continuous

def closedDerivativeSmulValue {dimension : ℕ} (scalar : ℂ) (field : ClosedJet dimension)
    (order : ℕ) (word : CartesianWord order) :
    ContinuousMap ClosedDisk (ComplexEuclidean dimension) where
  toFun := fun point => scalar • closedDerivative field order word point
  continuous_toFun := (closedDerivative field order word).continuous.const_smul scalar

theorem openUnitDisk_isOpen : IsOpen openUnitDisk := by
  rw [openUnitDisk_eq_ball]
  exact Metric.isOpen_ball

theorem closedDerivativeAddValue_spec {dimension : ℕ} (first second : ClosedJet dimension)
    (order : ℕ) (word : CartesianWord order) :
    IsCartesianExtension (closedJetAddValue first second) order word
      (closedDerivativeAddValue first second order word) := by
  intro point membership
  rw [show closedDerivativeAddValue first second order word point =
      closedDerivative first order word point + closedDerivative second order word point from rfl]
  rw [closedDerivative_spec first order word point membership,
    closedDerivative_spec second order word point membership]
  rw [closedDiskLift_add_value]
  have first_smooth : ContDiffAt ℝ order (closedDiskLift first.value) point.val :=
    ((first.smoothInterior point.val membership).of_le
      (WithTop.coe_le_coe.mpr (show (order : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      (openUnitDisk_isOpen.mem_nhds membership)
  have second_smooth : ContDiffAt ℝ order (closedDiskLift second.value) point.val :=
    ((second.smoothInterior point.val membership).of_le
      (WithTop.coe_le_coe.mpr (show (order : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      (openUnitDisk_isOpen.mem_nhds membership)
  have derivative_identity := iteratedFDeriv_add_apply first_smooth second_smooth
  exact (congrArg (fun derivative => derivative (fun position => spatialBasis (word position)))
    derivative_identity).symm

theorem closedDerivativeSmulValue_spec {dimension : ℕ} (scalar : ℂ)
    (field : ClosedJet dimension) (order : ℕ) (word : CartesianWord order) :
    IsCartesianExtension (closedJetSmulValue scalar field) order word
      (closedDerivativeSmulValue scalar field order word) := by
  intro point membership
  rw [show closedDerivativeSmulValue scalar field order word point =
      scalar • closedDerivative field order word point from rfl]
  rw [closedDerivative_spec field order word point membership]
  rw [closedDiskLift_smul_value]
  have field_smooth : ContDiffAt ℝ order (closedDiskLift field.value) point.val :=
    ((field.smoothInterior point.val membership).of_le
      (WithTop.coe_le_coe.mpr (show (order : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      (openUnitDisk_isOpen.mem_nhds membership)
  have derivative_identity := iteratedFDeriv_const_smul_apply (a := scalar) field_smooth
  exact (congrArg (fun derivative => derivative (fun position => spatialBasis (word position)))
    derivative_identity).symm

def closedJetZero (dimension : ℕ) : ClosedJet dimension where
  value := closedJetZeroValue dimension
  smoothInterior := by
    rw [closedDiskLift_zero_value]
    exact contDiff_const.contDiffOn
  derivativeExists := by
    intro order word
    refine ⟨closedJetZeroValue dimension, ?_⟩
    intro point membership
    rw [closedDiskLift_zero_value]
    simp [closedJetZeroValue, cartesianDerivative, iteratedFDeriv_zero]

def closedJetAdd {dimension : ℕ} (first second : ClosedJet dimension) :
    ClosedJet dimension where
  value := closedJetAddValue first second
  smoothInterior := by
    rw [closedDiskLift_add_value]
    exact first.smoothInterior.add second.smoothInterior
  derivativeExists := fun order word =>
    ⟨closedDerivativeAddValue first second order word,
      closedDerivativeAddValue_spec first second order word⟩

def closedJetSmul {dimension : ℕ} (scalar : ℂ) (field : ClosedJet dimension) :
    ClosedJet dimension where
  value := closedJetSmulValue scalar field
  smoothInterior := by
    rw [closedDiskLift_smul_value]
    exact field.smoothInterior.const_smul scalar
  derivativeExists := fun order word =>
    ⟨closedDerivativeSmulValue scalar field order word,
      closedDerivativeSmulValue_spec scalar field order word⟩

theorem closedJetAdd_derivative {dimension : ℕ} (first second : ClosedJet dimension)
    (order : ℕ) (word : CartesianWord order) :
    closedDerivative (closedJetAdd first second) order word =
      closedDerivativeAddValue first second order word := by
  symm
  apply cartesianExtension_unique
  exact closedDerivativeAddValue_spec first second order word

theorem closedJetSmul_derivative {dimension : ℕ} (scalar : ℂ)
    (field : ClosedJet dimension) (order : ℕ) (word : CartesianWord order) :
    closedDerivative (closedJetSmul scalar field) order word =
      closedDerivativeSmulValue scalar field order word := by
  symm
  apply cartesianExtension_unique
  exact closedDerivativeSmulValue_spec scalar field order word

theorem closed_jet_goal : ClosedJetGoal := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun _ first second equality => closedJet_eq_of_value_eq first second equality
  · intro dimension field order word
    exact ⟨closedDerivative_spec field order word,
      fun extension extension_spec =>
        cartesianExtension_unique field order word extension extension_spec⟩
  · exact fun _ field => closedDerivative_zero_order field

theorem closed_jet_linear_goal : ClosedJetLinearGoal := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro dimension
    refine ⟨closedJetZero dimension, ?_, ?_⟩
    · intro point
      rfl
    · intro candidate candidate_zero
      apply closedJet_eq_of_value_eq
      apply ContinuousMap.ext
      intro point
      exact candidate_zero point
  · intro dimension first second
    refine ⟨closedJetAdd first second, ?_, ?_⟩
    · intro point
      rfl
    · intro candidate candidate_add
      apply closedJet_eq_of_value_eq
      apply ContinuousMap.ext
      intro point
      exact candidate_add point
  · intro dimension scalar field
    refine ⟨closedJetSmul scalar field, ?_, ?_⟩
    · intro point
      rfl
    · intro candidate candidate_smul
      apply closedJet_eq_of_value_eq
      apply ContinuousMap.ext
      intro point
      exact candidate_smul point
  · intro dimension first second sum sum_value order word point
    have sum_eq : sum = closedJetAdd first second := by
      apply closedJet_eq_of_value_eq
      apply ContinuousMap.ext
      exact sum_value
    subst sum
    rw [closedJetAdd_derivative]
    rfl
  · intro dimension scalar field scaled scaled_value order word point
    have scaled_eq : scaled = closedJetSmul scalar field := by
      apply closedJet_eq_of_value_eq
      apply ContinuousMap.ext
      exact scaled_value
    subst scaled
    rw [closedJetSmul_derivative]
    rfl

end Grad.ClosedJets
