import COR01Disk

noncomputable section

open Set
open scoped ContDiff Topology

namespace Grad.ClosedJets

def assembleSpatialCell (point : SpatialPlane) (cell : ℝ) : SpatialCell :=
  WithLp.toLp 2 ![point 0, point 1, cell]

@[simp] theorem planarPart_assembleSpatialCell (point : SpatialPlane) (cell : ℝ) :
    planarPart (assembleSpatialCell point cell) = point := by
  ext coordinate
  fin_cases coordinate <;> rfl

theorem continuous_planarPart : Continuous planarPart := by
  unfold planarPart
  fun_prop

theorem openUnitCylinder_isOpen : IsOpen openUnitCylinder := by
  have cylinder_preimage :
      openUnitCylinder = planarPart ⁻¹' Metric.ball (0 : SpatialPlane) 1 := by
    ext point
    change (‖planarPart point‖ < 1) ↔ dist (planarPart point) 0 < 1
    rw [dist_zero_right]
  rw [cylinder_preimage]
  exact Metric.isOpen_ball.preimage continuous_planarPart

theorem diskCellPoint_assembleSpatialCell
    (point : ClosedDisk) (cell : ℝ) (membership : point.val ∈ openUnitDisk) :
    diskCellPoint (assembleSpatialCell point.val cell)
      (openCylinderMembershipClosed (assembleSpatialCell point.val cell) (by
        change ‖planarPart (assembleSpatialCell point.val cell)‖ < 1
        simpa [openUnitDisk] using membership)) = (point, (cell : CellCircle)) := by
  apply Prod.ext
  · apply Subtype.ext
    exact planarPart_assembleSpatialCell point.val cell
  · rfl

theorem diskCellClosedJet_eq_of_value_eq {dimension : ℕ}
    (first second : DiskCellClosedJet dimension) (equality : first.value = second.value) :
    first = second := by
  cases first
  cases second
  cases equality
  rfl

theorem closedMixedDerivative_spec {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (order : ℕ) (word : MixedCartesianWord order) :
    IsMixedCartesianExtension field.value order word
      (closedMixedDerivative field order word) :=
  Classical.choose_spec (field.derivativeExists order word)

theorem mixedCartesianExtension_unique {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (order : ℕ) (word : MixedCartesianWord order)
    (extension : ContinuousMap DiskCellDomain (ComplexEuclidean dimension))
    (extension_spec : IsMixedCartesianExtension field.value order word extension) :
    extension = closedMixedDerivative field order word := by
  apply continuousMap_eq_of_openDiskCell
  rintro ⟨point, circle⟩ membership
  obtain ⟨cell, rfl⟩ := QuotientAddGroup.mk_surjective circle
  let ambient := assembleSpatialCell point.val cell
  have ambient_membership : ambient ∈ openUnitCylinder := by
    change ‖planarPart ambient‖ < 1
    simpa [ambient, openUnitDisk] using membership
  have point_identity :
      diskCellPoint ambient (openCylinderMembershipClosed ambient ambient_membership) =
        (point, (cell : CellCircle)) := by
    simpa [ambient] using diskCellPoint_assembleSpatialCell point cell membership
  rw [← point_identity]
  rw [extension_spec ambient ambient_membership,
    closedMixedDerivative_spec field order word ambient ambient_membership]

theorem closedMixedDerivative_zero_order {dimension : ℕ}
    (field : DiskCellClosedJet dimension) :
    closedMixedDerivative field 0 emptyMixedCartesianWord = field.value := by
  symm
  apply mixedCartesianExtension_unique field 0 emptyMixedCartesianWord
  intro point membership
  simp only [mixedCartesianDerivative, iteratedFDeriv_zero_apply]
  simp [diskCellLift, openCylinderMembershipClosed point membership]

def diskCellJetZeroValue (dimension : ℕ) :
    ContinuousMap DiskCellDomain (ComplexEuclidean dimension) where
  toFun := fun _ => 0
  continuous_toFun := continuous_const

def diskCellJetAddValue {dimension : ℕ}
    (first second : DiskCellClosedJet dimension) :
    ContinuousMap DiskCellDomain (ComplexEuclidean dimension) where
  toFun := fun point => first.value point + second.value point
  continuous_toFun := first.value.continuous.add second.value.continuous

def diskCellJetSmulValue {dimension : ℕ} (scalar : ℂ)
    (field : DiskCellClosedJet dimension) :
    ContinuousMap DiskCellDomain (ComplexEuclidean dimension) where
  toFun := fun point => scalar • field.value point
  continuous_toFun := field.value.continuous.const_smul scalar

theorem diskCellLift_zero_value (dimension : ℕ) :
    diskCellLift (diskCellJetZeroValue dimension) =
      (0 : SpatialCell → ComplexEuclidean dimension) := by
  funext point
  simp [diskCellLift, diskCellJetZeroValue]

theorem diskCellLift_add_value {dimension : ℕ}
    (first second : DiskCellClosedJet dimension) :
    diskCellLift (diskCellJetAddValue first second) =
      diskCellLift first.value + diskCellLift second.value := by
  funext point
  by_cases membership : point ∈ closedUnitCylinder <;>
    simp [diskCellLift, diskCellJetAddValue, membership]

theorem diskCellLift_smul_value {dimension : ℕ} (scalar : ℂ)
    (field : DiskCellClosedJet dimension) :
    diskCellLift (diskCellJetSmulValue scalar field) =
      scalar • diskCellLift field.value := by
  funext point
  by_cases membership : point ∈ closedUnitCylinder <;>
    simp [diskCellLift, diskCellJetSmulValue, membership]

def closedMixedDerivativeAddValue {dimension : ℕ}
    (first second : DiskCellClosedJet dimension)
    (order : ℕ) (word : MixedCartesianWord order) :
    ContinuousMap DiskCellDomain (ComplexEuclidean dimension) where
  toFun := fun point =>
    closedMixedDerivative first order word point +
      closedMixedDerivative second order word point
  continuous_toFun :=
    (closedMixedDerivative first order word).continuous.add
      (closedMixedDerivative second order word).continuous

def closedMixedDerivativeSmulValue {dimension : ℕ} (scalar : ℂ)
    (field : DiskCellClosedJet dimension)
    (order : ℕ) (word : MixedCartesianWord order) :
    ContinuousMap DiskCellDomain (ComplexEuclidean dimension) where
  toFun := fun point => scalar • closedMixedDerivative field order word point
  continuous_toFun := (closedMixedDerivative field order word).continuous.const_smul scalar

theorem closedMixedDerivativeAddValue_spec {dimension : ℕ}
    (first second : DiskCellClosedJet dimension)
    (order : ℕ) (word : MixedCartesianWord order) :
    IsMixedCartesianExtension (diskCellJetAddValue first second) order word
      (closedMixedDerivativeAddValue first second order word) := by
  intro point membership
  rw [show closedMixedDerivativeAddValue first second order word
      (diskCellPoint point (openCylinderMembershipClosed point membership)) =
      closedMixedDerivative first order word
          (diskCellPoint point (openCylinderMembershipClosed point membership)) +
        closedMixedDerivative second order word
          (diskCellPoint point (openCylinderMembershipClosed point membership)) from rfl]
  rw [closedMixedDerivative_spec first order word point membership,
    closedMixedDerivative_spec second order word point membership]
  rw [diskCellLift_add_value]
  have first_smooth : ContDiffAt ℝ order (diskCellLift first.value) point :=
    ((first.smoothInterior point membership).of_le
      (WithTop.coe_le_coe.mpr (show (order : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      (openUnitCylinder_isOpen.mem_nhds membership)
  have second_smooth : ContDiffAt ℝ order (diskCellLift second.value) point :=
    ((second.smoothInterior point membership).of_le
      (WithTop.coe_le_coe.mpr (show (order : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      (openUnitCylinder_isOpen.mem_nhds membership)
  have derivative_identity := iteratedFDeriv_add_apply first_smooth second_smooth
  exact (congrArg
    (fun derivative => derivative (fun position => spatialCellBasis (word position)))
    derivative_identity).symm

theorem closedMixedDerivativeSmulValue_spec {dimension : ℕ} (scalar : ℂ)
    (field : DiskCellClosedJet dimension)
    (order : ℕ) (word : MixedCartesianWord order) :
    IsMixedCartesianExtension (diskCellJetSmulValue scalar field) order word
      (closedMixedDerivativeSmulValue scalar field order word) := by
  intro point membership
  rw [show closedMixedDerivativeSmulValue scalar field order word
      (diskCellPoint point (openCylinderMembershipClosed point membership)) =
      scalar • closedMixedDerivative field order word
        (diskCellPoint point (openCylinderMembershipClosed point membership)) from rfl]
  rw [closedMixedDerivative_spec field order word point membership]
  rw [diskCellLift_smul_value]
  have field_smooth : ContDiffAt ℝ order (diskCellLift field.value) point :=
    ((field.smoothInterior point membership).of_le
      (WithTop.coe_le_coe.mpr (show (order : ℕ∞) ≤ ⊤ from le_top))).contDiffAt
      (openUnitCylinder_isOpen.mem_nhds membership)
  have derivative_identity := iteratedFDeriv_const_smul_apply (a := scalar) field_smooth
  exact (congrArg
    (fun derivative => derivative (fun position => spatialCellBasis (word position)))
    derivative_identity).symm

def diskCellClosedJetZero (dimension : ℕ) : DiskCellClosedJet dimension where
  value := diskCellJetZeroValue dimension
  smoothInterior := by
    rw [diskCellLift_zero_value]
    exact contDiff_const.contDiffOn
  derivativeExists := by
    intro order word
    refine ⟨diskCellJetZeroValue dimension, ?_⟩
    intro point membership
    rw [diskCellLift_zero_value]
    simp [diskCellJetZeroValue, mixedCartesianDerivative, iteratedFDeriv_zero]

def diskCellClosedJetAdd {dimension : ℕ}
    (first second : DiskCellClosedJet dimension) : DiskCellClosedJet dimension where
  value := diskCellJetAddValue first second
  smoothInterior := by
    rw [diskCellLift_add_value]
    exact first.smoothInterior.add second.smoothInterior
  derivativeExists := fun order word =>
    ⟨closedMixedDerivativeAddValue first second order word,
      closedMixedDerivativeAddValue_spec first second order word⟩

def diskCellClosedJetSmul {dimension : ℕ} (scalar : ℂ)
    (field : DiskCellClosedJet dimension) : DiskCellClosedJet dimension where
  value := diskCellJetSmulValue scalar field
  smoothInterior := by
    rw [diskCellLift_smul_value]
    exact field.smoothInterior.const_smul scalar
  derivativeExists := fun order word =>
    ⟨closedMixedDerivativeSmulValue scalar field order word,
      closedMixedDerivativeSmulValue_spec scalar field order word⟩

theorem diskCellClosedJetAdd_derivative {dimension : ℕ}
    (first second : DiskCellClosedJet dimension)
    (order : ℕ) (word : MixedCartesianWord order) :
    closedMixedDerivative (diskCellClosedJetAdd first second) order word =
      closedMixedDerivativeAddValue first second order word := by
  symm
  apply mixedCartesianExtension_unique
  exact closedMixedDerivativeAddValue_spec first second order word

theorem diskCellClosedJetSmul_derivative {dimension : ℕ} (scalar : ℂ)
    (field : DiskCellClosedJet dimension)
    (order : ℕ) (word : MixedCartesianWord order) :
    closedMixedDerivative (diskCellClosedJetSmul scalar field) order word =
      closedMixedDerivativeSmulValue scalar field order word := by
  symm
  apply mixedCartesianExtension_unique
  exact closedMixedDerivativeSmulValue_spec scalar field order word

theorem disk_cell_closed_jet_goal : DiskCellClosedJetGoal := by
  refine ⟨?_, ?_, ?_⟩
  · exact fun _ first second equality =>
      diskCellClosedJet_eq_of_value_eq first second equality
  · intro dimension field order word
    exact ⟨closedMixedDerivative_spec field order word,
      fun extension extension_spec =>
        mixedCartesianExtension_unique field order word extension extension_spec⟩
  · exact fun _ field => closedMixedDerivative_zero_order field

theorem disk_cell_linear_goal : DiskCellLinearGoal := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro dimension
    refine ⟨diskCellClosedJetZero dimension, ?_, ?_⟩
    · intro point
      rfl
    · intro candidate candidate_zero
      apply diskCellClosedJet_eq_of_value_eq
      apply ContinuousMap.ext
      exact candidate_zero
  · intro dimension first second
    refine ⟨diskCellClosedJetAdd first second, ?_, ?_⟩
    · intro point
      rfl
    · intro candidate candidate_add
      apply diskCellClosedJet_eq_of_value_eq
      apply ContinuousMap.ext
      exact candidate_add
  · intro dimension scalar field
    refine ⟨diskCellClosedJetSmul scalar field, ?_, ?_⟩
    · intro point
      rfl
    · intro candidate candidate_smul
      apply diskCellClosedJet_eq_of_value_eq
      apply ContinuousMap.ext
      exact candidate_smul
  · intro dimension first second sum sum_value order word point
    have sum_eq : sum = diskCellClosedJetAdd first second := by
      apply diskCellClosedJet_eq_of_value_eq
      apply ContinuousMap.ext
      exact sum_value
    subst sum
    rw [diskCellClosedJetAdd_derivative]
    rfl
  · intro dimension scalar field scaled scaled_value order word point
    have scaled_eq : scaled = diskCellClosedJetSmul scalar field := by
      apply diskCellClosedJet_eq_of_value_eq
      apply ContinuousMap.ext
      exact scaled_value
    subst scaled
    rw [diskCellClosedJetSmul_derivative]
    rfl

end Grad.ClosedJets
