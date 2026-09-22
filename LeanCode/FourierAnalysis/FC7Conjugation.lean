import FC7Truncation
import Mathlib.Analysis.Calculus.ContDiff.Basic

noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators Topology ComplexConjugate ContDiff

namespace Grad.CartesianState

open Grad.ClosedJets

/-- Coordinatewise complex conjugation on the fixed finite-dimensional
physical value space, regarded as a real-linear isometric equivalence. -/
def cartesianPhysicalConjugation (dimension : ℕ) :
    ComplexEuclidean dimension ≃ₗᵢ[ℝ] ComplexEuclidean dimension :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin dimension => Complex.conjLIE)

theorem cartesianPhysicalConjugation_apply (dimension : ℕ)
    (value : ComplexEuclidean dimension) (coordinate : Fin dimension) :
    cartesianPhysicalConjugation dimension value coordinate = conj (value coordinate) := rfl

theorem cartesianPhysicalConjugation_involutive (dimension : ℕ) :
    Function.Involutive (cartesianPhysicalConjugation dimension) := by
  intro value
  apply PiLp.ext
  intro coordinate
  simp only [cartesianPhysicalConjugation_apply, starRingEnd_apply, star_star]

/-- Coordinatewise conjugation of a continuous field on the closed disk. -/
def conjugateClosedMap {dimension : ℕ}
    (field : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    ContinuousMap ClosedDisk (ComplexEuclidean dimension) where
  toFun point := cartesianPhysicalConjugation dimension (field point)
  continuous_toFun := (cartesianPhysicalConjugation dimension).continuous.comp field.continuous

theorem conjugateClosedMap_apply {dimension : ℕ}
    (field : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) (point : ClosedDisk) :
    conjugateClosedMap field point = cartesianPhysicalConjugation dimension (field point) := rfl

theorem conjugateClosedMap_add {dimension : ℕ}
    (first second : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    conjugateClosedMap (first + second) =
      conjugateClosedMap first + conjugateClosedMap second := by
  apply ContinuousMap.ext
  intro point
  exact map_add (cartesianPhysicalConjugation dimension) (first point) (second point)

theorem conjugateClosedMap_real_smul {dimension : ℕ} (scalar : ℝ)
    (field : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    conjugateClosedMap (scalar • field) = scalar • conjugateClosedMap field := by
  apply ContinuousMap.ext
  intro point
  exact map_smul (cartesianPhysicalConjugation dimension) scalar (field point)

theorem conjugateClosedMap_involutive {dimension : ℕ} :
    Function.Involutive (@conjugateClosedMap dimension) := by
  intro field
  apply ContinuousMap.ext
  intro point
  exact cartesianPhysicalConjugation_involutive dimension (field point)

theorem closedDiskLift_conjugateClosedMap {dimension : ℕ}
    (field : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    closedDiskLift (conjugateClosedMap field) =
      cartesianPhysicalConjugation dimension ∘ closedDiskLift field := by
  funext point
  by_cases membership : point ∈ closedUnitDisk <;>
    simp [closedDiskLift, conjugateClosedMap, membership]

def conjugateClosedDerivative {dimension : ℕ} (field : ClosedJet dimension)
    (order : ℕ) (word : CartesianWord order) :
    ContinuousMap ClosedDisk (ComplexEuclidean dimension) :=
  conjugateClosedMap (closedDerivative field order word)

theorem conjugateClosedDerivative_spec {dimension : ℕ} (field : ClosedJet dimension)
    (order : ℕ) (word : CartesianWord order) :
    IsCartesianExtension (conjugateClosedMap field.value) order word
      (conjugateClosedDerivative field order word) := by
  intro point membership
  rw [show conjugateClosedDerivative field order word point =
    cartesianPhysicalConjugation dimension (closedDerivative field order word point) from rfl]
  rw [closedDiskLift_conjugateClosedMap]
  unfold cartesianDerivative
  change cartesianPhysicalConjugation dimension
      (closedDerivative field order word point) =
    (iteratedFDeriv ℝ order
      ((cartesianPhysicalConjugation dimension).toContinuousLinearEquiv ∘
        closedDiskLift field.value) point.val)
      (fun position => spatialBasis (word position))
  rw [(cartesianPhysicalConjugation dimension).toContinuousLinearEquiv.iteratedFDeriv_comp_left]
  change cartesianPhysicalConjugation dimension (closedDerivative field order word point) =
    cartesianPhysicalConjugation dimension
      (iteratedFDeriv ℝ order (closedDiskLift field.value) point.val
        (fun position => spatialBasis (word position)))
  exact congrArg (cartesianPhysicalConjugation dimension)
    (closedDerivative_spec field order word point membership)

/-- Conjugation of an actual closed jet, with all derivative extensions
conjugated rather than assumed. -/
def closedJetConjugate {dimension : ℕ} (field : ClosedJet dimension) :
    ClosedJet dimension where
  value := conjugateClosedMap field.value
  smoothInterior := by
    rw [closedDiskLift_conjugateClosedMap]
    exact (cartesianPhysicalConjugation dimension).toContinuousLinearEquiv
      |>.comp_contDiffOn_iff.mpr field.smoothInterior
  derivativeExists order word :=
    ⟨conjugateClosedDerivative field order word,
      conjugateClosedDerivative_spec field order word⟩

theorem closedJetConjugate_value {dimension : ℕ} (field : ClosedJet dimension) :
    (closedJetConjugate field).value = conjugateClosedMap field.value := rfl

theorem closedJetConjugate_value_apply {dimension : ℕ} (field : ClosedJet dimension)
    (point : ClosedDisk) (coordinate : Fin dimension) :
    (closedJetConjugate field).value point coordinate =
      conj (field.value point coordinate) := rfl

theorem closedJetConjugate_derivative {dimension : ℕ} (field : ClosedJet dimension)
    (order : ℕ) (word : CartesianWord order) :
    closedDerivative (closedJetConjugate field) order word =
      conjugateClosedDerivative field order word := by
  symm
  apply cartesianExtension_unique
  exact conjugateClosedDerivative_spec field order word

theorem closedMultiDerivative_conjugate {dimension : ℕ} (field : ClosedJet dimension)
    (index : CartesianMultiIndex) :
    closedMultiDerivative (closedJetConjugate field) index =
      conjugateClosedMap (closedMultiDerivative field index) := by
  exact closedJetConjugate_derivative field (cartesianOrder index)
    (cartesianMultiIndexWord index)

theorem closedJetConjugate_add {dimension : ℕ} (first second : ClosedJet dimension) :
    closedJetConjugate (first + second) =
      closedJetConjugate first + closedJetConjugate second := by
  apply closedJet_eq_of_value_eq
  exact conjugateClosedMap_add first.value second.value

theorem closedJetConjugate_real_smul {dimension : ℕ} (scalar : ℝ)
    (field : ClosedJet dimension) :
    closedJetConjugate (scalar • field) = scalar • closedJetConjugate field := by
  apply closedJet_eq_of_value_eq
  exact conjugateClosedMap_real_smul scalar field.value

theorem closedJetConjugate_involutive {dimension : ℕ} :
    Function.Involutive (@closedJetConjugate dimension) := by
  intro field
  apply closedJet_eq_of_value_eq
  exact conjugateClosedMap_involutive field.value

theorem closedJetConjugate_zero {dimension : ℕ} :
    closedJetConjugate (0 : ClosedJet dimension) = 0 := by
  simpa only [zero_smul] using
    (closedJetConjugate_real_smul (dimension := dimension) (0 : ℝ)
      (0 : ClosedJet dimension))

theorem phaseWeightedJet_neg {dimension : ℕ} (parameters : PhaseParameters)
    (cell : ℤ) (field : ClosedJet dimension) :
    phaseWeightedJet parameters (-cell) field =
      phaseWeightedJet parameters cell field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [phaseWeightedJet_value, phaseWeightedJet_value,
    cartesianWeight_neg]

theorem closedJetConjugate_phaseWeightedJet {dimension : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension) :
    closedJetConjugate (phaseWeightedJet parameters cell field) =
      phaseWeightedJet parameters cell (closedJetConjugate field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  change conj (cartesianWeight parameters cell point.val •
      field.value point coordinate) =
    cartesianWeight parameters cell point.val • conj (field.value point coordinate)
  exact map_smul Complex.conjLIE (cartesianWeight parameters cell point.val)
    (field.value point coordinate)

theorem phaseWeightedJet_conjugate_reflect {dimension : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension) :
    phaseWeightedJet parameters cell (closedJetConjugate field) =
      closedJetConjugate (phaseWeightedJet parameters (-cell) field) := by
  rw [phaseWeightedJet_neg parameters cell field,
    closedJetConjugate_phaseWeightedJet]

theorem closedContinuousToDiskL2_norm_sq {dimension : ℕ}
    (field : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    ‖closedContinuousToDiskL2 field‖ ^ 2 =
      ∫ point : SpatialPlane,
        ‖closedDiskLift field point‖ ^ 2 ∂volume.restrict openUnitDisk := by
  rw [diskL2_norm_sq]
  apply integral_congr_ae
  filter_upwards [closedContinuousToDiskL2_ae field] with point equality
  rw [equality]

theorem closedContinuousToDiskL2_conjugate_norm_sq {dimension : ℕ}
    (field : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    ‖closedContinuousToDiskL2 (conjugateClosedMap field)‖ ^ 2 =
      ‖closedContinuousToDiskL2 field‖ ^ 2 := by
  rw [closedContinuousToDiskL2_norm_sq,
    closedContinuousToDiskL2_norm_sq,
    closedDiskLift_conjugateClosedMap]
  apply integral_congr_ae
  filter_upwards with point
  rw [Function.comp_apply, LinearIsometryEquiv.norm_map]

theorem weightedDerivativeL2_conjugate_reflect_norm_sq {dimension : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (index : CartesianMultiIndex) :
    ‖closedContinuousToDiskL2
        (closedMultiDerivative
          (phaseWeightedJet parameters cell (closedJetConjugate field)) index)‖ ^ 2 =
      ‖closedContinuousToDiskL2
        (closedMultiDerivative
          (phaseWeightedJet parameters (-cell) field) index)‖ ^ 2 := by
  rw [phaseWeightedJet_conjugate_reflect,
    closedMultiDerivative_conjugate]
  exact closedContinuousToDiskL2_conjugate_norm_sq _

/-- The actual coefficient formula `C_A(h)_n = conj(h_{-n})` on closed jets. -/
def conjugateCoefficients {dimension : ℕ}
    (coefficients : ℤ → ClosedJet dimension) : ℤ → ClosedJet dimension :=
  fun cell => closedJetConjugate (coefficients (-cell))

theorem conjugateCoefficients_apply {dimension : ℕ}
    (coefficients : ℤ → ClosedJet dimension) (cell : ℤ) :
    conjugateCoefficients coefficients cell =
      closedJetConjugate (coefficients (-cell)) := rfl

theorem conjugateCoefficients_add {dimension : ℕ}
    (first second : ℤ → ClosedJet dimension) :
    conjugateCoefficients (first + second) =
      conjugateCoefficients first + conjugateCoefficients second := by
  funext cell
  exact closedJetConjugate_add (first (-cell)) (second (-cell))

theorem conjugateCoefficients_real_smul {dimension : ℕ} (scalar : ℝ)
    (coefficients : ℤ → ClosedJet dimension) :
    conjugateCoefficients (scalar • coefficients) =
      scalar • conjugateCoefficients coefficients := by
  funext cell
  exact closedJetConjugate_real_smul scalar (coefficients (-cell))

theorem conjugateCoefficients_involutive {dimension : ℕ} :
    Function.Involutive (@conjugateCoefficients dimension) := by
  intro coefficients
  funext cell
  simpa only [conjugateCoefficients_apply, neg_neg] using
    closedJetConjugate_involutive (coefficients cell)

theorem conjugateCoefficients_truncate {dimension : ℕ} (cutoff : ℕ)
    (coefficients : ℤ → ClosedJet dimension) :
    conjugateCoefficients (truncateCoefficients cutoff coefficients) =
      truncateCoefficients cutoff (conjugateCoefficients coefficients) := by
  funext cell
  by_cases membership : cell ∈ centeredCellBox cutoff
  · have reflectedMembership : -cell ∈ centeredCellBox cutoff :=
      (neg_mem_centeredCellBox_iff cutoff cell).mpr membership
    simp only [conjugateCoefficients_apply, truncateCoefficients_apply,
      membership, reflectedMembership, if_true]
  · have reflectedMembership : -cell ∉ centeredCellBox cutoff := by
      simpa only [neg_mem_centeredCellBox_iff] using membership
    simp only [conjugateCoefficients_apply, truncateCoefficients_apply,
      membership, reflectedMembership, if_false, closedJetConjugate_zero]

theorem m2CellEnergy_conjugateCoefficients {dimension : ℕ}
    (parameters : PhaseParameters) (grade : ℕ)
    (coefficients : ℤ → ClosedJet dimension) (cell : ℤ) :
    m2CellEnergy parameters grade (conjugateCoefficients coefficients) cell =
      m2CellEnergy parameters grade coefficients (-cell) := by
  unfold m2CellEnergy
  apply Finset.sum_congr rfl
  intro index _membership
  rw [cellFrequency_neg]
  apply congrArg (fun energy : ℝ =>
    cellFrequency cell ^ (2 * (grade - cartesianOrder index.toCartesian)) * energy)
  exact weightedDerivativeL2_conjugate_reflect_norm_sq
    parameters cell (coefficients (-cell)) index.toCartesian

/-- Conjugate-reflection preserves the one all-grade coefficient core. -/
def cartesianCoreConjugation {dimension : ℕ} (parameters : PhaseParameters) :
    ACore parameters dimension →ₗ[ℝ] ACore parameters dimension where
  toFun field := ⟨conjugateCoefficients field.1, by
    apply (mem_originalCore_iff parameters _).mpr
    intro grade
    have original := (mem_originalCore_iff parameters field.1).mp field.property grade
    have reflected := (Equiv.neg ℤ).summable_iff.mpr original
    exact reflected.congr (fun cell => by
      simpa only [Function.comp_apply, Equiv.neg_apply] using
        (m2CellEnergy_conjugateCoefficients parameters grade field.1 cell).symm)⟩
  map_add' first second := by
    apply Subtype.ext
    exact conjugateCoefficients_add first.1 second.1
  map_smul' scalar field := by
    apply Subtype.ext
    exact conjugateCoefficients_real_smul scalar field.1

theorem cartesianCoreConjugation_apply {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (cell : ℤ) :
    (cartesianCoreConjugation parameters field).1 cell =
      closedJetConjugate (field.1 (-cell)) := rfl

theorem cartesianCoreConjugation_involutive {dimension : ℕ}
    (parameters : PhaseParameters) :
    Function.Involutive (cartesianCoreConjugation parameters :
      ACore parameters dimension → ACore parameters dimension) := by
  intro field
  apply Subtype.ext
  exact conjugateCoefficients_involutive field.1

theorem cartesianCoreTruncation_conjugation_commute {dimension : ℕ}
    (parameters : PhaseParameters) (cutoff : ℕ)
    (field : ACore parameters dimension) :
    cartesianCoreConjugation parameters
        (cartesianCoreTruncation parameters cutoff field) =
      cartesianCoreTruncation parameters cutoff
        (cartesianCoreConjugation parameters field) := by
  apply Subtype.ext
  exact conjugateCoefficients_truncate cutoff field.1

/-- The real-linear conjugate-reflection on a grade-tagged core. -/
def gradeCoreConjugationMap {dimension grade : ℕ} (parameters : PhaseParameters) :
    GradeCore parameters dimension grade →ₗ[ℝ]
      GradeCore parameters dimension grade where
  toFun field := ⟨cartesianCoreConjugation parameters field.toCore⟩
  map_add' first second := by
    apply GradeCore.ext
    exact (cartesianCoreConjugation parameters).map_add first.toCore second.toCore
  map_smul' scalar field := by
    apply GradeCore.ext
    exact (cartesianCoreConjugation parameters).map_smul scalar field.toCore

theorem gradeCoreConjugationMap_apply {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension grade)
    (cell : ℤ) :
    (gradeCoreConjugationMap parameters field).toCore.1 cell =
      closedJetConjugate (field.toCore.1 (-cell)) := rfl

theorem gradeCoreConjugationMap_involutive {dimension grade : ℕ}
    (parameters : PhaseParameters) :
    Function.Involutive (gradeCoreConjugationMap parameters :
      GradeCore parameters dimension grade → GradeCore parameters dimension grade) := by
  intro field
  apply GradeCore.ext
  exact cartesianCoreConjugation_involutive parameters field.toCore

theorem gradeCoreConjugationMap_norm {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension grade) :
    ‖gradeCoreConjugationMap parameters field‖ = ‖field‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [gradeCore_norm_eq_cartesianGradeSeminorm,
    gradeCore_norm_eq_cartesianGradeSeminorm,
    cartesianGradeSeminorm_apply, cartesianGradeSeminorm_apply,
    gradeCoreCoordinates_apply, gradeCoreCoordinates_apply,
    cartesianGradeCoordinates_norm_sq, cartesianGradeCoordinates_norm_sq]
  change (∑' cell : ℤ,
      m2CellEnergy parameters grade (conjugateCoefficients field.toCore.1) cell) =
    ∑' cell : ℤ, m2CellEnergy parameters grade field.toCore.1 cell
  simpa only [m2CellEnergy_conjugateCoefficients, Equiv.neg_apply] using
    (Equiv.neg ℤ).tsum_eq
      (fun cell : ℤ => m2CellEnergy parameters grade field.toCore.1 cell)

/-- The exact isometric real-linear involution `C_A` at every original grade. -/
def gradeCoreConjugation {dimension grade : ℕ} (parameters : PhaseParameters) :
    GradeCore parameters dimension grade ≃ₗᵢ[ℝ]
      GradeCore parameters dimension grade :=
  { gradeCoreConjugationMap parameters with
    invFun := gradeCoreConjugationMap parameters
    left_inv := gradeCoreConjugationMap_involutive parameters
    right_inv := gradeCoreConjugationMap_involutive parameters
    norm_map' := gradeCoreConjugationMap_norm parameters }

theorem gradeCoreConjugation_apply {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension grade)
    (cell : ℤ) :
    (gradeCoreConjugation parameters field).toCore.1 cell =
      closedJetConjugate (field.toCore.1 (-cell)) := rfl

theorem gradeCoreConjugation_involutive {dimension grade : ℕ}
    (parameters : PhaseParameters) :
    Function.Involutive (gradeCoreConjugation parameters :
      GradeCore parameters dimension grade → GradeCore parameters dimension grade) :=
  gradeCoreConjugationMap_involutive parameters

/-- Literal coefficientwise conjugate symmetry, stated in the fixed physical
complex coordinates. -/
def GradeCoreReality {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : GradeCore parameters dimension grade) : Prop :=
  ∀ (cell : ℤ) (point : ClosedDisk) (coordinate : Fin dimension),
    conj ((field.toCore.1 (-cell)).value point coordinate) =
      (field.toCore.1 cell).value point coordinate

theorem gradeCoreConjugation_fixed_iff_reality {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension grade) :
    gradeCoreConjugation parameters field = field ↔
      GradeCoreReality parameters field := by
  constructor
  · intro fixed cell point coordinate
    have coefficientEquality := congrArg
      (fun value : GradeCore parameters dimension grade =>
        (value.toCore.1 cell).value point coordinate) fixed
    simpa only [gradeCoreConjugation_apply,
      closedJetConjugate_value_apply] using coefficientEquality
  · intro reality
    apply GradeCore.ext
    apply Subtype.ext
    funext cell
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    apply PiLp.ext
    intro coordinate
    simpa only [gradeCoreConjugation_apply,
      closedJetConjugate_value_apply] using reality cell point coordinate

end Grad.CartesianState
