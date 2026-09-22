import FC5Proof

noncomputable section

open Set MeasureTheory Filter
open scoped ENNReal BigOperators Topology

namespace Grad.CartesianState

open Grad.ClosedJets

/-- The literal centered finite cell box `{-N, ..., N}`. -/
def centeredCellBox (cutoff : ℕ) : Finset ℤ :=
  Finset.Icc (-(cutoff : ℤ)) (cutoff : ℤ)

theorem mem_centeredCellBox_iff (cutoff : ℕ) (cell : ℤ) :
    cell ∈ centeredCellBox cutoff ↔ cell.natAbs ≤ cutoff := by
  simp only [centeredCellBox, Finset.mem_Icc]
  constructor
  · intro bounds
    by_cases nonnegative : 0 ≤ cell
    · have upper := bounds.2
      rw [← Int.natAbs_of_nonneg nonnegative] at upper
      exact_mod_cast upper
    · have nonpositive : cell ≤ 0 := le_of_not_ge nonnegative
      have reflected : -cell ≤ (cutoff : ℤ) := by omega
      have reflectedNonnegative : 0 ≤ -cell := by omega
      have castAbs : (cell.natAbs : ℤ) = -cell := by
        rw [← Int.natAbs_neg cell]
        exact Int.natAbs_of_nonneg reflectedNonnegative
      rw [← castAbs] at reflected
      exact_mod_cast reflected
  · intro bound
    have upper : cell ≤ (cell.natAbs : ℤ) := Int.le_natAbs
    have lower : -cell ≤ (cell.natAbs : ℤ) := by
      simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -cell))
    have castBound : (cell.natAbs : ℤ) ≤ cutoff := by exact_mod_cast bound
    constructor <;> omega

theorem neg_mem_centeredCellBox_iff (cutoff : ℕ) (cell : ℤ) :
    -cell ∈ centeredCellBox cutoff ↔ cell ∈ centeredCellBox cutoff := by
  simp only [mem_centeredCellBox_iff, Int.natAbs_neg]

/-- The centered boxes are cofinal among all finite subsets of `ℤ`. -/
theorem tendsto_centeredCellBox :
    Tendsto centeredCellBox atTop atTop := by
  rw [tendsto_atTop]
  intro cells
  refine Filter.eventually_atTop.2 ⟨cells.sup Int.natAbs, ?_⟩
  intro cutoff cutoffLarge cell membership
  rw [mem_centeredCellBox_iff]
  exact (Finset.le_sup membership).trans cutoffLarge

/-- Delete all coefficients outside the literal centered finite cell box. -/
def truncateCoefficients {dimension : ℕ} (cutoff : ℕ)
    (coefficients : ℤ → ClosedJet dimension) : ℤ → ClosedJet dimension :=
  fun cell => if cell ∈ centeredCellBox cutoff then coefficients cell else 0

theorem truncateCoefficients_apply {dimension : ℕ} (cutoff : ℕ)
    (coefficients : ℤ → ClosedJet dimension) (cell : ℤ) :
    truncateCoefficients cutoff coefficients cell =
      if cell ∈ centeredCellBox cutoff then coefficients cell else 0 := rfl

theorem truncateCoefficients_add {dimension : ℕ} (cutoff : ℕ)
    (first second : ℤ → ClosedJet dimension) :
    truncateCoefficients cutoff (first + second) =
      truncateCoefficients cutoff first + truncateCoefficients cutoff second := by
  funext cell
  by_cases membership : cell ∈ centeredCellBox cutoff <;>
    simp [truncateCoefficients, membership]

theorem truncateCoefficients_smul {dimension : ℕ} (cutoff : ℕ) (scalar : ℂ)
    (coefficients : ℤ → ClosedJet dimension) :
    truncateCoefficients cutoff (scalar • coefficients) =
      scalar • truncateCoefficients cutoff coefficients := by
  funext cell
  by_cases membership : cell ∈ centeredCellBox cutoff <;>
    simp [truncateCoefficients, membership]

theorem rawCartesianGradeCoordinates_truncate {dimension : ℕ}
    (parameters : PhaseParameters) (grade cutoff : ℕ)
    (coefficients : ℤ → ClosedJet dimension) (cell : ℤ) :
    rawCartesianGradeCoordinates parameters grade
        (truncateCoefficients cutoff coefficients) cell =
      if cell ∈ centeredCellBox cutoff then
        rawCartesianGradeCoordinates parameters grade coefficients cell
      else 0 := by
  by_cases membership : cell ∈ centeredCellBox cutoff <;>
    simp [rawCartesianGradeCoordinates, truncateCoefficients, membership]

/-- Centered cell truncation preserves the one all-grade core. -/
def cartesianCoreTruncation {dimension : ℕ} (parameters : PhaseParameters) (cutoff : ℕ) :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension where
  toFun field := ⟨truncateCoefficients cutoff field.1, by
    intro grade
    rw [memlp_iff_summable_sq]
    have original : Summable (fun cell : ℤ =>
        ‖rawCartesianGradeCoordinates parameters grade field.1 cell‖ ^ 2) :=
      (memlp_iff_summable_sq _).mp (field.property grade)
    have restricted := original.indicator
      (centeredCellBox cutoff : Set ℤ)
    exact restricted.congr (fun cell => by
      by_cases membership : cell ∈ centeredCellBox cutoff <;>
        simp [rawCartesianGradeCoordinates_truncate, membership])⟩
  map_add' first second := by
    apply Subtype.ext
    exact truncateCoefficients_add cutoff first.1 second.1
  map_smul' scalar field := by
    apply Subtype.ext
    exact truncateCoefficients_smul cutoff scalar field.1

theorem cartesianCoreTruncation_apply {dimension : ℕ} (parameters : PhaseParameters)
    (cutoff : ℕ) (field : ACore parameters dimension) (cell : ℤ) :
    (cartesianCoreTruncation parameters cutoff field).1 cell =
      if cell ∈ centeredCellBox cutoff then field.1 cell else 0 := rfl

/-- The same truncation on the grade-tagged normed core. -/
def gradeCoreTruncation {dimension grade : ℕ} (parameters : PhaseParameters) (cutoff : ℕ) :
    GradeCore parameters dimension grade →ₗ[ℂ] GradeCore parameters dimension grade :=
  GradeCore.ofCoreLinear.comp
    ((cartesianCoreTruncation parameters cutoff).comp GradeCore.toCoreLinear)

theorem gradeCoreTruncation_apply {dimension grade : ℕ} (parameters : PhaseParameters)
    (cutoff : ℕ) (field : GradeCore parameters dimension grade) (cell : ℤ) :
    (gradeCoreTruncation parameters cutoff field).toCore.1 cell =
      if cell ∈ centeredCellBox cutoff then field.toCore.1 cell else 0 := rfl

theorem gradeCoreCoordinates_truncation_sum {dimension grade : ℕ}
    (parameters : PhaseParameters) (cutoff : ℕ)
    (field : GradeCore parameters dimension grade) :
    gradeCoreCoordinates parameters (gradeCoreTruncation parameters cutoff field) =
      ∑ cell ∈ centeredCellBox cutoff,
        lp.single 2 cell (gradeCoreCoordinates parameters field cell) := by
  apply lp.ext
  funext cell
  rw [show gradeCoreCoordinates parameters
      (gradeCoreTruncation parameters cutoff field) cell =
        if cell ∈ centeredCellBox cutoff then
          gradeCoreCoordinates parameters field cell else 0 by
    change rawCartesianGradeCoordinates parameters grade
        (truncateCoefficients cutoff field.toCore.1) cell =
      if cell ∈ centeredCellBox cutoff then
        rawCartesianGradeCoordinates parameters grade field.toCore.1 cell else 0
    exact rawCartesianGradeCoordinates_truncate parameters grade cutoff field.toCore.1 cell]
  rw [lp.coeFn_sum]
  rw [Finset.sum_apply]
  simp_rw [lp.single_apply]
  rw [Finset.sum_pi_single]

/-- Centered finite cell truncations converge in the exact installed grade norm. -/
theorem tendsto_gradeCoreTruncation {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : GradeCore parameters dimension grade) :
    Tendsto (fun cutoff : ℕ => gradeCoreTruncation parameters cutoff field)
      atTop (𝓝 field) := by
  rw [(gradeCoreCoordinateIsometry parameters).isometry.isEmbedding.tendsto_nhds_iff]
  change Tendsto
    (fun cutoff : ℕ => gradeCoreCoordinates parameters
      (gradeCoreTruncation parameters cutoff field)) atTop
      (𝓝 (gradeCoreCoordinates parameters field))
  have coordinateLimit :=
    (lp.hasSum_single (p := (2 : ENNReal)) (by norm_num)
      (gradeCoreCoordinates parameters field)).comp tendsto_centeredCellBox
  simpa only [Function.comp_def, gradeCoreCoordinates_truncation_sum] using coordinateLimit

/-- A single all-grade core sequence is approximated in every original grade
by the same coefficient truncations. -/
theorem tendsto_cartesianCoreTruncation_every_grade {dimension : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension) (grade : ℕ) :
    Tendsto
      (fun cutoff : ℕ => GradeCore.ofCoreLinear (grade := grade)
        (cartesianCoreTruncation parameters cutoff field))
      atTop (𝓝 (GradeCore.ofCoreLinear (grade := grade) field)) :=
  tendsto_gradeCoreTruncation parameters
    (GradeCore.ofCoreLinear (grade := grade) field)

end Grad.CartesianState
