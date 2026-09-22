import SCC16KappaFourierBound

noncomputable section
open Set
open scoped BigOperators ContDiff

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarAngular

def angularCharacterField {dimension : ℕ} (shift : ℤ)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (point : ℝ × ℝ) : ComplexEuclidean dimension :=
  cellExponential shift point.2 • field point

theorem angularCharacterField_smooth {dimension : ℕ} (shift : ℤ)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (angularCharacterField shift field) :=
  ((cellExponential_smooth shift).comp contDiff_snd).smul smooth

theorem radialField_angularCharacter {dimension : ℕ} (shift : ℤ)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field) :
    radialField (angularCharacterField shift field) = angularCharacterField shift (radialField field) := by
  funext point
  exact (radialField_hasDerivAt _ (angularCharacterField_smooth shift field smooth) point.1 point.2).unique
    ((radialField_hasDerivAt field smooth point.1 point.2).const_smul (cellExponential shift point.2))

theorem radialIter_angularCharacter {dimension : ℕ} (shift : ℤ)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field) (order : ℕ) :
    radialIter order (angularCharacterField shift field) = angularCharacterField shift (radialIter order field) := by
  induction order with
  | zero => rfl
  | succ order previous =>
    rw [radialIter_succ, previous, radialField_angularCharacter _ _ (radialIter_smooth order field smooth)]
    rfl

theorem radialCoefficientJet_angularCharacter {dimension : ℕ} (shift : ℤ)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (mode : ℤ) (order : ℕ) (radius : ℝ) :
    radialCoefficientJet (angularCharacterField shift field) mode order radius =
      radialCoefficientJet field (mode - shift) order radius := by
  rw [radialCoefficientJet, radialIter_angularCharacter shift field smooth order]
  exact angularCoefficient_character_mul _ shift mode

theorem radialIter_zero {dimension : ℕ} (order : ℕ) :
    radialIter order (0 : ℝ × ℝ → ComplexEuclidean dimension) = 0 := by
  induction order with
  | zero => rfl
  | succ order previous =>
    rw [radialIter_succ, previous]
    funext point
    simp [radialField]

theorem radialIter_finsetSum {Index : Type*} {dimension : ℕ} (indices : Finset Index)
    (fields : Index → ℝ × ℝ → ComplexEuclidean dimension)
    (smooth : ∀ index ∈ indices, ContDiff ℝ ∞ (fields index)) (order : ℕ) :
    radialIter order (∑ index ∈ indices, fields index) = ∑ index ∈ indices, radialIter order (fields index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp [radialIter_zero]
  | @insert index indices absent previous =>
    have sumSmooth : ContDiff ℝ ∞ (∑ other ∈ indices, fields other) := by
      simpa only [← Finset.sum_apply] using
        ContDiff.sum (fun other member => smooth other (Finset.mem_insert_of_mem member))
    rw [Finset.sum_insert absent, Finset.sum_insert absent,
      radialIter_add order (fields index) (∑ other ∈ indices, fields other)
        (smooth index (Finset.mem_insert_self _ _)) sumSmooth,
      previous (fun other member => smooth other (Finset.mem_insert_of_mem member))]

theorem angularCoefficient_finsetSum {Index : Type*} {dimension : ℕ} (indices : Finset Index)
    (fields : Index → ℝ → ComplexEuclidean dimension)
    (continuousFields : ∀ index ∈ indices, Continuous (fields index)) (mode : ℤ) :
    angularCoefficient (∑ index ∈ indices, fields index) mode =
      ∑ index ∈ indices, angularCoefficient (fields index) mode := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp [angularCoefficient_compact]
  | @insert index indices absent previous =>
    have sumContinuous : Continuous (∑ other ∈ indices, fields other) := by
      simpa only [← Finset.sum_apply] using
        continuous_finsetSum indices (fun other member => continuousFields other (Finset.mem_insert_of_mem member))
    rw [Finset.sum_insert absent, Finset.sum_insert absent,
      angularCoefficient_add_continuous (fields index) (∑ other ∈ indices, fields other)
        (continuousFields index (Finset.mem_insert_self _ _)) sumContinuous,
      previous (fun other member => continuousFields other (Finset.mem_insert_of_mem member))]

theorem radialCoefficientJet_finsetSum {Index : Type*} {dimension : ℕ} (indices : Finset Index)
    (fields : Index → ℝ × ℝ → ComplexEuclidean dimension)
    (smooth : ∀ index ∈ indices, ContDiff ℝ ∞ (fields index)) (mode : ℤ) (order : ℕ) (radius : ℝ) :
    radialCoefficientJet (∑ index ∈ indices, fields index) mode order radius =
      ∑ index ∈ indices, radialCoefficientJet (fields index) mode order radius := by
  rw [radialCoefficientJet, radialIter_finsetSum indices fields smooth order]
  have slice : (fun angle => (∑ index ∈ indices, radialIter order (fields index)) (radius, angle)) =
      ∑ index ∈ indices, fun angle => radialIter order (fields index) (radius, angle) := by
    funext angle
    simp only [Finset.sum_apply]
  rw [slice]
  exact angularCoefficient_finsetSum indices _ (fun index member =>
    ((radialIter_smooth order _ (smooth index member)).continuous.comp (continuous_const.prodMk continuous_id))) mode

end Grad.SourceCollarCoefficients
