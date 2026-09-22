import JCProof

noncomputable section

open MeasureTheory Filter Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2)
open scoped Topology BigOperators

namespace Grad.WeightedJets.CellCutoff

theorem cutoff_coordinates (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (cells : Finset ℤ) (jet : WJet dimension order domain exponent) :
    ∀ᵐ point ∂volume.restrict domain, ∀ (index : JetIndex order) (cell : ℤ),
      (cutoff dimension order domain exponent cells jet).val index point cell =
        if cell ∈ cells then jet.val index point cell else 0 :=
  ae_all_iff.mpr (fun index => fieldCutoff_coordinate dimension domain cells (jet.val index))

theorem recoveredDerivative_cutoff (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (cells : Finset ℤ) (index : JetIndex order)
    (jet : WJet dimension order domain exponent) :
    Realization.recoveredDerivative dimension order domain exponent index
        (cutoff dimension order domain exponent cells jet) =
      fieldCutoff dimension domain cells (Realization.recoveredDerivative dimension order domain exponent index jet) :=
  fieldCutoff_inverse dimension domain cells (exponent index) (jet.val index)

theorem recoveredDerivative_cutoff_clm (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (cells : Finset ℤ) (index : JetIndex order) :
    (Realization.recoveredDerivative dimension order domain exponent index).comp
        (cutoff dimension order domain exponent cells) =
      (fieldCutoff dimension domain cells).comp (Realization.recoveredDerivative dimension order domain exponent index) := by
  apply ContinuousLinearMap.ext
  exact recoveredDerivative_cutoff dimension order domain exponent cells index

theorem inclusion_cutoff (dimension lower higher : ℕ) (domain : Set Spatial) (gap : ℕ)
    (bound : lower ≤ higher) (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ)
    (compatible : Inclusions.Compatible bound gap source target) (cells : Finset ℤ)
    (jet : WJet dimension higher domain source) :
    Inclusions.inclusion dimension lower higher domain gap bound source target compatible
        (cutoff dimension higher domain source cells jet) =
      cutoff dimension lower domain target cells
        (Inclusions.inclusion dimension lower higher domain gap bound source target compatible jet) := by
  apply jet_eq
  intro index
  exact fieldCutoff_inverse dimension domain cells gap (jet.val (Inclusions.indexInclusion bound index))

theorem inclusion_cutoff_clm (dimension lower higher : ℕ) (domain : Set Spatial) (gap : ℕ)
    (bound : lower ≤ higher) (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ)
    (compatible : Inclusions.Compatible bound gap source target) (cells : Finset ℤ) :
    (Inclusions.inclusion dimension lower higher domain gap bound source target compatible).comp
        (cutoff dimension higher domain source cells) =
      (cutoff dimension lower domain target cells).comp
        (Inclusions.inclusion dimension lower higher domain gap bound source target compatible) := by
  apply ContinuousLinearMap.ext
  exact inclusion_cutoff dimension lower higher domain gap bound source target compatible cells

theorem cutoff_weak_integral (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (cells : Finset ℤ) (index : JetIndex order)
    (jet : WJet dimension order domain exponent) (cell : ℤ) (vector : PhysicalValue dimension)
    (test : TestFunction domain) :
    (∫ point in domain, test.toFun point • inner ℂ vector
        (fieldCutoff dimension domain cells (Realization.recoveredDerivative dimension order domain exponent index jet) point cell)) =
      (-1 : ℂ) ^ degree index * ∫ point in domain,
        Grad.WeakTesting.orderedTestDerivative (degree index) (derivativeWord index) test.toFun point •
          inner ℂ vector (fieldCutoff dimension domain cells (base dimension order domain exponent jet) point cell) := by
  rw [← recoveredDerivative_cutoff, ← cutoff_base]
  exact Realization.recoveredDerivative_integral dimension order domain exponent index
    (cutoff dimension order domain exponent cells jet) cell vector test

def centeredCells (radius : ℕ) : Finset ℤ := Finset.Icc (-(radius : ℤ)) radius

theorem centeredCells_monotone : Monotone centeredCells := by
  intro smaller larger bound cell membership
  simp only [centeredCells, Finset.mem_Icc] at membership ⊢
  constructor <;> omega

theorem centeredCells_cover (cell : ℤ) : ∃ radius : ℕ, cell ∈ centeredCells radius := by
  refine ⟨cell.natAbs, ?_⟩
  simp only [centeredCells, Finset.mem_Icc]
  omega

theorem centeredCells_cofinal : Tendsto centeredCells atTop atTop :=
  centeredCells_monotone.tendsto_atTop_finset centeredCells_cover

theorem cutoff_sequence_strong (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order domain exponent) :
    Tendsto (fun radius : ℕ => cutoff dimension order domain exponent (centeredCells radius) jet) atTop (𝓝 jet) :=
  (cutoff_strong dimension order domain exponent jet).comp centeredCells_cofinal

theorem common_sequence (dimension : ℕ) (domain : Set Spatial) {Index : Type*}
    (order : Index → ℕ) (exponent : ∀ index, JetIndex (order index) → ℕ)
    (jets : ∀ index, WJet dimension (order index) domain (exponent index))
    (field : FieldL2 dimension domain)
    (sameBase : ∀ index, base dimension (order index) domain (exponent index) (jets index) = field) :
    (∀ index, Tendsto (fun radius : ℕ =>
      cutoff dimension (order index) domain (exponent index) (centeredCells radius) (jets index)) atTop (𝓝 (jets index))) ∧
    (∀ (radius : ℕ) index,
      base dimension (order index) domain (exponent index)
          (cutoff dimension (order index) domain (exponent index) (centeredCells radius) (jets index)) =
        fieldCutoff dimension domain (centeredCells radius) field) := by
  constructor
  · intro index
    exact cutoff_sequence_strong dimension (order index) domain (exponent index) (jets index)
  · intro radius index
    rw [cutoff_base, sameBase]

theorem graphGrade_consumer (dimension order weight : ℕ) (domain : Set Spatial)
    (jet : GraphGrade dimension order weight domain) :
    Tendsto (fun radius : ℕ => cutoff dimension order domain (fun _ => weight) (centeredCells radius) jet)
      atTop (𝓝 jet) := cutoff_sequence_strong dimension order domain (fun _ => weight) jet

theorem mixed_consumer (dimension grade : ℕ) (domain : Set Spatial) (jet : Mixed dimension grade domain) :
    Tendsto (fun radius : ℕ => cutoff dimension grade domain (fun index => grade - degree index)
      (centeredCells radius) jet) atTop (𝓝 jet) :=
  cutoff_sequence_strong dimension grade domain (fun index => grade - degree index) jet

end Grad.WeightedJets.CellCutoff
