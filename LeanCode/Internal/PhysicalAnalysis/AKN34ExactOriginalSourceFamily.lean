import AKN33OriginalDatumInsertedTransport

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology BigOperators

namespace Grad.ExhaustionSourceAllocation
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.SourceCollarFullSource Grad.SourceCollarCoefficients Grad.AnnularCurrentSource
open Grad.AxisCore Grad.QuotientProjection Grad.FlatSourceProjection Grad.ConstrainedGrades
open Grad.SourceCollarBulk Grad.AnnularStrongData Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularExhaustionEstimate Grad.AnnularStrongOrbit Grad.AnnularCrossOrbit
attribute [local instance] Grad.AnnularStrongOrbit.knownAmbientNormed Grad.AnnularStrongOrbit.knownAmbientSeminormed Grad.AnnularStrongOrbit.knownAmbientRealNormed Grad.AnnularStrongOrbit.knownAmbientRealModule
  Grad.AnnularStrongOrbit.strongCarrierNormed Grad.AnnularStrongOrbit.strongCarrierSeminormed Grad.AnnularStrongOrbit.strongCarrierRealNormed Grad.AnnularStrongOrbit.strongCarrierRealModule

theorem actualOriginalSourceDatum_inserted (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (lengthPositive : 0 < L) (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    StrongInsertedGrade parameters lower positive bounded.le grade
      (originalWeightedDatum parameters lower L positive bounded.le lengthPositive
        (actualOriginalSourceDatum parameters L rho epsilon field small lower positive bounded 0 source flat))
      (originalWeightedDatum parameters lower L positive bounded.le lengthPositive
        (actualOriginalSourceDatum parameters L rho epsilon field small lower positive bounded grade source flat)) := by
  apply originalWeightedDatum_inserted_sources parameters lower L positive bounded.le lengthPositive grade
  · exact actualOriginalF0Graph_inserted parameters lower positive bounded grade source
  · exact actualOriginalF2Graph_inserted parameters L lower positive bounded grade source
  · exact actualOriginalF1Row_inserted parameters lower positive bounded.le grade source
  · exact actualOriginalG3Row_inserted parameters L rho epsilon field small lower positive bounded.le grade source flat
  · rfl
  · rfl

/-- A fully supplied actual weighted source family, with constant before the
moving radii. All grades are insertions of the same four original source
blocks, at unchanged phase width, and all independent boundary data are zero. -/
theorem actualOriginalSourceFamily_uniform (parameters : PhaseParameters) (L : ℝ)
    (lengthPositive : 0 < L) (grade : ℕ) :
    ∃ constant : ℝ, 0 < constant ∧
      ∀ (rho epsilon : ℝ) (field : ACore parameters 3)
        (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
        (source : SmoothQuotient parameters) (flat : IsFlat source) (_vanishing : SourceHigherVanishing source)
        (radii : ℕ → ℝ) (positive : ∀ index, 0 < radii index) (bounded : ∀ index, radii index < 1),
        let data := fun index => actualOriginalSourceDatum parameters L rho epsilon field small
          (radii index) (positive index) (bounded index) 0 source flat
        ∃ weighted : ∀ index, StrongDataCarrier parameters (radii index) (positive index) (bounded index).le 0 0,
          ∀ index,
            StrongInsertedGrade parameters (radii index) (positive index) (bounded index).le grade
              (originalWeightedDatum parameters (radii index) L (positive index) (bounded index).le lengthPositive (data index))
              (weighted index) ∧
            ‖weighted index‖ ≤ constant * (‖quotientEta parameters (grade + 8) source‖ +
              physicalBudget parameters field rho epsilon (grade + 14) * ‖quotientEta parameters 8 source‖) := by
  refine ⟨originalSourceAllocationConstant parameters L grade,
    originalSourceAllocationConstant_positive parameters L grade, ?_⟩
  intro rho epsilon field small source flat vanishing radii positive bounded
  dsimp only
  refine ⟨fun index => originalWeightedDatum parameters (radii index) L (positive index) (bounded index).le lengthPositive
    (actualOriginalSourceDatum parameters L rho epsilon field small (radii index) (positive index) (bounded index) grade source flat), ?_⟩
  intro index
  exact ⟨actualOriginalSourceDatum_inserted parameters L rho epsilon lengthPositive field small
    (radii index) (positive index) (bounded index) grade source flat,
    actualOriginalSourceDatum_EX_bound parameters L rho epsilon lengthPositive field small grade
      (radii index) (positive index) (bounded index) source flat vanishing⟩

/-- Direct AKL input: the actual source at a coupled inverse context supplies
its own every-grade witness and original source norm bound. -/
theorem actualOriginalSourceDatum_exhaustion_inserted (parameters : PhaseParameters) (L compact rho epsilon : ℝ)
    (field : ACore parameters 3)
    (small : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (context : CoupledCoordinateContext parameters L compact) (grade : ℕ)
    (source : SmoothQuotient parameters) (flat : IsFlat source) :
    let bounded : context.lower < 1 := context.lowerHalf.trans_lt (by norm_num)
    let data := actualOriginalSourceDatum parameters L rho epsilon field small context.lower context.positive bounded 0 source flat
    ExhaustionDataInserted parameters L compact context grade data
      (originalWeightedDatum parameters context.lower L context.positive (context.lowerHalf.trans (by norm_num)) context.lengthPositive
        (actualOriginalSourceDatum parameters L rho epsilon field small context.lower context.positive bounded grade source flat)) := by
  dsimp only
  unfold ExhaustionDataInserted
  have zero : zeroBoundaryDatum parameters context.lower
      (actualOriginalSourceDatum parameters L rho epsilon field small context.lower context.positive
        (context.lowerHalf.trans_lt (by norm_num)) 0 source flat) =
      actualOriginalSourceDatum parameters L rho epsilon field small context.lower context.positive
        (context.lowerHalf.trans_lt (by norm_num)) 0 source flat := rfl
  rw [zero]
  exact actualOriginalSourceDatum_inserted parameters L rho epsilon context.lengthPositive field small context.lower context.positive
    (context.lowerHalf.trans_lt (by norm_num)) grade source flat

end Grad.ExhaustionSourceAllocation
