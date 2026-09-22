import AXF15FlatSourceDensity

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatSourceProjection

open Grad.CartesianState Grad.RealFixedRanges Grad.ChartAxisProjections
open Grad.CompletedReality Grad.QuotientProjection
open Filter
open scoped Topology

theorem sourceCellTruncation_conjugate (parameters : PhaseParameters) (cutoff : ℕ)
    (source : SmoothQuotient parameters) :
    zCoreConjugation parameters (sourceCellTruncation parameters cutoff source) =
      sourceCellTruncation parameters cutoff (zCoreConjugation parameters source) := by
  funext row
  exact cartesianCoreTruncation_conjugation_commute parameters cutoff (source (spinSwap row))

theorem sourceCellTruncation_real_flat (parameters : PhaseParameters)
    (cellLength : ℝ) (positive : 0 < cellLength) (cutoff : ℕ)
    (source : LinearMap.ker (realExtraction parameters cellLength)) :
    sourceCellTruncation parameters cutoff source.val.val ∈ sourceSmoothRange parameters := by
  have flat := sourceCellTruncation_flat cutoff source.val.val
    ((source_isFlat_iff_kernel cellLength positive source.val).mpr source.property)
  apply (mem_sourceSmoothRange parameters _).mpr
  refine ⟨quotientProjection_fixes parameters _ flat.1, ?_⟩
  rw [sourceCellTruncation_conjugate,
    ((mem_sourceSmoothRange parameters source.val.val).mp source.val.property).2]

def realFlatCellTruncation (parameters : PhaseParameters) (cellLength : ℝ)
    (positive : 0 < cellLength) (cutoff : ℕ)
    (source : LinearMap.ker (realExtraction parameters cellLength)) :
    LinearMap.ker (realExtraction parameters cellLength) :=
  ⟨⟨sourceCellTruncation parameters cutoff source.val.val,
    sourceCellTruncation_real_flat parameters cellLength positive cutoff source⟩,
      (source_isFlat_iff_kernel cellLength positive _).mp
        (sourceCellTruncation_flat cutoff source.val.val
          ((source_isFlat_iff_kernel cellLength positive source.val).mpr source.property))⟩

theorem realFlatCellTruncation_outside (parameters : PhaseParameters) (cellLength : ℝ)
    (positive : 0 < cellLength) (cutoff : ℕ)
    (source : LinearMap.ker (realExtraction parameters cellLength))
    (cell : ℤ) (outside : cell ∉ centeredCellBox cutoff) (row : Fin 4) :
    (((realFlatCellTruncation parameters cellLength positive cutoff source).val.val) row).val cell = 0 := by
  exact if_neg outside

theorem sourceCellTruncation_tendsto (parameters : PhaseParameters) (grade : ℕ)
    (source : SmoothQuotient parameters) :
    Tendsto (fun cutoff : ℕ => quotientEta parameters grade
      (sourceCellTruncation parameters cutoff source)) atTop
        (𝓝 (quotientEta parameters grade source)) := by
  let equiv := PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 4 => AGrade parameters 1 grade)
  apply equiv.toHomeomorph.isEmbedding.tendsto_nhds_iff.mpr
  apply tendsto_pi_nhds.mpr
  intro row
  exact (aGradeEta parameters).continuous.continuousAt.tendsto.comp
    (tendsto_cartesianCoreTruncation_every_grade parameters (source row) grade)

theorem realFlatCellTruncation_tendsto (parameters : PhaseParameters) (cellLength : ℝ)
    (positive : 0 < cellLength) (grade : ℕ) (large : 3 ≤ grade)
    (source : LinearMap.ker (realExtraction parameters cellLength)) :
    Tendsto (fun cutoff : ℕ => flatSmoothEmbedding parameters cellLength positive grade large
      (realFlatCellTruncation parameters cellLength positive cutoff source)) atTop
        (𝓝 (flatSmoothEmbedding parameters cellLength positive grade large source)) := by
  apply tendsto_subtype_rng.mpr
  apply tendsto_subtype_rng.mpr
  exact sourceCellTruncation_tendsto parameters grade source.val.val

end Grad.FlatSourceProjection
