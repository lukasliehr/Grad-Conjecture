import ADW2ReciprocalOmegaMultipliers

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularOmegaGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularGrades Grad.AnnularFluxTrace
open Grad.CircularHighRegularity Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The two ORIGINAL r dr coordinates, stored as sqrt(r)y and
sqrt(r)omega^-1 y'. The ambient norm is their Hilbert sum. -/
abbrev AnnularOmegaAmbient (lower : ℝ) := PiLp 2 (fun _ : Fin 2 => AnnularBulk lower)

def annularOmegaValue (lower : ℝ) : AnnularOmegaAmbient lower →L[ℂ] AnnularBulk lower :=
  PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => AnnularBulk lower) 0

def annularOmegaSlope (lower : ℝ) : AnnularOmegaAmbient lower →L[ℂ] AnnularBulk lower :=
  PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 2 => AnnularBulk lower) 1

def annularOmegaNuCoordinates (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    AnnularOmegaAmbient lower →L[ℂ] AnnularFluxGraphAmbient lower :=
  (annularOmegaValue lower).prod ((annularOmegaToNu lower length positive lengthPositive).comp (annularOmegaSlope lower))

/-- Literal high-flux D_omega. Its derivative constraint is the accepted
actual weak graph transported by the proved omega/nu coefficient. -/
def annularOmegaGraph (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    Submodule ℂ (AnnularOmegaAmbient lower) :=
  (annularFluxWeakGraph lower positive).comap
    (annularOmegaNuCoordinates lower length positive lengthPositive).toLinearMap

theorem annularOmegaGraph_closed (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    IsClosed (annularOmegaGraph lower length positive lengthPositive : Set (AnnularOmegaAmbient lower)) :=
  (annularFluxWeakGraph_closed lower positive).preimage
    (annularOmegaNuCoordinates lower length positive lengthPositive).continuous

instance annularOmegaGraph_complete (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    CompleteSpace (annularOmegaGraph lower length positive lengthPositive) :=
  (annularOmegaGraph_closed lower length positive lengthPositive).completeSpace_coe

theorem annularOmegaGraph_norm_sq (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : annularOmegaGraph lower length positive lengthPositive) :
    ‖field‖ ^ 2 = ‖field.val 0‖ ^ 2 + ‖field.val 1‖ ^ 2 := by
  change ‖field.val‖ ^ 2 = _
  rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]

/-- The comparison map has the exact same actual derivative, after changing
only its displayed normalization. -/
theorem annularOmegaToNu_derivative (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : AnnularBulk lower) (mode : HighAnnularMode) :
    (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 : ℝ) •
      radialOrdinary 1 lower positive (annularOmegaToNu lower length positive lengthPositive field mode) =
      collarScalar 1 lower (annularOmegaCurve lower length positive mode)
        (radialOrdinary 1 lower positive (field mode)) := by
  rw [annularOmegaToNu, annularScalarFamily_ordinary]
  apply Lp.ext
  filter_upwards [Lp.coeFn_smul (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 : ℝ)
      (collarScalar 1 lower (annularOmegaOverNuCurve lower length positive mode) (radialOrdinary 1 lower positive (field mode))),
    collarScalar_ae 1 lower (annularOmegaOverNuCurve lower length positive mode) (radialOrdinary 1 lower positive (field mode)),
    collarScalar_ae 1 lower (annularOmegaCurve lower length positive mode) (radialOrdinary 1 lower positive (field mode))]
    with radius scaled left right
  rw [scaled, Pi.smul_apply, left, right, smul_smul]
  congr 1
  change _ * (_ / Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) = _
  field_simp [(Grad.AnnularFluxTrace.annularFrequency_pos mode).ne']

/-- Exact membership uses fixed-mode distributional tests and the ORIGINAL
omega, with no independent derivative or endpoint coordinates. -/
theorem annularOmegaGraph_mem_iff (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (field : AnnularOmegaAmbient lower) :
    field ∈ annularOmegaGraph lower length positive lengthPositive ↔
      ∀ mode, CollarWeakDerivative lower (radialOrdinary 1 lower positive (field 0 mode))
        (collarScalar 1 lower (annularOmegaCurve lower length positive mode)
          (radialOrdinary 1 lower positive (field 1 mode))) := by
  change (∀ mode, CollarWeakDerivative lower (radialOrdinary 1 lower positive (field 0 mode))
    ((Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 : ℝ) •
      radialOrdinary 1 lower positive (annularOmegaToNu lower length positive lengthPositive (field 1) mode))) ↔ _
  simp_rw [annularOmegaToNu_derivative]

def annularOmegaIntoNu (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length) :
    annularOmegaGraph lower length positive lengthPositive →L[ℂ] annularFluxWeakGraph lower positive :=
  ((annularOmegaNuCoordinates lower length positive lengthPositive).comp
    (annularOmegaGraph lower length positive lengthPositive).subtypeL).codRestrict
      (annularFluxWeakGraph lower positive) (fun field => field.property)

/-- The derivative coordinate is forced by the genuine weak value. -/
theorem annularOmegaGraph_value_injective (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) :
    Function.Injective (fun field : annularOmegaGraph lower length positive lengthPositive => field.val 0) := by
  intro first second same
  have pairSame : annularOmegaIntoNu lower length positive lengthPositive first =
      annularOmegaIntoNu lower length positive lengthPositive second :=
    annularFluxWeakGraph_value_injective lower positive bounded same
  have slopeSame := congrArg (fun field : annularFluxWeakGraph lower positive => field.val.2) pairSame
  have slopes : first.val 1 = second.val 1 :=
    annularOmegaToNu_injective lower length positive lengthPositive slopeSame
  apply Subtype.ext
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  · exact same
  · exact slopes

end Grad.AnnularOmegaGraph
