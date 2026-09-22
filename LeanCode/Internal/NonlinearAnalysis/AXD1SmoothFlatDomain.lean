import AXF9Reality
import AXJ7DomainFlatJets
import QR16StateReality

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 500000

namespace Grad.FlatDomainProjection

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.AxisJet
open Grad.SmoothingFamily Grad.Cor18 Grad.RealFixedRanges Grad.CompletedReality
open Grad.FlatSourceProjection Grad.ChartAxisProjections Grad.Q24Realization

variable {parameters : PhaseParameters}

/-- The scalar flat projection commutes with the actual real involution. -/
theorem scalarFlatProjection_conjugate (field : ACore parameters 1) :
    cartesianCoreConjugation parameters (scalarFlatProjection field) =
      scalarFlatProjection (cartesianCoreConjugation parameters field) := by
  rw [scalarFlatProjection_apply, map_sub, map_sub, scalarGradientCorrection_conjugate,
    angularCore_conjugate, neg_zero, scalarFlatProjection_apply, map_sub,
    angularCore_conjugate, neg_zero]

/-- Vanishing of the two accepted first traces is the literal vanishing of
the scalar origin gradient, cell by cell. -/
theorem scalarOriginGradient_eq_zero_iff_traceFirst (field : ACore parameters 1) :
    (∀ cell, scalarOriginGradient field cell = 0) ↔
      ∀ direction : Fin 2, traceFirst direction field = 0 := by
  constructor
  · intro gradient direction
    apply Subtype.ext
    funext cell
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate
    have value := congrArg (fun point : ComplexEuclidean 2 => point direction) (gradient cell)
    fin_cases direction
    · exact value
    · exact value
  · intro traces cell
    apply PiLp.ext
    intro direction
    fin_cases direction
    · have value := congrArg
        (fun family : Grad.AxisCore.AxisSmoothCore parameters 1 => family.val cell 0)
        (traces 0)
      exact value
    · have value := congrArg
        (fun family : Grad.AxisCore.AxisSmoothCore parameters 1 => family.val cell 0)
        (traces 1)
      exact value

theorem scalarOriginGradient_scalarFlatProjection (field : ACore parameters 1) :
    ∀ cell, scalarOriginGradient (scalarFlatProjection field) cell = 0 :=
  (scalarOriginGradient_eq_zero_iff_traceFirst _).2
    (fun direction => traceFirst_scalarFlatProjection direction field)

theorem smoothingToTangent_injective : Function.Injective (smoothingToTangent parameters) := by
  intro first second equality
  apply Grad.SmoothingFamily.axisToGrade_injective parameters.sigma0 0
  rw [← tangentToGrade_smoothing parameters 0 first,
    ← tangentToGrade_smoothing parameters 0 second, equality]

/-- RC01's fixed smooth flat-domain operation on the original state core:
kill the free axis coordinate, apply the actual N31 vector projection, and
apply the literal scalar mean/first-jet projection. -/
def flatDomainCoreProjection (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) :
    StateCore parameters →ₗ[ℂ] StateCore parameters :=
  (0 : Grad.SmoothingFamily.AxisCore parameters.sigma0 (ComplexEuclidean 2) →ₗ[ℂ]
      Grad.SmoothingFamily.AxisCore parameters.sigma0 (ComplexEuclidean 2)).comp
      (LinearMap.fst ℂ _ _)
    |>.prod
      (((vectorProjection parameters reference insideR).comp
          ((LinearMap.fst ℂ (ACore parameters 3) (ACore parameters 1)).comp
            (LinearMap.snd ℂ _ _))).prod
        ((scalarFlatProjection (parameters := parameters)).comp
          ((LinearMap.snd ℂ (ACore parameters 3) (ACore parameters 1)).comp
            (LinearMap.snd ℂ _ _))))

theorem flatDomainCoreProjection_apply
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (state : StateCore parameters) :
    flatDomainCoreProjection parameters reference insideR state =
      (0, vectorProjection parameters reference insideR state.2.1,
        scalarFlatProjection state.2.2) := by
  rfl

theorem flatDomainCoreProjection_conjugate
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (state : StateCore parameters) :
    xCoreConjugation parameters (flatDomainCoreProjection parameters reference insideR state) =
      flatDomainCoreProjection parameters reference insideR (xCoreConjugation parameters state) := by
  simp only [flatDomainCoreProjection_apply, xCoreConjugation, LinearMap.prodMap_apply]
  rw [map_zero, vectorProjection_conjugate, scalarFlatProjection_conjugate]

theorem flatDomainCoreProjection_fullConstraints
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (state : StateCore parameters) :
    FullConstraints parameters reference insideR
      (flatDomainCoreProjection parameters reference insideR state) := by
  rw [flatDomainCoreProjection_apply]
  exact ⟨vectorProjection_constraints parameters reference insideR state.2.1,
    scalarFlatProjection_mean state.2.2⟩

/-- The fixed smooth projection restricted to the actual real constrained
state slice. Its codomain proof includes the full N31 constraints and the
literal real involution. -/
def realFlatDomainProjection (parameters : PhaseParameters)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) :
    stateSmoothRange parameters reference insideR →ₗ[ℝ]
      stateSmoothRange parameters reference insideR where
  toFun state := ⟨flatDomainCoreProjection parameters reference insideR state.val, by
    apply (mem_stateSmoothRange parameters reference insideR _).2
    constructor
    · exact fullProjection_fixes parameters reference insideR _
        (flatDomainCoreProjection_fullConstraints reference insideR state.val)
    · rw [flatDomainCoreProjection_conjugate]
      have real := ((mem_stateSmoothRange parameters reference insideR state.val).1 state.property).2
      rw [real]⟩
  map_add' first second := Subtype.ext
    ((flatDomainCoreProjection parameters reference insideR).map_add first.val second.val)
  map_smul' scalar state := Subtype.ext
    (((flatDomainCoreProjection parameters reference insideR).restrictScalars ℝ).map_smul
      scalar state.val)

theorem realFlatDomainProjection_coe
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (state : stateSmoothRange parameters reference insideR) :
    (realFlatDomainProjection parameters reference insideR state).val =
      (0, vectorProjection parameters reference insideR state.val.2.1,
        scalarFlatProjection state.val.2.2) := rfl

/-- On the already constrained original state core, the N31 component is
literally unchanged. -/
theorem realFlatDomainProjection_vector
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (state : stateSmoothRange parameters reference insideR) :
    vectorProjection parameters reference insideR state.val.2.1 = state.val.2.1 := by
  have fixed := ((mem_stateSmoothRange parameters reference insideR state.val).1 state.property).1
  rw [fullProjection_apply] at fixed
  exact congrArg (fun value : StateCore parameters => value.2.1) fixed

theorem realFlatDomainProjection_mem_ker
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (state : stateSmoothRange parameters reference insideR) :
    realFlatDomainProjection parameters reference insideR state ∈
      LinearMap.ker (realChartKappa parameters reference insideR) := by
  rw [LinearMap.mem_ker, realChartKappa_eq_zero_iff]
  constructor
  · exact map_zero (smoothingToTangent parameters)
  · exact scalarOriginGradient_scalarFlatProjection state.val.2.2

theorem realFlatDomainProjection_fixes
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (state : stateSmoothRange parameters reference insideR)
    (flat : state ∈ LinearMap.ker (realChartKappa parameters reference insideR)) :
    realFlatDomainProjection parameters reference insideR state = state := by
  rw [LinearMap.mem_ker, realChartKappa_eq_zero_iff] at flat
  apply Subtype.ext
  rw [realFlatDomainProjection_coe, realFlatDomainProjection_vector]
  have axisZero : state.val.1 = 0 := by
    apply smoothingToTangent_injective
    rw [flat.1, map_zero]
  have meanZero : angularCore parameters 0 state.val.2.2 = 0 := by
    have fixed := ((mem_stateSmoothRange parameters reference insideR state.val).1 state.property).1
    rw [fullProjection_apply] at fixed
    have scalar := congrArg (fun value : StateCore parameters => value.2.2) fixed
    exact sub_eq_self.mp scalar
  rw [scalarFlatProjection_fixes state.val.2.2 meanZero
    ((scalarOriginGradient_eq_zero_iff_traceFirst state.val.2.2).1 flat.2)]
  exact Prod.ext axisZero.symm rfl

theorem realFlatDomainProjection_idempotent
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (state : stateSmoothRange parameters reference insideR) :
    realFlatDomainProjection parameters reference insideR
        (realFlatDomainProjection parameters reference insideR state) =
      realFlatDomainProjection parameters reference insideR state :=
  realFlatDomainProjection_fixes reference insideR _
    (realFlatDomainProjection_mem_ker reference insideR state)

/-- Exact smooth range: the actual fixed flat-domain projection has range
precisely `ker(realChartKappa)`. -/
theorem realFlatDomainProjection_range_iff
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (state : stateSmoothRange parameters reference insideR) :
    state ∈ LinearMap.range (realFlatDomainProjection parameters reference insideR) ↔
      state ∈ LinearMap.ker (realChartKappa parameters reference insideR) := by
  constructor
  · rintro ⟨source, rfl⟩
    exact realFlatDomainProjection_mem_ker reference insideR source
  · intro flat
    exact ⟨state, realFlatDomainProjection_fixes reference insideR state flat⟩

end Grad.FlatDomainProjection
