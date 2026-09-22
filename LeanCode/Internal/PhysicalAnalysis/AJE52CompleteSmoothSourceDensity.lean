import AJE51OriginalMeanFreeRetraction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set Filter
open scoped Topology BigOperators
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularLowEnergy
attribute [local instance] originalAmbientRealNormed

/-- Dense maps are assembled with their proofs before specializing to the
full original seven-coordinate carrier. -/
structure SourceDenseMap (E : Type) [TopologicalSpace E] where
  Core : Type
  mapping : Core → E
  dense : DenseRange mapping

def SourceDenseMap.pair {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (first : SourceDenseMap E) (second : SourceDenseMap F) :
    SourceDenseMap (WithLp 2 (E × F)) :=
  ⟨first.Core × second.Core,fun core => WithLp.toLp 2 (first.mapping core.1,second.mapping core.2),
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.surjective.denseRange.comp
      (first.dense.prodMap second.dense) (WithLp.prodContinuousLinearEquiv 2 ℝ E F).symm.continuous⟩

def SourceDenseMap.comp {E F : Type} [TopologicalSpace E] [TopologicalSpace F]
    (source : SourceDenseMap E) (mapping : E → F) (continuous : Continuous mapping)
    (surjective : Function.Surjective mapping) : SourceDenseMap F :=
  ⟨source.Core,fun core => mapping (source.mapping core),surjective.denseRange.comp source.dense continuous⟩

def graphSourceDenseMap (parameters : PhaseParameters) (lower : ℝ) :
    SourceDenseMap (lp (fun _ : ℤ × ℤ => WeightedRadialH1 1 lower) 2) :=
  ⟨(ℤ × ℤ) →₀ SmoothRadialCore 1,finiteSourceCore parameters 1 lower 0 0,
    finiteSourceCore_denseRange parameters 1 lower 0 0⟩

def radialSourceDenseMap (lower : ℝ) : SourceDenseMap (DivisionRow 1 lower) :=
  ⟨(ℤ × ℤ) →₀ SmoothRadialCore 1,finiteSmoothRadialSource 1 lower,finiteSmoothRadialSource_denseRange 1 lower⟩

def finiteBoundaryDenseMap (ι : Type) [DecidableEq ι] : SourceDenseMap (lp (fun _ : ι => ComplexEuclidean 1) 2) :=
  ⟨ι →₀ ComplexEuclidean 1,finiteLpSourceCore (LinearMap.id : ComplexEuclidean 1 →ₗ[ℝ] ComplexEuclidean 1),
    finiteLpSourceCore_denseRange _ Function.surjective_id.denseRange⟩

def outerSourceDenseMap (parameters : PhaseParameters) : SourceDenseMap (HighBoundaryPrimitive parameters 0 0) where
  Core := Finset (ℤ × ℤ) × HighBoundaryPrimitive parameters 0 0
  mapping core := outerDatumCut parameters 0 0 core.1 core.2
  dense := by
    intro field
    apply isClosed_closure.mem_of_tendsto (outerDatumCut_tendsto parameters 0 0 field)
    exact Filter.Eventually.of_forall (fun support => subset_closure ⟨(support,field),rfl⟩)

variable (parameters : PhaseParameters) (lower : ℝ)

def originalSmoothAmbientDenseMap : SourceDenseMap (OriginalStrongAmbient parameters lower 0 0) :=
  (((graphSourceDenseMap parameters lower).pair (graphSourceDenseMap parameters lower)).pair
    ((radialSourceDenseMap lower).pair (radialSourceDenseMap lower))).pair
    ((outerSourceDenseMap parameters).pair ((finiteBoundaryDenseMap HighAnnularMode).pair (finiteBoundaryDenseMap LowAnnularIndex)))

/-- Genuine smooth radial and finite Fourier sources are dense after the
actual meanfree retraction, retaining the SAME source graphs and independent data. -/
def originalSmoothStrongDenseMap (positive : 0 < lower) (bounded : lower ≤ 1) :
    SourceDenseMap (OriginalStrongCarrier parameters lower 0 0) :=
  (originalSmoothAmbientDenseMap parameters lower).comp (originalMeanFreeRetraction parameters lower)
    (originalMeanFreeRetraction parameters lower).continuous
    (originalMeanFreeRetraction_surjective parameters lower positive bounded)

def strongSmoothDenseMap (length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length) :
    SourceDenseMap (StrongDataCarrier parameters lower positive bounded 0 0) :=
  (originalSmoothStrongDenseMap parameters lower positive bounded).comp
    (originalStrongWeightEquivalence parameters lower length positive bounded lengthPositive 0 0)
    (originalStrongWeightEquivalence parameters lower length positive bounded lengthPositive 0 0).continuous
    (originalStrongWeightEquivalence parameters lower length positive bounded lengthPositive 0 0).surjective

/-- The dense weighted data use the explicit original reconstruction,
including the shared RF0 graph row and the actual angular Rg row. -/
theorem strongSmoothDenseMap_actual (length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (core : (originalSmoothAmbientDenseMap parameters lower).Core) :
    (strongSmoothDenseMap parameters lower length positive bounded lengthPositive).mapping core =
      originalToStrong parameters lower length positive bounded lengthPositive 0 0
        (originalMeanFreeRetraction parameters lower ((originalSmoothAmbientDenseMap parameters lower).mapping core)) :=
  originalStrongWeightEquivalence_eq_reconstruction parameters lower length positive bounded lengthPositive 0 0 _

end Grad.AnnularStrongOrbit
