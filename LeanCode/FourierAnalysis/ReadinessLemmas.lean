import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Abel

/- Reusable analytic constructions under explicit hypotheses.
   No original PDE carrier,
   density theorem, annular inverse, or nonlinear solution is assumed to have
   been constructed here. The generic hypotheses below remain explicit.

   Endpoint equivalences are bounded, not isometric: their constants may
   depend on fixed radii. Smooth-core inverse algebra uses LinearMap, not a
   fictitious same-grade bounded inverse. The concrete norm models preserve
   the X sum, Y Hilbert, and spatial Euclidean conventions. -/

noncomputable section

namespace Grad.ImplementationReadiness

section EndpointRestriction

universe u v w
variable {I : Type u} {X W : I → Type v}
  [∀ i, NormedAddCommGroup (X i)] [∀ i, NormedSpace ℝ (X i)]
  [∀ i, NormedAddCommGroup (W i)] [∀ i, NormedSpace ℝ (W i)]

/-- Conjugate a physical restriction into the endpoint-dependent retained
    coordinates. Instantiate only at the proved admissible annular radii. -/
def conjugatedRestriction {c d : I}
    (ec : X c ≃L[ℝ] W c) (ed : X d ≃L[ℝ] W d)
    (r : W c →L[ℝ] W d) : X c →L[ℝ] X d :=
  ed.symm.toContinuousLinearMap.comp (r.comp ec.toContinuousLinearMap)

theorem conjugatedRestriction_apply {c d : I}
    (ec : X c ≃L[ℝ] W c) (ed : X d ≃L[ℝ] W d)
    (r : W c →L[ℝ] W d) (x : X c) :
    conjugatedRestriction ec ed r x = ed.symm (r (ec x)) := rfl

theorem conjugatedRestriction_id {c : I} (ec : X c ≃L[ℝ] W c) :
    conjugatedRestriction ec ec (ContinuousLinearMap.id ℝ (W c)) =
      ContinuousLinearMap.id ℝ (X c) := by
  ext x
  simp [conjugatedRestriction]

/-- This proves functoriality from the actual physical restriction law;
    it assumes neither injectivity nor isometry of a restriction. -/
theorem conjugatedRestriction_comp {c d e : I}
    (ec : X c ≃L[ℝ] W c) (ed : X d ≃L[ℝ] W d)
    (ee : X e ≃L[ℝ] W e)
    (rcd : W c →L[ℝ] W d) (rde : W d →L[ℝ] W e)
    (rce : W c →L[ℝ] W e) (hr : rde.comp rcd = rce) :
    (conjugatedRestriction ed ee rde).comp
        (conjugatedRestriction ec ed rcd) =
      conjugatedRestriction ec ee rce := by
  ext x
  have h := congrArg (fun r : W c →L[ℝ] W e => r (ec x)) hr
  simpa [conjugatedRestriction] using congrArg ee.symm h

theorem conjugatedRestriction_norm_le {c d : I}
    (ec : X c ≃L[ℝ] W c) (ed : X d ≃L[ℝ] W d)
    (r : W c →L[ℝ] W d) :
    ‖conjugatedRestriction ec ed r‖ ≤
      ‖ed.symm.toContinuousLinearMap‖ * ‖r‖ * ‖ec.toContinuousLinearMap‖ := by
  calc
    ‖conjugatedRestriction ec ed r‖ ≤
        ‖ed.symm.toContinuousLinearMap‖ * ‖r.comp ec.toContinuousLinearMap‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖ed.symm.toContinuousLinearMap‖ *
        (‖r‖ * ‖ec.toContinuousLinearMap‖) :=
      mul_le_mul_of_nonneg_left
        (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ = _ := (mul_assoc _ _ _).symm

end EndpointRestriction

section SmoothCoreInverse

universe u v w
variable {E : Type u} {F : Type v} {G : Type w}
  [AddCommGroup E] [Module ℝ E]
  [AddCommGroup F] [Module ℝ F]
  [AddCommGroup G] [Module ℝ G]

/-- Two inverse laws in the two distinct smooth cores are sufficient.
    No norm or completion is involved in this algebraic identity. -/
theorem inverse_resolvent
    (Ab Ac : E →ₗ[ℝ] F) (Vb Vc : F →ₗ[ℝ] E)
    (hbR : ∀ f, Ab (Vb f) = f) (hcL : ∀ x, Vc (Ac x) = x) :
    Vc - Vb = -(Vc.comp ((Ac - Ab).comp Vb)) := by
  ext f
  simp [hbR, hcL, map_sub, neg_sub]

/-- Exact D1.5 noncommutative remainder. J is the proposed first variation
    of A. The statement does not assume it is already a derivative.
    The last word is Vc · DeltaA · Vb · DeltaA · Vb in that order. -/
theorem inverse_quadratic_remainder
    (Ab Ac J : E →ₗ[ℝ] F) (Vb Vc : F →ₗ[ℝ] E)
    (hbR : ∀ f, Ab (Vb f) = f) (hcL : ∀ x, Vc (Ac x) = x) :
    Vc - Vb + Vb.comp (J.comp Vb) =
      -(Vb.comp ((Ac - Ab - J).comp Vb)) +
        Vc.comp ((Ac - Ab).comp (Vb.comp ((Ac - Ab).comp Vb))) := by
  ext f
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.neg_apply,
    LinearMap.comp_apply, map_sub, hbR, hcL]
  abel

/-- The two-factor case of D1's exact product remainder, with typed
    noncommutative factors. Repeated use telescopes a longer prefix. -/
theorem product_quadratic_remainder
    (P0 P1 LP : E →ₗ[ℝ] F) (Q0 Q1 LQ : G →ₗ[ℝ] E) :
    P1.comp Q1 - P0.comp Q0 - (LP.comp Q0 + P0.comp LQ) =
      (P1 - P0 - LP).comp Q0 + P0.comp (Q1 - Q0 - LQ) +
        (P1 - P0).comp (Q1 - Q0) := by
  ext x
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.comp_apply,
    map_sub]
  abel

end SmoothCoreInverse

section NormModels

universe u v w
variable (H : Type u)

abbrev VectorBlock := PiLp 2 (fun _ : Fin 2 => H)

/-- Three independent normed blocks with a sum norm at both product nodes.
    Instantiate A,V,S with the actual graded axis/vector/scalar carriers.
    None of those carriers or their constraints is constructed here. -/
abbrev StateAmbient (A : Type u) (V : Type v) (S : Type w) :=
  WithLp 1 (A × WithLp 1 (V × S))

/-- Original four quotient coordinates, before imposing the real N38 range. -/
abbrev QuotientAmbient := PiLp 2 (fun _ : Fin 4 => H)

abbrev Spatial := EuclideanSpace ℝ (Fin 3)
abbrev Plane := EuclideanSpace ℝ (Fin 2)

variable {H}

def statePack {A : Type u} {V : Type v} {S : Type w}
    (a : A) (v : V) (s : S) : StateAmbient A V S :=
  WithLp.toLp 1 (a, WithLp.toLp 1 (v, s))

theorem statePack_norm {A : Type u} {V : Type v} {S : Type w}
    [NormedAddCommGroup A] [NormedAddCommGroup V] [NormedAddCommGroup S]
    (a : A) (v : V) (s : S) :
    ‖statePack a v s‖ = ‖a‖ + ‖v‖ + ‖s‖ := by
  simp [statePack, WithLp.prod_norm_eq_of_L1, add_assoc]

/-- Spatial derivative coordinates are flattened in the order y1,y2,zeta. -/
def spatialJoin (y : Plane) (zeta : ℝ) : Spatial :=
  WithLp.toLp 2 ![y 0, y 1, zeta]

theorem spatialJoin_norm_sq (y : Plane) (zeta : ℝ) :
    ‖spatialJoin y zeta‖ ^ 2 = ‖y‖ ^ 2 + ‖zeta‖ ^ 2 := by
  simp [spatialJoin, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_three,
    Fin.sum_univ_two]

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- Literal BS spin coordinates g_plus=f1+i f2, g_minus=f1-i f2. -/
def spinPack (f : VectorBlock H) (g h : H) : QuotientAmbient H :=
  WithLp.toLp 2 ![f 0 + Complex.I • f 1, f 0 - Complex.I • f 1, g, h]

/-- The squared vector weight is exactly two, not one or four. -/
theorem spinPack_norm_sq (f : VectorBlock H) (g h : H) :
    ‖spinPack f g h‖ ^ 2 = 2 * ‖f‖ ^ 2 + ‖g‖ ^ 2 + ‖h‖ ^ 2 := by
  have hp := parallelogram_law_with_norm ℂ (f 0) (Complex.I • f 1)
  simp only [norm_smul, Complex.norm_I, one_mul] at hp
  simpa [spinPack, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_four,
    Fin.sum_univ_two] using hp

-- These are example instance checks, not the original domain's carriers.
#synth NormedSpace ℝ (StateAmbient ℝ (VectorBlock ℂ) ℂ)
#synth CompleteSpace (StateAmbient ℝ (VectorBlock ℂ) ℂ)
#synth InnerProductSpace ℂ (QuotientAmbient ℂ)
#synth CompleteSpace (QuotientAmbient ℂ)
#synth InnerProductSpace ℝ Spatial
#synth CompleteSpace Spatial

end NormModels

#print axioms conjugatedRestriction
#print axioms conjugatedRestriction_apply
#print axioms conjugatedRestriction_id
#print axioms conjugatedRestriction_comp
#print axioms conjugatedRestriction_norm_le
#print axioms inverse_resolvent
#print axioms inverse_quadratic_remainder
#print axioms product_quadratic_remainder
#print axioms VectorBlock
#print axioms StateAmbient
#print axioms QuotientAmbient
#print axioms Spatial
#print axioms Plane
#print axioms statePack
#print axioms statePack_norm
#print axioms spatialJoin
#print axioms spatialJoin_norm_sq
#print axioms spinPack
#print axioms spinPack_norm_sq

#check @conjugatedRestriction_comp
#check @conjugatedRestriction_norm_le
#check @inverse_resolvent
#check @inverse_quadratic_remainder
#check @product_quadratic_remainder
#check @statePack_norm
#check @spatialJoin_norm_sq
#check @spinPack_norm_sq

end Grad.ImplementationReadiness
