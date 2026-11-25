module

public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective
public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.RingTheory.KrullDimension.PID
public import Mathlib.RingTheory.OrderOfVanishing.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableIffOfLeOfLe
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthQuotientMaximalIdealPowSmulTop
public import Mathlib.RingTheory.Localization.Finiteness
public import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankIInfKerOfIsBaseChange
public import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral
public import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg
public import Development.AbelianVarietyTheory.Definitions.Foundations.CanonicalExponents
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelCharacterEqProdSuperdiagonalSum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCuspFormsFullLattice
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelLiftModuliLawsOfCore
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KeepsCuspOfIsUnifAt
public import Development.AutomorphicArithmetic.LocalEmbeddings.RootInCore
public import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableInfRestrictScalarsOfLeSpan, Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerSemilinear, Development.AutomorphicArithmetic.LocalEmbeddings.KeepsOfGood

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableInfRestrictScalarsOfLeSpan =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableInfRestrictScalarsOfLeSpan", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective\npublic import Mathlib.Algebra.Module.Lattice.Full\npublic import Mathlib.RingTheory.KrullDimension.PID\npublic import Mathlib.RingTheory.OrderOfVanishing.Basic\npublic import Mathlib.RingTheory.RegularLocalRing.Defs\npublic import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableIffOfLeOfLe\npublic import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthQuotientMaximalIdealPowSmulTop\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.Order.CompletePartialOrder\nimport Mathlib.RingTheory.OrderOfVanishing.Noetherian\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.SimpleRing.Principal\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.RingTheory.Localization.Finiteness\n\n"}
section -- clump:auto
@[expose] public section

open IsDiscreteValuationRing Pointwise

namespace GlobalTheory

section Span

variable {R : Type*} (K : Type*) {V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

theorem exists_ne_zero_smul_mem_of_mem_span_fractionField {M : Submodule R V} {x : V}
    (hx : x ∈ Submodule.span K (M : Set V)) : ∃ a : R, a ≠ 0 ∧ a • x ∈ M := by
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span (nonZeroDivisors R) K _ x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t, nonZeroDivisors.coe_ne_zero t, ht⟩

theorem span_inf_restrictScalars_eq {M : Submodule R V} {W : Submodule K V}
    (h : W ≤ Submodule.span K (M : Set V)) :
    Submodule.span K ((M ⊓ W.restrictScalars R : Submodule R V) : Set V) = W := by
  refine le_antisymm (Submodule.span_le.mpr fun x hx => hx.2) fun x hx => ?_
  obtain ⟨a, ha, hax⟩ := exists_ne_zero_smul_mem_of_mem_span_fractionField K (h hx)
  have ha' : algebraMap R K a ≠ 0 := by simpa using ha
  rw [← Submodule.smul_mem_iff _ ha', algebraMap_smul]
  exact Submodule.subset_span ⟨hax, W.smul_of_tower_mem a hx⟩

variable {K}


variable [IsPrincipalIdealRing R]

end Span

section FractionField

variable {R K V : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K]
  [Algebra R K] [IsFractionRing R K] [AddCommGroup V] [Module R V] [Module K V]
  [IsScalarTower R K V]




end FractionField

end GlobalTheory
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableInfRestrictScalarsOfLeSpan =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerSemilinear =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerSemilinear", "h": "module\n\npublic import Formalism.LocalToGlobal.IndefiniteReal.GramCEqTranspose\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt\npublic import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.LengthCommensurableInfRestrictScalarsOfLeSpan\npublic import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed\npublic import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankIInfKerOfIsBaseChange\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open Module
open scoped TensorProduct NumberField

namespace GlobalTheory.BadCount.RankRead

theorem finrank_iInf_ker_semilinear {L M W X ι κ : Type} [Field L] [Field M] [AddCommGroup W] [Module L W] [AddCommGroup X]
    [Module M X] [Finite ι] [Finite κ] {σ : L →+* M} (Φ : W →ₛₗ[σ] X) (b : Basis κ L W) (hb : LinearIndependent M fun k => Φ (b k))
    (a : ι → W →ₗ[L] W) (a' : ι → X →ₗ[M] X) (h : ∀ i w, a' i (Φ w) = Φ (a i w)) :
    finrank L (⨅ i, LinearMap.ker (a i) : Submodule L W) =
      finrank M ((⨅ i, LinearMap.ker (a' i)) ⊓ Submodule.span M (Set.range Φ) : Submodule M X) := by
  haveI := Module.Finite.of_basis b
  letI : Algebra L M := σ.toAlgebra
  letI : Module L X := Module.compHom X σ
  haveI : IsScalarTower L M X := ⟨fun x y z => mul_smul (σ x) y z⟩
  let U := Submodule.span M (Set.range Φ)
  let f : W →ₗ[L] U :=
    { toFun := fun w => ⟨Φ w, Submodule.subset_span ⟨w, rfl⟩⟩
      map_add' := fun x y => Subtype.ext (map_add Φ x y)
      map_smul' := fun x y => Subtype.ext (map_smulₛₗ Φ x y) }
  have hU : U = Submodule.span M (Set.range fun k => Φ (b k)) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (by rintro _ ⟨k, rfl⟩; exact ⟨_, rfl⟩))
    rintro _ ⟨w, rfl⟩
    haveI := Fintype.ofFinite κ

    rw [← b.sum_repr w, map_sum]
    exact Submodule.sum_mem _ fun k _ => by
      rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  let c : Basis κ M U := (Basis.span hb).map (LinearEquiv.ofEq _ _ hU.symm)
  have hc : ∀ k, c k = f (b k) := fun k => Subtype.ext (by simp [c, f])
  have hf : IsBaseChange M f := by
    refine IsBaseChange.of_equiv ((Algebra.TensorProduct.basis M b).equiv c (Equiv.refl _)) fun m => ?_
    have : ((((Algebra.TensorProduct.basis M b).equiv c (Equiv.refl _)).toLinearMap.restrictScalars L) ∘ₗ
        TensorProduct.mk L M W 1) = f := b.ext fun k => by
      rw [← hc]
      simp [← Algebra.TensorProduct.basis_apply]
    exact LinearMap.congr_fun this m
  have hm : ∀ i, ∀ x ∈ U, a' i x ∈ U := fun i => Submodule.span_le (p := U.comap (a' i)) |>.2 (by
    rintro _ ⟨w, rfl⟩
    exact Submodule.subset_span ⟨_, (h i w).symm⟩)
  rw [← GlobalTheory.finrank_iInf_ker_of_isBaseChange L M W U ι f a (fun i => (a' i).restrict (hm i)) hf
    (fun i w => Subtype.ext (h i w)), ← Submodule.finrank_map_subtype_eq U]
  refine congrArg (fun N : Submodule M X => finrank M N) (Submodule.ext fun x => ?_)
  simp only [Submodule.mem_map, Submodule.mem_iInf, LinearMap.mem_ker, Submodule.mem_inf]
  exact ⟨by rintro ⟨y, hy, rfl⟩; exact ⟨fun i => congrArg Subtype.val (hy i), y.2⟩,
    fun ⟨h1, h2⟩ => ⟨⟨x, h2⟩, fun i => Subtype.ext (h1 i), rfl⟩⟩

def twistExt {F M V Γ : Type} [Field F] [Field M] [Algebra F M] [AddCommGroup V] [Module F V] [Group Γ]
    (τ : Representation F Γ V) (χ : Γ →* Mˣ) : Representation M Γ (M ⊗[F] V) where
  toFun γ := ((χ γ : Mˣ) : M) • (τ γ).baseChange M
  map_one' := by simp [Module.End.one_eq_id]
  map_mul' γ δ := by
    rw [map_mul, map_mul, LinearMap.baseChange_mul, Units.val_mul, smul_mul_smul_comm]

theorem twistExt_tmul {F M V Γ : Type} [Field F] [Field M] [Algebra F M] [AddCommGroup V] [Module F V] [Group Γ]
    (τ : Representation F Γ V) (χ : Γ →* Mˣ) (γ : Γ) (m : M) (v : V) :
    twistExt τ χ γ (m ⊗ₜ[F] v) = ((χ γ : Mˣ) : M) • (m ⊗ₜ[F] τ γ v) := rfl

theorem finrank_eq {K L F M C W V G G' Γ : Type} [Field K] [Field L] [Field F] [Field M] [Algebra K L] [Algebra F M]
    [AddCommGroup C] [Module K C] [AddCommGroup W] [Module L W] [Module K W] [IsScalarTower K L W] [AddCommGroup V] [Module F V]
    [Group G] [Fintype G] [Group G'] [Group Γ] [Finite Γ] {j : K →+* F} (σ : L →+* M)
    (hσ : ∀ a, σ (algebraMap K L a) = algebraMap F M (j a)) (ε : C →ₗ[K] W) (π : C →ₛₗ[j] V) {n : ℕ} (b : Fin n → C)
    (b₁ : Submodule.span K (Set.range b) = ⊤) (b₂ : LinearIndependent L fun k => ε (b k))
    (b₃ : Submodule.span L (Set.range fun k => ε (b k)) = ⊤) (b₄ : LinearIndependent F fun k => π (b k))
    (ρ : G →* (W →ₗ[L] W)) (chi : G →* Lˣ) (τ : Representation F Γ V) (θ : Γ →* G) (c : G ≃* G') (s : G' →* Γ)
    (hs : ∀ g, θ (s (c g)) = g) (hρ : ∀ γ f, ∃ f', ρ (θ γ) (ε f) = ε f' ∧ τ γ (π f) = π f')
    (hinv : ∀ v, (∀ γ, θ γ = 1 → τ γ v = v) → v ∈ Submodule.span F (Set.range π))
    (P : Subgroup G) (lam : P →* Lˣ) (Q : Subgroup Γ) (hQ : ∀ γ, γ ∈ Q ↔ θ γ ∈ P) (lamb : Q →* Mˣ)
    (hlam : ∀ γ : Q, ((lamb γ : Mˣ) : M) = σ (lam ⟨θ γ, (hQ _).1 γ.2⟩ : Lˣ))
    (S : Submodule L W) (hS : ∀ w, w ∈ S ↔ ∀ p : P, ρ p w = ((chi p * lam p : Lˣ) : L) • w)
    (eC : G → L) (e : MonoidAlgebra M G') (he : ∀ g, σ (eC g) = e.coeff (c g)) :
    finrank L S = finrank M (eig (twistExt τ ((Units.map (σ : L →* M)).comp (chi.comp θ))⁻¹) Q lamb) ∧
    finrank L (S ⊓ LinearMap.ker (∑ g, (eC g * ((chi g)⁻¹ : Lˣ)) • ρ g) : Submodule L W) =
      finrank M (eig (twistExt τ ((Units.map (σ : L →* M)).comp (chi.comp θ))⁻¹) Q lamb ⊓
        LinearMap.ker (Representation.asAlgebraHom ((twistExt τ ((Units.map (σ : L →* M)).comp (chi.comp θ))⁻¹).comp s :
          Representation M G' (M ⊗[F] V)) e) : Submodule M (M ⊗[F] V)) := by
  set R := twistExt τ ((Units.map (σ : L →* M)).comp (chi.comp θ))⁻¹ with hR
  let bW : Basis (Fin n) L W := Basis.mk b₂ b₃.ge
  let Φ : W →ₛₗ[σ] M ⊗[F] V :=
    { toFun := fun w => ∑ k, σ (bW.repr w k) • ((1 : M) ⊗ₜ[F] π (b k))
      map_add' := fun x y => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun x y => by simp [Finset.smul_sum, mul_smul] }
  have hΦb : ∀ k, Φ (bW k) = (1 : M) ⊗ₜ[F] π (b k) := fun k => by
    show ∑ l, σ (bW.repr (bW k) l) • _ = _
    rw [Finset.sum_eq_single k (fun l _ hl => by simp [Finsupp.single_eq_of_ne hl]) (by simp)]
    simp
  have hΦ : ∀ f, Φ (ε f) = (1 : M) ⊗ₜ[F] π f := fun f => by
    have hf : f ∈ Submodule.span K (Set.range b) := b₁ ▸ Submodule.mem_top
    induction hf using Submodule.span_induction with
    | mem _ h => obtain ⟨k, rfl⟩ := h; rw [← hΦb, Basis.mk_apply]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy, map_add (f := _), TensorProduct.tmul_add]
    | smul t x _ hx =>
      rw [map_smul, ← algebraMap_smul L, map_smulₛₗ, hx, map_smulₛₗ, hσ, algebraMap_smul, TensorProduct.tmul_smul]
  have hind : LinearIndependent M fun k => Φ (bW k) := by
    simp only [hΦb]
    exact Module.Flat.linearIndependent_one_tmul b₄
  have hRΦ : ∀ γ w, R γ (Φ w) = Φ ((((chi (θ γ))⁻¹ : Lˣ) : L) • ρ (θ γ) w) := fun γ w => by
    rw [← bW.sum_repr w]

    simp only [map_sum, map_smulₛₗ, Finset.smul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    obtain ⟨f', h1, h2⟩ := hρ γ (b k)
    rw [hΦb, Basis.mk_apply, h1, hΦ, hR, twistExt_tmul, h2, smul_comm]
    simp
  have hE : eig R Q lamb ≤ Submodule.span M (Set.range Φ) := fun x hx => by
    have h0 := GlobalTheory.GaloisDescent.span_image_iInf (TensorProduct.isBaseChange F V M)
      fun γ : θ.ker => LinearMap.ker (τ γ - LinearMap.id)
    have h1 : x ∈ Submodule.span M (TensorProduct.mk F M V 1 ''
        (⨅ γ : θ.ker, LinearMap.ker (τ γ - LinearMap.id) : Submodule F V)) := by
      rw [h0, Submodule.mem_iInf]
      intro γ
      have hγ : θ γ = 1 := γ.2
      have hq : (γ : Γ) ∈ Q := (hQ _).2 (hγ ▸ P.one_mem)
      rw [GlobalTheory.GaloisDescent.span_image_ker (TensorProduct.isBaseChange F V M) (TensorProduct.isBaseChange F V M) _
        ((τ γ).baseChange M - LinearMap.id) (fun v => by simp [TensorProduct.tmul_sub])]
      have := (mem_eig R Q lamb x).1 hx ⟨γ, hq⟩
      rw [hlam, show (⟨θ γ, (hQ _).1 hq⟩ : P) = 1 from Subtype.ext hγ] at this
      simpa [hR, twistExt, hγ, sub_eq_zero] using this
    refine Submodule.span_le.2 ?_ h1
    rintro _ ⟨v, hv, rfl⟩
    have hv' := hinv v fun γ hγ => sub_eq_zero.1 ((Submodule.mem_iInf _).1 hv ⟨γ, hγ⟩)
    clear hv
    induction hv' using Submodule.span_induction with
    | mem _ h => obtain ⟨f, rfl⟩ := h; exact Submodule.subset_span ⟨_, hΦ f⟩
    | zero => simp
    | add x y _ _ hx hy =>
      change (TensorProduct.mk F M V 1) (x + y) ∈ Submodule.span M (Set.range Φ)
      rw [map_add]
      exact add_mem hx hy
    | smul t x _ hx => rw [map_smul, ← algebraMap_smul M]; exact Submodule.smul_mem _ _ hx
  let a : Q → W →ₗ[L] W := fun γ => (((chi (θ γ))⁻¹ : Lˣ) : L) • ρ (θ γ) - ((lam ⟨θ γ, (hQ _).1 γ.2⟩ : Lˣ) : L) • LinearMap.id
  let a' : Q → M ⊗[F] V →ₗ[M] M ⊗[F] V := fun γ => R γ - ((lamb γ : Mˣ) : M) • LinearMap.id
  have ha : ∀ γ w, a' γ (Φ w) = Φ (a γ w) := fun γ w => by
    simp only [a, a', LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hRΦ, map_sub, map_smulₛₗ, hlam]
  have hSa : S = ⨅ γ, LinearMap.ker (a γ) := by
    ext w
    have key : ∀ (g : G) (x : Lˣ), (((chi g)⁻¹ : Lˣ) : L) • ρ g w - (x : L) • w = 0 ↔ ρ g w = ((chi g * x : Lˣ) : L) • w :=
      fun g x => by rw [sub_eq_zero, ← Units.smul_def, inv_smul_eq_iff, Units.smul_def, smul_smul, Units.val_mul]
    rw [hS, Submodule.mem_iInf]
    refine ⟨fun h γ => (key _ _).2 (h ⟨θ γ, (hQ _).1 γ.2⟩), fun h p => ?_⟩
    have := (key _ _).1 (h ⟨s (c p), (hQ _).2 (by rw [hs]; exact p.2)⟩)
    simpa only [hs] using this
  have hEa : eig R Q lamb = ⨅ γ, LinearMap.ker (a' γ) := rfl
  refine ⟨by rw [hSa, finrank_iInf_ker_semilinear Φ bW hind a a' ha, ← hEa, inf_eq_left.2 hE], ?_⟩
  have h2 := finrank_iInf_ker_semilinear Φ bW hind (fun o : Option Q => o.elim (∑ g, (eC g * ((chi g)⁻¹ : Lˣ)) • ρ g) a)
    (fun o => o.elim (Representation.asAlgebraHom (R.comp s : Representation M G' (M ⊗[F] V)) e) a') (by
      rintro (_ | γ) w
      · haveI := Fintype.ofEquiv G c.toEquiv
        simp only [Option.elim]

        rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum_fintype _ _ (fun _ => by simp),
        LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
        refine (Fintype.sum_equiv c.toEquiv _ _ fun g => ?_).symm
        rw [LinearMap.smul_apply, LinearMap.smul_apply, mul_smul, map_smulₛₗ, he]
        exact congrArg _ (by rw [MonoidHom.comp_apply, hRΦ]; simp only [MulEquiv.toEquiv_eq_coe, EquivLike.coe_coe, hs])
      · exact ha γ w)
  rw [iInf_option, iInf_option] at h2
  simp only [Option.elim] at h2
  rw [hSa, inf_comm]
  refine h2.trans (congrArg (fun N : Submodule M (M ⊗[F] V) => finrank M N) ?_)
  rw [← hEa, inf_assoc, inf_eq_left.2 hE, inf_comm]

theorem rkK_inf {LL Ks WL G : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL] [AddCommGroup WL]
    [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL] [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL]
    [IsScalarTower (𝓞 Ks) Ks WL] {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)] [Group G]
    (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G) (hK : A.IsKsForm) (hM : A.MKFull) (S : Submodule LL WL) :
    Formalism.HN.rkK (Submodule.span (𝓞 LL) (A.MK : Set WL) ⊓ S.restrictScalars (𝓞 LL)) = finrank LL S := by
  obtain ⟨n, b, h1, -, -, -, h5⟩ := hK
  have h : S ≤ Submodule.span LL (Submodule.span (𝓞 LL) (A.MK : Set WL) : Set WL) := by
    refine le_top.trans (h5.ge.trans (Submodule.span_le.2 ?_))
    rintro _ ⟨k, rfl⟩
    exact Submodule.span_mono Submodule.subset_span (Submodule.span_le_restrictScalars Ks LL _ (hM.2 ▸ h1 k))
  rw [Formalism.HN.rkK, GlobalTheory.span_inf_restrictScalars_eq LL h]

end GlobalTheory.BadCount.RankRead
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerSemilinear =====

-- ===== clump member: Development.AutomorphicArithmetic.LocalEmbeddings.KeepsOfGood =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.LocalEmbeddings.KeepsOfGood", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings\npublic import Formalism.LocalToGlobal.ProjectiveLattices.HalfOneAddSqrtNegIsIntegral\npublic import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.OrthonormalBaseFrameNeg\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.CanonicalExponents\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelCharacterEqProdSuperdiagonalSum\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerSemilinear\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCuspFormsFullLattice\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelLiftModuliLawsOfCore\npublic import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KeepsCuspOfIsUnifAt\npublic import Development.AutomorphicArithmetic.LocalEmbeddings.RootInCore\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\npublic import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace GlobalTheory.CovTop.BadRep

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.BigTop GlobalTheory.AllWt GlobalTheory.CovTop GlobalTheory.BadCount
open GlobalTheory.LevDesc (TypeFrame IsTypeLevel typeRed typeEmb grpHR grpGHR transl levelGU)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters (Sq LevelGroup levelU psiU unitri superDiag)
open GlobalTheory.LevPull (CongMod)
open Formalism.MainNotions.ArithmeticCylinders
open scoped TensorProduct

section Group

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]



theorem whit_data (R : RealDat D A Ks) (F : Face D A) (hlevels : R.grp_levels F) (c : G ≃* G0g D.nd)
    (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1)
    (hpin : ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (c g kv)) :
    ∃ (Pb : Subgroup (G0g D.nd)) (lam : Pb →* ℂˣ)
      (ψ : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ), IsWhit D Pb lam ψ ∧
      (∀ g, c g ∈ Pb ↔ g ∈ (F.lvl false).P) ∧
      ∀ g (h : c g ∈ Pb) (h' : g ∈ (F.lvl false).P), ((lam ⟨c g, h⟩ : ℂˣ) : ℂ) =
        D.what₂.embLL (((F.lvl false).ψ⁻¹ ⟨g, h'⟩ : D.what₂.LLˣ) : D.what₂.LL) := by
  classical
  obtain ⟨ψ0, hgen, hlev, -⟩ := hlevels
  let P := (F.lvl false).P
  let Pb : Subgroup (G0g D.nd) := P.map c.toMonoidHom
  have hPb : ∀ g, g ∈ Pb ↔ c.symm g ∈ P := fun g => Subgroup.mem_map_equiv
  let toP : Pb →* P := (c.symm.toMonoidHom.comp Pb.subtype).codRestrict P fun x => (hPb x).1 x.2
  let lam : Pb →* ℂˣ := (Units.map (D.what₂.embLL : D.what₂.LL →* ℂ)).comp ((F.lvl false).ψ⁻¹.comp toP)
  let ψC : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), AddChar (ZMod (D.host.g kv.1)) ℂ := fun kv =>
    (ψ0 (plg kv).1).compAddMonoidHom ((iso kv).toAddMonoidHom.comp (-AddMonoidHom.id _))
  have hmemP : ∀ x : G, x ∈ P ↔ ∀ kv, c x kv ∈ unitri D.R.r (ZMod (D.host.g kv.1)) := by
    intro x
    have e1 : x ∈ P ↔ R.eG x ∈ (R.levR F false).H := by
      show _ ↔ R.eG.symm (R.eG x) ∈ P
      rw [MulEquiv.symm_apply_apply]
    rw [e1, hlev, GlobalTheory.TypeBase.mem_lastZeroOrthImageSubspace_iff, ← plg.forall_congr_right]
    refine forall_congr' fun kv => ?_
    rw [hpin, GlobalTheory.TypeBase.bc_mem_unip_iff]
  refine ⟨Pb, lam, ψC, ⟨fun kv h => hgen (plg kv).1 (plg kv).2 (AddChar.ext _ _ fun y => ?_), fun g => ?_, fun g => ?_⟩,
    fun g => by rw [hPb, MulEquiv.symm_apply_apply], fun g h h' => ?_⟩
  · obtain ⟨x, rfl⟩ := (iso kv).surjective y
    have := DFunLike.congr_fun h (-x)
    simpa [ψC] using this
  · rw [hPb, hmemP]
    refine forall_congr' fun kv => ?_
    rw [MulEquiv.apply_symm_apply, isUniUp_iff]
  · have hx : c.symm (g : G0g D.nd) ∈ P := (hPb _).1 g.2
    have hxH : R.eG (c.symm g) ∈ (R.levR F false).H := by
      show R.eG.symm (R.eG _) ∈ P
      rw [MulEquiv.symm_apply_apply]
      exact hx
    have e1 : (R.levR F false).chi ⟨_, hxH⟩ = Units.map (D.what₂.embLL : D.what₂.LL →* ℂ)
        ((F.lvl false).ψ ⟨R.eG.symm (R.eG (c.symm g)), hxH⟩) := rfl
    rw [show (⟨R.eG.symm (R.eG (c.symm g)), hxH⟩ : P) = ⟨c.symm g, hx⟩ from
      Subtype.ext (MulEquiv.symm_apply_apply _ _)] at e1
    have key : ∀ X : LevelP R.Pg D.R.r ℂ, X = P0 R.Pg D.R.r ψ0 → ∀ y (hy : y ∈ X.H),
        ((X.chi ⟨y, hy⟩ : ℂˣ) : ℂ) = ∏ PP : R.Pg, ψ0 PP.1 (edgeSum supEdge (y PP)) := by
      rintro X rfl y hy
      exact GlobalTheory.TypeBase.baseLevelCharacter_eq_prod_superdiagonalSum _ _ _ y hy
    have h3 := key _ hlev _ hxH
    rw [e1] at h3
    have ht : toP g = ⟨c.symm g, hx⟩ := rfl
    show ((Units.map (D.what₂.embLL : D.what₂.LL →* ℂ) ((F.lvl false).ψ⁻¹ (toP g)) : ℂˣ) : ℂ) = _
    rw [ht, MonoidHom.inv_apply, map_inv, Units.val_inv_eq_inv_val, h3, ← plg.prod_comp, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun kv _ => ?_
    rw [hpin, MulEquiv.apply_symm_apply, GlobalTheory.TypeBase.edgeSum_bc, sum_entN]
    show _ = ψ0 (plg kv).1 ((iso kv) (-(superDiag _)))
    rw [map_neg, AddChar.map_neg_eq_inv]
    rfl
  · have ht : toP ⟨c g, h⟩ = ⟨g, h'⟩ := Subtype.ext (c.symm_apply_apply g)
    show ((Units.map (D.what₂.embLL : D.what₂.LL →* ℂ) ((F.lvl false).ψ⁻¹ (toP ⟨c g, h⟩)) : ℂˣ) : ℂ) = _
    rw [ht]
    rfl



theorem half_data (R : RealDat D A Ks) (c : G ≃* G0g D.nd)
    (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ R.Pg) (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1)
    (hpin : ∀ g kv, R.eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (c g kv))
    (ε : Sq D.host ≃ R.Pg) (iso' : ∀ v : Sq D.host, ZMod (D.host.g v.1) ≃+* kP (ε v).1) (t : LevelGroup D.host ≃* G)
    (t1 : ∀ u v, R.eG (t u) (ε v) = Formalism.UG.bc (iso' v : ZMod (D.host.g v.1) →+* kP (ε v).1) (u v)) (k : Fin 2) :
    ∃ H : Subgroup (G0g D.nd), IsHalf D k H ∧ ∀ u, c (t u) ∈ H ↔ u ∈ levelGU D.host k := by
  refine ⟨Subgroup.pi {kv | kv.1 ≠ k} fun kv => unitri D.R.r (ZMod (D.host.g kv.1)),
    fun g => forall_congr' fun kv => imp_congr_right fun _ => (isUniUp_iff _).symm, fun u => ?_⟩
  refine ((ε.trans plg.symm).forall_congr fun v => ?_).symm
  have he : plg ((ε.trans plg.symm) v) = ε v := plg.apply_symm_apply _
  generalize (ε.trans plg.symm) v = kv at he
  have hk : v.1 = kv.1 := idx_eq (iso' v) (iso kv) (by rw [he])
  show (v.1 ≠ k → _) ↔ (kv.1 ≠ k → _)
  rw [hk]
  refine imp_congr_right fun _ => ?_
  show u v ∈ unitri D.R.r (ZMod (D.host.g v.1)) ↔ c (t u) kv ∈ unitri D.R.r (ZMod (D.host.g kv.1))
  rw [← GlobalTheory.TypeBase.bc_mem_unip_iff (iso' v), ← GlobalTheory.TypeBase.bc_mem_unip_iff (iso kv), ← hpin, ← t1, he]

end Group

section Point

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}



theorem keeps_of_good {T : CoreJ D} (hJ : LawsJ T) {j : ℕ} (hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q) (Y : Deep T.toCore j) {e : ℕ}
    {o : ℝ} (hY : Y.Good e o) {G : WTZ D.host.E} (hG : Even G.2) : GlobalTheory.LevDesc.KeepsCusp Y.U G := by
  have hA := hY.lev.2
  have hM : Y.d.l₂.M = D.host.g 0 * D.host.g 1 * Y.d.pd := by rw [hY.lev.1.2.1, hJ.pins.2.1.1]
  have hχ := fun σ hσ => GlobalTheory.AllWt.Model.chi_modelWt (Y.U σ) (hY.chiTriv σ hσ) G hG
  obtain ⟨ι, hι, -, hpin⟩ := hY.adPin
  refine GlobalTheory.LevelKeeps.keepsCusp_of_isUnf hpq hA hG hY.unf (fun σ hσ k k' => ?_) (fun σ hσ => ?_) hχ
  · obtain ⟨hr, hW⟩ := hY.modelW σ hσ
    exact ⟨(hW k).1.trans (hW k').1.symm, (hW k).2.trans (hW k').2.symm⟩
  · obtain ⟨hr, hW⟩ := hY.modelW σ hσ
    obtain ⟨th, _, hth, hD⟩ := hY.dictU σ hσ
    obtain ⟨x₀, h0, _, g, e, F, ik, φ, th', hth', hL⟩ := hpin σ hσ
    obtain rfl : th = th' := funext fun k => funext fun τ =>
      GlobalTheory.LettersCheck.isInfEmb_unique τ.1 _ _ (hth k τ) (hth' k τ)
    exact GlobalTheory.LevelKeeps.mem_group (hY.unf σ hσ) hA ((hY.unf σ hσ).1 ▸ hpq) hr hW h0 (hM ▸ hY.levelK) hth hD fun h => by
      obtain ⟨γ, -, -, -, h3⟩ := hL.2 h
      exact ⟨_, h3⟩

theorem basis_of_form {K M R V : Type} [Field K] [Field M] [Algebra K M] [AddCommGroup R] [Module K R] [AddCommGroup V]
    [Module K V] [Module M V] {C C' : Submodule K R} (hC : C' = C) {W : Submodule K V} (e : C ≃ₗ[K] W) {n : ℕ} (b : Fin n → V)
    (h1 : ∀ k, b k ∈ W) (h2 : LinearIndependent K b) (h3 : Submodule.span K (Set.range b) = W) :
    ∃ (ε : C' →ₗ[K] V) (b' : Fin n → C'), (∀ (f : C') (h : (f : R) ∈ C), ε f = e ⟨f, h⟩) ∧ (∀ k, ε (b' k) = b k) ∧
      LinearIndependent K b' ∧ Submodule.span K (Set.range b') = ⊤ := by
  subst hC
  have hb : ∀ k, (W.subtype ∘ₗ e.toLinearMap) (e.symm ⟨b k, h1 k⟩) = b k := fun k => by simp
  refine ⟨W.subtype ∘ₗ e.toLinearMap, fun k => e.symm ⟨b k, h1 k⟩, fun f h => rfl, hb, ?_, ?_⟩
  · exact LinearIndependent.of_comp (W.subtype ∘ₗ e.toLinearMap) (by convert h2 using 1; exact funext hb)
  · refine Submodule.map_injective_of_injective (f := W.subtype ∘ₗ e.toLinearMap)
      (W.injective_subtype.comp e.injective) ?_
    rw [Submodule.map_span, ← Set.range_comp, show (W.subtype ∘ₗ e.toLinearMap) ∘ (fun k => e.symm ⟨b k, h1 k⟩) = b from funext hb,
      h3, Submodule.map_top, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top, Submodule.range_subtype]


theorem rank_gen {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
    {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}
    (fw : FWTie T R κ v₀) (Fc : Face D A) (i : Fin D.R.m) (act : G → T.R ((i : ℕ) + 1) →ₗ[T.Q.c.F] T.R ((i : ℕ) + 1))
    (hρ : ActRho R i (T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n) (fw.e i) act)
    {C : Submodule T.Q.c.F (T.R ((i : ℕ) + 1))} (hC : C = T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n)
    {F V Γ G' : Type} [Field F] [Algebra F ℂ] [AddCommGroup V] [Module F V] [Group Γ] [Finite Γ] [Group G']
    {j : T.Q.c.F →+* F} (hj : ∀ a, algebraMap F ℂ (j a) = T.σ₀ a) (π : C →ₛₗ[j] V) (τ : Representation F Γ V) (θ : Γ →* G)
    (q1 : ∀ (m : ℕ) (b : Fin m → C), LinearIndependent T.Q.c.F b → LinearIndependent F fun k => π (b k))
    (q2 : ∀ γ (v : C), ∃ hv : act (θ γ) v ∈ C, τ γ (π v) = π ⟨_, hv⟩)
    (q3 : ∀ v, (∀ γ, θ γ = 1 → τ γ v = v) → v ∈ Submodule.span F (Set.range π))
    (c : G ≃* G') (s : G' →* Γ) (hs : ∀ g, θ (s (c g)) = g) (Q : Subgroup Γ)
    (hQ : ∀ γ, γ ∈ Q ↔ θ γ ∈ (Fc.lvl false).P) (lamb : Q →* ℂˣ)
    (hlam : ∀ γ : Q, ((lamb γ : ℂˣ) : ℂ) =
      D.what₂.embLL (((Fc.lvl false).ψ⁻¹ ⟨θ γ, (hQ _).1 γ.2⟩ : D.what₂.LLˣ) : D.what₂.LL))
    (e0 : MonoidAlgebra ℂ G') (he : ∀ g, D.what₂.embLL ((idemOf A.X).coeff g) = e0.coeff (c g)) :
    ∃ (ρ : Representation ℂ Γ (ℂ ⊗[F] V)) (χ : Γ →* ℂˣ),
      (∀ (g : Γ) (v : V), ρ g ((1 : ℂ) ⊗ₜ[F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[F] τ g v)) ∧
      Formalism.HN.rkK (latType R Fc i) = Module.finrank ℂ (eig ρ Q lamb) ∧
      Formalism.HN.rkK (CovTop.latBad R Fc i) = Module.finrank ℂ (eig ρ Q lamb ⊓
        LinearMap.ker (Representation.asAlgebraHom (ρ.comp s : Representation ℂ G' (ℂ ⊗[F] V)) e0) :
          Submodule ℂ (ℂ ⊗[F] V)) := by
  obtain ⟨n, b, b1, b2, b3, b4, b5⟩ := fw.ks i
  obtain ⟨ε, b', e1, e2, e3, e4⟩ := basis_of_form (M := D.what₂.LL) hC (fw.e i) b b1 b2 b3
  have H := GlobalTheory.BadCount.RankRead.finrank_eq (M := ℂ) D.what₂.embLL
    (fun a => (RingHom.congr_fun (res_embLL T fw.alg_eq fw.laws.pins.2.2.1) a).trans (hj a).symm) ε π b' e4
    (by simpa only [e2] using b4) (by simpa only [e2] using b5) (q1 n b' e3)
    (R.FW i).ρ (R.FW i).chi τ θ c s hs
    (fun γ f => by
      obtain ⟨hv, h⟩ := q2 γ f
      have hf : (f : T.R ((i : ℕ) + 1)) ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n := hC ▸ f.2
      obtain ⟨hf', h'⟩ := hρ (θ γ) ⟨f, hf⟩
      exact ⟨⟨_, hv⟩, by rw [e1 f hf, e1 ⟨_, hv⟩ hf']; exact h'.symm, h⟩)
    q3 (Fc.lvl false).P (Fc.lvl false).ψ⁻¹ Q hQ lamb hlam (spType R Fc i) (fun _ => Iff.rfl)
    (fun g => (idemOf A.X).coeff g) e0 he
  have hM := GlobalTheory.GoodLat.Obj.mkFull_of_tie fw i
  refine ⟨_, _, fun g v => GlobalTheory.BadCount.RankRead.twistExt_tmul _ _ _ _ _,
    (GlobalTheory.BadCount.RankRead.rkK_inf _ (fw.ks i) hM _).trans H.1, Eq.trans ?_ H.2⟩
  rw [← GlobalTheory.BadCount.RankRead.rkK_inf _ (fw.ks i) hM, Submodule.restrictScalars_inf, ← inf_assoc]
  rfl


theorem rep_data {T : CoreJ D} (hT : LawsJ T) {j : ℕ} (hj : InR D j) (Y : Deep T.toCore j) {e : ℕ} {o : ℝ} (hY : Y.Good e o)
    {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} (hD : Dom a n) {G : Type} [Group G]
    (lev : G → (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)
    (hact : ActLev (Xo := T.Q.Xo j) T.Q.c (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))))
    (hk : ∀ g, ∀ f ∈ T.cuspA j a n, actLev (Xo := T.Q.Xo j) T.Q.c
      (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))) g f ∈ T.cuspA j a n)
    (θ : LevelAut (T.Q.Dw j) Y.d.l₂ →* G) (h1 : ∀ γ, CongMod T.Q.l.Mb (liftLa γ) (lev (θ γ)))
    (h2 : ∀ γ, CongMod T.Q.l.Mb (liftLa γ) LinearMap.id → θ γ = 1) :
    ∃ (π : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n) →ₛₗ[((Y.d.eF : Y.c'.F →+* Y.d.c₂.F).comp (incF T.Q.c Y.c' Y.hle))]
        Y.V (wtZ a n)) (τ : Representation Y.d.c₂.F (LevelAut (T.Q.Dw j) Y.d.l₂) (Y.V (wtZ a n))),
      (∀ g v, (τ g v : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v) ∧
      (∀ (m : ℕ) (b : Fin m → cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)), LinearIndependent T.Q.c.F b →
        LinearIndependent Y.d.c₂.F fun k => π (b k)) ∧
      (∀ γ (v : cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n)), ∃ hv : actLev (Xo := T.Q.Xo j) T.Q.c
        (fun g => (lev g, (LinearMap.id : (T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La))) (θ γ) v ∈
          cuspW (T.Q.Xo j) T.Q.c (T.U j) (wtZ a n), τ γ (π v) = π ⟨_, hv⟩) ∧
      (∀ v, (∀ γ, θ γ = 1 → τ γ v = v) → v ∈ Submodule.span Y.d.c₂.F (Set.range π)) := by
  have hpq : 1 ≤ (T.Q.Dw j).p + (T.Q.Dw j).q := by
    have hL := (GlobalTheory.LevGeo.laws_of_coreJ D T j hT hj).1
    obtain ⟨hp, hq, -⟩ := hL.dat
    obtain ⟨h1, h2⟩ := hj
    have hk := D.R.m_add_three_le_k
    rw [hp, hq]
    simp only [Ranks.sigW]
    omega
  have hA' : Y.d.l₂.A.Coprime Y.d.l₂.M := by rw [hY.lev.2]; exact Nat.coprime_one_left _
  have hKC : GlobalTheory.LevDesc.KeepsCusp Y.U (wtZ a n) := keeps_of_good hT hpq Y hY ((Int.even_coe_nat _).2 hD.2)
  obtain ⟨π, q1, q2, q3⟩ := pull_data D T j Y e o hT hj hY a n hD G lev hact hk θ h1
  have hτ := GlobalTheory.LevDesc.coe_cuspRep Y.U (wtZ a n) hpq hA' hKC
  exact ⟨π, _, hτ, q1, fun γ v => (q2 γ v).imp fun hv h => Subtype.ext ((hτ γ _).trans h),
    fun v hv => q3 v fun γ hγ => (hτ γ v).symm.trans (congrArg Subtype.val (hv γ (h2 γ hγ)))⟩

end Point

end GlobalTheory.CovTop.BadRep
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.LocalEmbeddings.KeepsOfGood =====
