module

public import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RepresentationTheory.Invariants
public import Mathlib.RepresentationTheory.Irreducible
public import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetOperatorsCommOfAntiInvolution
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqTopOfStable, Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandPairSphericalVectorUnique

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqTopOfStable =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqTopOfStable", "h": "module\n\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable\npublic import Mathlib.Basic.Complex.Basic\npublic import Mathlib.RepresentationTheory.Invariants\npublic import Mathlib.RepresentationTheory.Irreducible\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\npublic import Mathlib.LinearAlgebra.Eigenspace.Triangularizable\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\npublic import Mathlib.LinearAlgebra.Eigenspace.Basic\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

namespace GlobalTheory.GroupAverageProjection

open GlobalTheory.PRep

section Mean

variable {H V : Type} [Group H] [AddCommGroup V] [Module ℂ V]

theorem sum_out_comp (N : Subgroup H) [Fintype (H ⧸ N)] (f : H → V) (hf : ∀ k, ∀ n ∈ N, f (k * n) = f k)
    (φ : H → H) (σ : H ⧸ N ≃ H ⧸ N) (hσ : ∀ k : H, σ (k : H ⧸ N) = (φ k : H ⧸ N)) :
    ∑ q : H ⧸ N, f (φ q.out) = ∑ q : H ⧸ N, f q.out := by
  rw [← σ.sum_comp (fun q : H ⧸ N => f q.out)]
  refine Finset.sum_congr rfl fun q _ => ?_
  have h : ((φ q.out : H) : H ⧸ N) = (((σ q).out : H) : H ⧸ N) := by
    rw [← hσ, QuotientGroup.out_eq', QuotientGroup.out_eq']
  have := hf (φ q.out) _ (QuotientGroup.eq.1 h)
  rw [← this, mul_inv_cancel_left]

def mean (τ : Representation ℂ H V) (N : Subgroup H) [Fintype (H ⧸ N)] : V →ₗ[ℂ] V :=
  (Fintype.card (H ⧸ N) : ℂ)⁻¹ • ∑ q : H ⧸ N, τ q.out

theorem mean_apply (τ : Representation ℂ H V) (N : Subgroup H) [Fintype (H ⧸ N)] (v : V) :
    mean τ N v = (Fintype.card (H ⧸ N) : ℂ)⁻¹ • ∑ q : H ⧸ N, τ q.out v := by
  simp [mean, LinearMap.sum_apply]

theorem card_ne (N : Subgroup H) [Fintype (H ⧸ N)] : (Fintype.card (H ⧸ N) : ℂ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

theorem apply_mean (τ : Representation ℂ H V) (N : Subgroup H) [Fintype (H ⧸ N)] {v : V}
    (hv : ∀ n ∈ N, τ n v = v) (k : H) : τ k (mean τ N v) = mean τ N v := by

  rw [mean_apply, map_smul, map_sum]
  congr 1
  have := sum_out_comp N (fun x => τ x v) (fun x n hn => by simp [hv n hn]) (fun x => k * x)
    (MulAction.toPerm k) (fun _ => rfl)
  simpa using this

theorem mean_apply_apply (τ : Representation ℂ H V) (N : Subgroup H) [N.Normal] [Fintype (H ⧸ N)] {v : V}
    (hv : ∀ n ∈ N, τ n v = v) (k : H) : mean τ N (τ k v) = mean τ N v := by
  rw [mean_apply, mean_apply]
  congr 1
  have := sum_out_comp N (fun x => τ x v) (fun x n hn => by simp [hv n hn]) (fun x => x * k)
    (Equiv.mulRight (k : H ⧸ N)) (fun _ => rfl)
  simpa using this

theorem mean_of_fixed (τ : Representation ℂ H V) (N : Subgroup H) [Fintype (H ⧸ N)] {v : V}
    (hv : ∀ k, τ k v = v) : mean τ N v = v := by
  rw [mean_apply]
  simp only [hv, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (card_ne N), one_smul]

def aug (τ : Representation ℂ H V) : Submodule ℂ V := Submodule.span ℂ {w | ∃ k v, w = τ k v - v}

theorem mean_sub_mem (τ : Representation ℂ H V) (N : Subgroup H) [Fintype (H ⧸ N)] (v : V) :
    mean τ N v - v ∈ aug τ := by
  have : mean τ N v - v = (Fintype.card (H ⧸ N) : ℂ)⁻¹ • ∑ q : H ⧸ N, (τ q.out v - v) := by
    rw [mean_apply, Finset.sum_sub_distrib, smul_sub, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ (card_ne N), one_smul]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => Submodule.subset_span ⟨_, _, rfl⟩)

theorem exists_projector (τ : Representation ℂ H V)
    (hτ : ∀ v, ∃ N : Subgroup H, N.Normal ∧ N.FiniteIndex ∧ ∀ n ∈ N, τ n v = v) :
    ∃ e : V →ₗ[ℂ] τ.invariants, (∀ v : τ.invariants, e v = v) ∧ (∀ k v, e (τ k v) = e v) ∧
      ∀ (N : Subgroup H) [Fintype (H ⧸ N)] (v : V), (∀ n ∈ N, τ n v = v) → (e v : V) = mean τ N v := by
  have hd : Disjoint τ.invariants (aug τ) := by
    have key : ∀ w ∈ aug τ, ∃ N : Subgroup H, N.Normal ∧ N.FiniteIndex ∧
        ∀ M : Subgroup H, M ≤ N → M.Normal → ∀ [Fintype (H ⧸ M)], mean τ M w = 0 := by
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨k, v, rfl⟩ := hw
        obtain ⟨N, h1, h2, h3⟩ := hτ v
        refine ⟨N, h1, h2, fun M hM _ _ => ?_⟩
        rw [map_sub, mean_apply_apply τ M (fun n hn => h3 n (hM hn)), sub_self]
      | zero => exact ⟨⊤, inferInstance, inferInstance, fun M _ _ _ => map_zero _⟩
      | add x y _ _ hx hy =>
        obtain ⟨N, h1, h2, h3⟩ := hx
        obtain ⟨N', h1', h2', h3'⟩ := hy
        refine ⟨N ⊓ N', inferInstance, inferInstance, fun M hM hn _ => ?_⟩
        rw [map_add (f := _), h3 M (hM.trans inf_le_left) hn, h3' M (hM.trans inf_le_right) hn, add_zero]
      | smul c x _ hx =>
        obtain ⟨N, h1, h2, h3⟩ := hx
        exact ⟨N, h1, h2, fun M hM hn _ => by rw [map_smul, h3 M hM hn, smul_zero]⟩
    rw [Submodule.disjoint_def]
    intro w hw hw'
    obtain ⟨N, h1, h2, h3⟩ := key w hw'
    letI : Fintype (H ⧸ N) := Fintype.ofFinite _
    rw [← mean_of_fixed τ N hw, h3 N le_rfl h1]
  have hc : Codisjoint τ.invariants (aug τ) := by
    rw [codisjoint_iff, eq_top_iff]
    intro v _
    obtain ⟨N, h1, h2, h3⟩ := hτ v
    letI : Fintype (H ⧸ N) := Fintype.ofFinite _
    have : v = mean τ N v - (mean τ N v - v) := by abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (apply_mean τ N h3))
      (Submodule.mem_sup_right (mean_sub_mem τ N v))
  have hcomp : IsCompl τ.invariants (aug τ) := ⟨hd, hc⟩
  obtain ⟨e, he1, he2⟩ : ∃ e : V →ₗ[ℂ] τ.invariants, (∀ v : τ.invariants, e v = v) ∧ ∀ w ∈ aug τ, e w = 0 :=
    ⟨τ.invariants.linearProjOfIsCompl _ hcomp, fun v => Submodule.linearProjOfIsCompl_apply_left hcomp v,
      fun w hw => Submodule.linearProjOfIsCompl_apply_right hcomp ⟨w, hw⟩⟩
  refine ⟨e, he1, fun k v => ?_, fun N _ v hv => ?_⟩
  · rw [← sub_eq_zero, ← map_sub]
    exact he2 _ (Submodule.subset_span ⟨_, _, rfl⟩)
  · have h1 := he2 _ (mean_sub_mem τ N v)
    rw [map_sub, sub_eq_zero] at h1
    rw [← h1]
    exact congrArg Subtype.val (he1 ⟨_, apply_mean τ N hv⟩)

end Mean

section Hecke

variable {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]

theorem hecke_comm (K : Subgroup G) (θ : G → G) (hmul : ∀ x y, θ (x * y) = θ y * θ x) (hinv : ∀ x, θ (θ x) = x)
    (hdc : ∀ g, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b) (ρ : Representation ℂ G W)
    (hτ : ∀ v, ∃ N : Subgroup K, N.Normal ∧ N.FiniteIndex ∧ ∀ n ∈ N, ρ (n : K) v = v)
    (e : W →ₗ[ℂ] W) (he : ∀ (k : K) v, e (ρ k v) = e v)
    (hm : ∀ (N : Subgroup K) [Fintype (K ⧸ N)] (v : W), (∀ n ∈ N, ρ (n : K) v = v) →
      e v = mean (ρ.comp K.subtype) N v)
    (v : W) (hv : ∀ k : K, ρ k v = v) (g h : G) : e (ρ g (e (ρ h v))) = e (ρ h (e (ρ g v))) := by
  have hS : ∀ a ∈ K, ∀ b ∈ K, ∀ x, e (ρ (a * x * b) v) = e (ρ x v) := by
    intro a ha b hb x
    simp only [map_mul, Module.End.mul_apply]
    rw [hv ⟨b, hb⟩, he ⟨a, ha⟩]
  have hSθ : ∀ x, e (ρ (θ x) v) = e (ρ x v) := by
    intro x
    obtain ⟨a, ha, b, hb, hx⟩ := hdc x
    rw [hx, hS a ha b hb]
  have hK : ∀ k ∈ K, θ k ∈ K := by
    intro k hk
    obtain ⟨a, ha, b, hb, hx⟩ := hdc k
    rw [hx]
    exact K.mul_mem (K.mul_mem ha hk) hb
  have h1 : θ 1 = 1 := by
    have := hmul 1 1
    rw [mul_one] at this
    exact (mul_eq_left.1 this.symm)
  have hi : ∀ x, θ x⁻¹ = (θ x)⁻¹ := by
    intro x
    rw [eq_inv_iff_mul_eq_one, ← hmul, mul_inv_cancel, h1]
  let ψ : K →* K := MonoidHom.mk' (fun k => ⟨(θ k)⁻¹, K.inv_mem (hK _ k.2)⟩) (by
    intro a b
    ext
    simp [hmul])
  have hψ : Function.Involutive ψ := by
    intro k
    ext
    show (θ (θ k)⁻¹)⁻¹ = k
    rw [hi, inv_inv, hinv]
  obtain ⟨N₁, n1, f1, p1⟩ := hτ (ρ g v)
  obtain ⟨N₂, n2, f2, p2⟩ := hτ (ρ h v)
  let M : Subgroup K := N₁ ⊓ N₂
  haveI : (M.comap ψ).FiniteIndex := ⟨by
    rw [Subgroup.index_comap_of_surjective _ hψ.surjective]; exact Subgroup.FiniteIndex.index_ne_zero⟩
  let N : Subgroup K := M ⊓ M.comap ψ
  haveI : N.Normal := inferInstance
  haveI : N.FiniteIndex := inferInstance
  letI : Fintype (K ⧸ N) := Fintype.ofFinite _
  have hN : N ≤ N.comap ψ := by
    intro n hn
    refine ⟨hn.2, ?_⟩
    show ψ (ψ n) ∈ M
    rw [hψ n]
    exact hn.1
  have hψ' : Function.Involutive (QuotientGroup.map N N ψ hN) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H k => simp [hψ k]
  obtain ⟨a, ha, b, hb, hh⟩ := hdc h
  obtain ⟨c, hc, d, hd, hg⟩ := hdc g
  rw [hm N (ρ h v) (fun n hn => p2 n hn.1.2), hm N (ρ g v) (fun n hn => p1 n hn.1.1), mean_apply, mean_apply]

  simp only [map_smul, map_sum]
  congr 1
  have := sum_out_comp N (fun k : K => e (ρ h (ρ k (ρ g v))))
    (fun k n hn => by simp [p1 n hn.1.1]) (fun k => ⟨b, hb⟩ * (ψ k)⁻¹ * ⟨c, hc⟩)
    (((hψ'.toPerm.trans (Equiv.inv _)).trans (Equiv.mulLeft ((⟨b, hb⟩ : K) : K ⧸ N))).trans
      (Equiv.mulRight ((⟨c, hc⟩ : K) : K ⧸ N))) (fun _ => rfl)
  refine Eq.trans (Finset.sum_congr rfl fun q _ => ?_) this
  have e1 := hSθ (g * (q.out : K) * h)
  have e2 := hS a ha d hd (h * (b * θ (q.out : K) * c) * g)
  have e3 : θ (g * (q.out : K) * h) = a * (h * (b * θ (q.out : K) * c) * g) * d := by
    rw [hmul, hmul, hh, hg]; group
  rw [e3, e2] at e1
  have e4 : (((⟨b, hb⟩ * (ψ q.out)⁻¹ * ⟨c, hc⟩ : K)) : G) = b * θ (q.out : K) * c := by
    simp [ψ]
  rw [e4]
  simp only [map_mul, Module.End.mul_apply] at e1 ⊢
  exact e1.symm

theorem eq_top_of_stable (ρ : Representation ℂ G W) (hρ : ρ.IsIrreducible) {U : Submodule ℂ W} (e : W →ₗ[ℂ] U)
    (he : ∀ u : U, e u = u) (E : Submodule ℂ U) (hE : E ≠ ⊥) (hs : ∀ g, ∀ u ∈ E, e (ρ g u) ∈ E) : E = ⊤ := by
  let S : Subrepresentation ρ :=
    { toSubmodule := ⨅ g : G, (E.comap e).comap (ρ g)
      apply_mem_toSubmodule := by
        intro g v hv
        simp only [Submodule.mem_iInf, Submodule.mem_comap] at hv ⊢
        intro x
        simpa using hv (x * g) }
  rcases eq_bot_or_eq_top S with h | h
  · exfalso
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hE
    have h1 : (u : W) ∈ S.toSubmodule := by
      simp only [S, Submodule.mem_iInf, Submodule.mem_comap]
      exact fun g => hs g u hu
    rw [h] at h1
    exact hu0 (Subtype.ext h1)
  · rw [eq_top_iff]
    intro u _
    have h1 : (u : W) ∈ S.toSubmodule := by rw [h]; trivial
    simp only [S, Submodule.mem_iInf, Submodule.mem_comap] at h1
    simpa [he] using h1 1

end Hecke

theorem main : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Subgroup G),
    IsOpen (K : Set G) → IsCompact (K : Set G) → ∀ (θ : G → G), (∀ x y : G, θ (x * y) = θ y * θ x) →
    (∀ x : G, θ (θ x) = x) → (∀ g : G, ∃ a ∈ K, ∃ b ∈ K, θ g = a * g * b) →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W), ρ.IsIrreducible → IsAdmissible ρ →
      ∀ x ∈ fixed ρ K, x ≠ (0 : W) → fixed ρ K = ℂ ∙ x := by
  intro G _ _ _ K hKo hKc θ hmul hinv hdc W _ _ ρ hρ hadm x hx hx0
  let τ : Representation ℂ K W := ρ.comp K.subtype
  have hU : fixed ρ K = τ.invariants := by
    ext v
    show (∀ k : K, ρ k v = ((1 : K →* ℂˣ) k : ℂ) • v) ↔ ∀ k : K, ρ k v = v
    simp
  haveI : FiniteDimensional ℂ τ.invariants := hU ▸ hadm.2 K hKo hKc
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hKc
  have hτ : ∀ v, ∃ N : Subgroup K, N.Normal ∧ N.FiniteIndex ∧ ∀ n ∈ N, ρ (n : K) v = v := by
    intro v
    let T : Subgroup K :=
      { carrier := {k | τ k v = v}
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
          rw [hb, ha]
        one_mem' := by simp
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at *
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]; simp }
    have hT : IsOpen (T : Set K) := (hadm.1 v).preimage continuous_subtype_val
    haveI := T.quotient_finite_of_isOpen hT
    haveI : T.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    exact ⟨T.normalCore, inferInstance, inferInstance, fun n hn => T.normalCore_le hn⟩
  obtain ⟨e, he1, he2, he3⟩ := exists_projector τ hτ
  have hcomm := hecke_comm K θ hmul hinv hdc ρ hτ (τ.invariants.subtype ∘ₗ e)
    (fun k v => congrArg Subtype.val (he2 k v)) he3
  rw [hU] at hx ⊢
  let x' : τ.invariants := ⟨x, hx⟩
  have hx' : x' ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  haveI : Nontrivial τ.invariants := ⟨x', 0, hx'⟩
  have hscal : ∀ g : G, ∃ c : ℂ, ∀ u : τ.invariants, e (ρ g u) = c • u := by
    intro g
    let T : Module.End ℂ τ.invariants := e ∘ₗ ρ g ∘ₗ τ.invariants.subtype
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue T
    have := eq_top_of_stable ρ hρ e he1 (T.eigenspace c) hc (by
      intro h u hu
      rw [Module.End.mem_eigenspace_iff] at hu ⊢
      have h1 : e (ρ g (e (ρ h u))) = e (ρ h (e (ρ g u))) := Subtype.ext (hcomm u u.2 g h)
      have h2 : e (ρ g u) = c • u := hu
      show e (ρ g (e (ρ h u))) = _
      rw [h1, h2]
      simp)
    exact ⟨c, fun u => Module.End.mem_eigenspace_iff.1 (this.ge Submodule.mem_top : u ∈ T.eigenspace c)⟩
  have htop := eq_top_of_stable ρ hρ e he1 (ℂ ∙ x') (by simpa using hx') (by
    intro g u hu
    obtain ⟨c, hc⟩ := hscal g
    rw [hc]
    exact Submodule.smul_mem _ _ hu)
  refine le_antisymm (fun u hu => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hx)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 (htop.ge Submodule.mem_top : (⟨u, hu⟩ : τ.invariants) ∈ ℂ ∙ x')
  exact Submodule.mem_span_singleton.2 ⟨c, congrArg Subtype.val hc⟩

end GlobalTheory.GroupAverageProjection

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqTopOfStable =====

-- ===== clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandPairSphericalVectorUnique =====
-- clump-header: {"m": "Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandPairSphericalVectorUnique", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetOperatorsCommOfAntiInvolution\npublic import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable\npublic import Mathlib.Basic.Complex.Basic\npublic import Mathlib.RepresentationTheory.Irreducible\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqTopOfStable\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\nimport Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift\nimport Development.AbelianVarietyTheory.Definitions.Foundations.InnerEqZeroOfNotUEquiv\nimport Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes\n\n"}
section -- clump:auto
@[expose] public section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Filter GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.AutMult
open GlobalTheory.PRep (IsAdmissible fixed)

noncomputable section

namespace GlobalTheory.GelfandLine

variable {G : Type} [Group G]

theorem mem_fixed_iff {V : Type} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {K : Subgroup G} {v : V} : v ∈ fixed ρ K ↔ ∀ k ∈ K, ρ k v = v :=
  ⟨fun h k hk => by simpa using h ⟨k, hk⟩, fun h k => by simpa using h k k.2⟩

variable {V : Type} [AddCommGroup V] [Module ℂ V]

end GlobalTheory.GelfandLine

end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandPairSphericalVectorUnique =====
