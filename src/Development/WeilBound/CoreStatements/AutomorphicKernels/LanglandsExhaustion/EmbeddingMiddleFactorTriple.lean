module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProducts
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquiv
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.MidDefs
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskySegmentClassExistsForEveryPlacing
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.CuspEmbP
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import GroundTheory.LocalFields.PadicLogSeries
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
public import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.EmbeddingMiddleFactorTriple

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.MidGen, Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.EmbeddingMiddleFactorTriple

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.MidGen =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.MidGen", "h": "module\n\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProducts\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar\npublic import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents\npublic import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskySegmentClassExistsForEveryPlacing\nimport Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible\nimport GroundTheory.LocalFields.PadicLogSeries\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult
open GlobalTheory.LocGL.ProjLine (quot quotMk)
open GlobalTheory.SegmentClass (rangeEquiv subIncl subIncl_injective)

namespace PositivityTheory.Exh

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section General

variable {m N : ℕ}
  (T : ∀ {V : Type} [AddCommGroup V] [Module ℂ V], Representation ℂ (GL (Fin m) k) V → GlobalTheory.ProdFlatten.BR k N)
  (Tm : ∀ {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] {τ : Representation ℂ (GL (Fin m) k) V}
    {τ' : Representation ℂ (GL (Fin m) k) W}, τ.IntertwiningMap τ' → (T τ).ρ.IntertwiningMap (T τ').ρ)
  (hT : ∀ {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]
    {τ₁ : Representation ℂ (GL (Fin m) k) V} {τ₂ : Representation ℂ (GL (Fin m) k) W} {τ₃ : Representation ℂ (GL (Fin m) k) U}
    (f : τ₁.IntertwiningMap τ₂) (g : τ₂.IntertwiningMap τ₃), Function.Injective f → Function.Exact f g →
      Function.Injective (Tm f) ∧ Function.Exact (Tm f) (Tm g))

def codSub {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ) (S : Subrepresentation σ)
    (h : ∀ v, f v ∈ S.toSubmodule) : ρ.IntertwiningMap S.toRepresentation :=
  ⟨f.toLinearMap.codRestrict S.toSubmodule h, fun g => LinearMap.ext fun v => Subtype.ext (by
    change f (ρ g v) = σ g (f v)
    rw [f.isIntertwining])⟩

theorem codSub_injective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ) (S : Subrepresentation σ)
    (h : ∀ v, f v ∈ S.toSubmodule) (hf : Function.Injective f) : Function.Injective (codSub f S h) :=
  fun a b hab => hf (congrArg Subtype.val hab)

end General

end PositivityTheory.Exh

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.MidGen =====

-- ===== clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.EmbeddingMiddleFactorTriple =====
-- clump-header: {"m": "Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.EmbeddingMiddleFactorTriple", "h": "module\n\npublic import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.CuspEmbP\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionInStagesProductOfProducts\npublic import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL\npublic import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.SegmentCuspLines.ProdIrrFiniteLength\npublic import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyEquivContraOfChar\npublic import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne\npublic import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleFiniteLength\npublic import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.EmbeddingMiddleFactorTriple\npublic import Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.MidGen\npublic import CompanionTheory.AutomorphicTheory.ProductFormulaTheory.CuspidalExhaustion.MidDefs\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.ProdFlatten
open GlobalTheory.LocGL.ProjLine (quot quotMk)

namespace PositivityTheory.Exh
open CompanionTheory.Exh (EmbL MidP RefineP SwapP T3 stage3_iso sum_get_eq' tripleProductMap tripleProductMap_injective)

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Emb {n : ℕ} (A C : BR k n) : Prop := ∃ f : A.ρ.IntertwiningMap C.ρ, Function.Injective f

def Sq {n : ℕ} (A C : BR k n) : Prop := IsSubquotient A.ρ C.ρ

def FL {n : ℕ} (A : BR k n) : Prop := HasFiniteLength A.ρ

theorem emb_trans {n : ℕ} {A C D : BR k n} (h : Emb A C) (h' : Emb C D) : Emb A D :=
  let ⟨f, hf⟩ := h; let ⟨g, hg⟩ := h'; ⟨g.comp f, hg.comp hf⟩

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem emb_of_iso {n : ℕ} {A C : BR k n} (h : Iso A C) : Emb A C :=
  let ⟨e⟩ := h; ⟨e.toIntertwiningMap, e.toLinearEquiv.injective⟩

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem embedding_middle_factor_triple {nA nB m m' N : ℕ} (h2 : m + nB = m') (h1 : nA + m' = N) (A : BR k nA) (B : BR k nB) {M M' : BR k m}
    (h : Emb M M') : Emb (two h1 A (two h2 M B)) (two h1 A (two h2 M' B)) := by
  obtain ⟨f, hf⟩ := h
  refine ⟨tripleProductMap h2 h1 A.ρ B.ρ f, (tripleProductMap_injective h2 h1 A.ρ B.ρ f (quotMk f.range) hf fun y => ?_).1⟩
  show f.range.toSubmodule.mkQ y = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact Iff.rfl

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem mid_br {nA nB m m' : ℕ} (x : IrrGL (k := k)) (h2 : m + nB = m') (h1 : nA + m' = x.1) (A : BR k nA) (B : BR k nB) (M : BR k m)
    (hM : FL M) (hs : Sm M) (h : Emb (one x) (two h1 A (two h2 M B))) :
    ∃ c : IrrCl (GL (Fin m) k), Sq (one ⟨m, c⟩) M ∧ Emb (one x) (two h1 A (two h2 (one ⟨m, c⟩) B)) :=
  let ⟨f, hf⟩ := h
  CompanionTheory.Exh.mid_gen (fun τ => ⟨_, T3 h2 h1 A.ρ B.ρ τ⟩) (fun f => tripleProductMap h2 h1 A.ρ B.ρ f) (fun f g => tripleProductMap_injective h2 h1 A.ρ B.ρ f g) hM hs x.2 f hf

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem emb_pr_iff (x : IrrGL (k := k)) {a : ℕ} (z : Fin a → IrrGL (k := k)) (hd : ∑ i, (z i).1 = x.1) :
    Emb (one x) (pr z hd) ↔ ∃ f : x.rep.IntertwiningMap (prodIrr z hd), Function.Injective f := Iff.rfl

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem sq_pr_iff (x : IrrGL (k := k)) {a : ℕ} (z : Fin a → IrrGL (k := k)) (hd : ∑ i, (z i).1 = x.1) :
    Sq (one x) (pr z hd) ↔ IsSubquotient x.rep (prodIrr z hd) := Iff.rfl

unseal GlobalTheory.ProdFlatten.one GlobalTheory.ProdFlatten.two GlobalTheory.ProdFlatten.mp GlobalTheory.ProdFlatten.pr GlobalTheory.ProdFlatten.Iso GlobalTheory.ProdFlatten.Sm in
theorem fl_pr (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {a N : ℕ} (z : Fin a → IrrGL (k := k)) (hd : ∑ i, (z i).1 = N) : FL (pr z hd) :=
  _root_.GlobalTheory.CompanionTheory.ProdFL.main hA z hd

attribute [irreducible] Emb Sq FL

theorem embL_iff (x : IrrGL (k := k)) (l : List (IrrGL (k := k))) : EmbL x l ↔ ∃ hd, Emb (one x) (pr l.get hd) :=
  exists_congr fun hd => (emb_pr_iff x l.get hd).symm

theorem embL_block {x : IrrGL (k := k)} {A M M' B : List (IrrGL (k := k))} {m : ℕ} (hM : ∑ a, (M.get a).1 = m) (hM' : ∑ a, (M'.get a).1 = m)
    (h : Emb (pr M.get hM) (pr M'.get hM')) (hx : EmbL x (A ++ M ++ B)) : EmbL x (A ++ M' ++ B) := by
  obtain ⟨hd, e⟩ := (embL_iff _ _).1 hx
  have h1 : ∑ a, (A.get a).1 + (m + ∑ a, (B.get a).1) = x.1 := by rw [← hM, ← CompanionTheory.Exh.deg3, hd]
  have hd' : ∑ a, ((A ++ M' ++ B).get a).1 = x.1 := by rw [CompanionTheory.Exh.deg3, hM', h1]
  exact (embL_iff _ _).2 ⟨hd', emb_trans (emb_trans (emb_trans e (emb_of_iso (stage3_iso A M B hd rfl hM rfl rfl h1)))
    (embedding_middle_factor_triple rfl h1 _ _ h)) (emb_of_iso (iso_symm (stage3_iso A M' B hd' rfl hM' rfl rfl h1)))⟩

end PositivityTheory.Exh

end
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.WeilBound.CoreStatements.AutomorphicKernels.LanglandsExhaustion.EmbeddingMiddleFactorTriple =====
