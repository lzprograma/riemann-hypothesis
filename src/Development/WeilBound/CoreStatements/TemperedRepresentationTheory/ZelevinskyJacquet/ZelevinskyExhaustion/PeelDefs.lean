module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

@[expose] public section

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult

namespace Zc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in
def PeelGoodP : Prop :=
  ∀ (x : IrrGL (k := k)) (y : Fin 2 → IrrGL (k := k)) (hd : ∑ a, (y a).1 = x.1) (Δ : Segment k) (𝔫 : Multiset (Segment k)),
    IsLSeg Δ (y 0).rep → IsL 𝔫 (y 1).rep → (∃ f : x.rep.IntertwiningMap (prodIrr y hd), Function.Injective f) →
    (∀ Δ' ∈ 𝔫, ¬ Δ'.Precedes Δ) → IsL (𝔫 + {Δ}) x.rep

end Zc

end
