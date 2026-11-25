module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock

@[expose] public section

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

section Lattices
variable {k : Type} [Field k] [ValuativeRel k] {a b : Type} [Fintype a]

def Maps (Λ' : Submodule 𝒪[k] (a → k)) (Λ : Submodule 𝒪[k] (b → k)) (x : Matrix b a k) : Prop :=
  ∀ v ∈ Λ', x *ᵥ v ∈ Λ

def srcLat (a : Type) (ϖ : kˣ) : Submodule 𝒪[k] (a ⊕ Fin (0 + 1) → k) :=
  (box a (1 : kˣ)).comap (LinearMap.funLeft 𝒪[k] k Sum.inl) ⊓
    (box (Fin (0 + 1)) ϖ).comap (LinearMap.funLeft 𝒪[k] k Sum.inr)

end Lattices

section Line
variable {k : Type} [Field k] {n n' : Type}

variable [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n]

def omCol (μz : kˣ →* ℂˣ) (h : GL n k) (φ : (n → k) → ℂ) : (n → k) → ℂ := fun y =>
  (((μz (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) *
    ((nabs k (Matrix.GeneralLinearGroup.det h) ^ (-(1 : ℝ) / 2) : ℝ) : ℂ) * φ ((h⁻¹).val *ᵥ y)

def omRow (μz : kˣ →* ℂˣ) (h : GL n k) (φ' : (n → k) → ℂ) : (n → k) → ℂ := fun η =>
  (((μz (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ) *
    ((nabs k (Matrix.GeneralLinearGroup.det h) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) * φ' (η ᵥ* h.val)

end Line

end GlobalTheory.IndefiniteRowSideFullHecke.OmegaColumnSlices
