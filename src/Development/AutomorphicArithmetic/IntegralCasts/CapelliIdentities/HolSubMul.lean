module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivity

@[expose] public section

namespace UpperTheory.Reformulated.B.Qe28

@[reducible] noncomputable def FDSec : {E : Type} →
  [inst : Field E] →
    [inst_1 : NumberField E] →
      [inst_2 : NumberField.IsCMField E] →
        {r : ℕ} → {Comp : Type} → (Comp → ReciprocityTheory.ChartRestriction.G.FD.Data E r) → Type :=
  fun {E} [Field E] [NumberField E] [NumberField.IsCMField E] {r} {Comp} X =>
    (c : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Frame (X c).Ψ r → ℂ

noncomputable def IsHolCusp : {E : Type} →
  [inst : Field E] →
    [inst_1 : NumberField E] →
      [inst_2 : NumberField.IsCMField E] →
        {r : ℕ} →
          {Comp : Type} →
            (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data E r) →
              ((c : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r) →
                FDSec X → Prop :=
  fun {E} [Field E] [NumberField E] [NumberField.IsCMField E] {_} {Comp} X la P => ∀ (c : Comp), P c ∈ (X c).SS (la c)

noncomputable def holSub : {E : Type} →
  [inst : Field E] →
    [inst_1 : NumberField E] →
      [inst_2 : NumberField.IsCMField E] →
        {r : ℕ} →
          {Comp : Type} →
            (X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data E r) →
              ((c : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r) →
                Submodule ℂ (FDSec X) :=
  fun {E} [Field E] [NumberField E] [NumberField.IsCMField E] {_} {_} X la =>
    Submodule.span ℂ {P | IsHolCusp X la P}

theorem holSub_mul : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E]
  [inst_2 : NumberField.IsCMField E] {r : ℕ},
  ReciprocityTheory.ChartRestriction.G.FD.SiegelSpaceAlgebra (E := E) →
    ∀ {Comp : Type} {X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data E r}
      {la la' : (k : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r}
      {P Q : FDSec X},
      P ∈ holSub X la →
        Q ∈ holSub X la' →
          P * Q ∈ holSub X (la + la') := by
  intro E _ _ _ r h5 Comp X la la' P Q hP hQ
  have key : ∀ (l : (k : Comp) → ReciprocityTheory.ChartRestriction.G.FD.Wt (X k).Ψ r) (R : FDSec X),
      R ∈ holSub X l → IsHolCusp X l R := by
    intro l R hR
    induction hR using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => exact fun c => (h5 r (X c) (l c) (l c) 0).1.1
    | add x y _ _ hx hy => exact fun c => (h5 r (X c) (l c) (l c) 0).1.2.1 _ (hx c) _ (hy c)
    | smul a x _ hx => exact fun c => (h5 r (X c) (l c) (l c) 0).1.2.2 a _ (hx c)
  exact Submodule.subset_span fun c =>
    (h5 r (X c) (la c) (la' c) 0).2.1 _ (key la P hP c) _ (key la' Q hQ c).1

end UpperTheory.Reformulated.B.Qe28
