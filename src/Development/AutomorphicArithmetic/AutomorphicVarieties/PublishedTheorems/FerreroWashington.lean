module

public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.RingTheory.ClassGroup.Basic

@[expose] public section

open NumberField

namespace UpperTheory.V.Published

/-- **Ferrero–Washington**, in the form used here: for a prime `l` and an abelian number field `K`
containing a primitive `l`-th root of unity (a primitive fourth root when `l = 2`), the `l`-ranks of
the class groups of the fields `K(μ_{l^n})` are bounded independently of `n`: there is `r` with
`#(Cl / Cl^l) ≤ l ^ r` for all of them. -/
def FerreroWashington : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [NumberField K] [IsAbelianGalois ℚ K],
    (∃ ζ : K, IsPrimitiveRoot ζ (if l = 2 then 4 else l)) →
    ∃ r : ℕ, ∀ (n : ℕ) (K' : Type) [Field K'] [NumberField K'] [Algebra K K'] [IsCyclotomicExtension {l ^ n} K K'],
      Nat.card (ClassGroup (𝓞 K') ⧸ (powMonoidHom l : ClassGroup (𝓞 K') →* ClassGroup (𝓞 K')).range) ≤ l ^ r

end UpperTheory.V.Published
