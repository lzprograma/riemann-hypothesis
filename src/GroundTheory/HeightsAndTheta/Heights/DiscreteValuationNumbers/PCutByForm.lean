module

public import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsCN
import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.Tactic.TypeStar

@[expose] public section

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

universe u

theorem weightedHomogeneousComponent_mem_span_of_isMultiHomog {R : Type*} [CommRing R] {K : Type*}
    [DecidableEq K] {ι : K → Type*} {s : MRing ι R} {c : K → ℕ} (hs : IsMultiHomog s c)
    {t : MRing ι R} (ht : t ∈ Ideal.span {s}) (b : K → ℕ) :
    weightedHomogeneousComponent (blockWeight ι) b t ∈ Ideal.span {s} := by
  classical
  let := MvPolynomial.weightedGradedAlgebra R (blockWeight ι)
  have h : (Ideal.span {s}).IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) :=
    Ideal.homogeneous_span _ _ (by rintro _ rfl; exact ⟨c, hs⟩)
  exact MvPolynomial.weightedHomogeneousComponent_mem_of_mem R (blockWeight ι) h ht b

theorem isMultiHomogIdeal_sup_span_of_form {R : Type*} [CommRing R] {K : Type*} [DecidableEq K]
    {ι : K → Type*} {I : Ideal (MRing ι R)} (hI : IsMultiHomogIdeal I) {s : MRing ι R}
    {c : K → ℕ} (hs : IsMultiHomog s c) : IsMultiHomogIdeal (I ⊔ Ideal.span {s}) := by
  intro f hf b
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add (f := _)]
  exact Ideal.add_mem _ (Ideal.mem_sup_left (hI y hy b))
    (Ideal.mem_sup_right (weightedHomogeneousComponent_mem_span_of_isMultiHomog hs hz b))

theorem withBot_lt_of_add_one_lt {d : WithBot ℕ∞} {N : ℕ}
    (h : d + 1 < ((N + 1 : ℕ) : WithBot ℕ∞)) : d < ((N : ℕ) : WithBot ℕ∞) := by
  rw [Nat.cast_add, Nat.cast_one] at h
  exact lt_of_add_lt_add_right h

theorem CutByForm.proof (h1 : IntNumAssoc.Statement.{u}) (h2 : HilbFnCut.Statement.{u})
    (h3 : MixedDiffLinear.Statement) : CutByForm.Statement.{u} := by
  intro F _ K _ _ ι _ n G hGp hG hdim s c hs hsG bs
  have : G.IsPrime := hGp
  set J : Ideal (MRing ι F) := G ⊔ Ideal.span {s} with hJdef
  set c' : K → ℤ := fun k => (c k : ℤ) with hc'

  have hnzd : ∀ y, s * y ∈ G → y ∈ G := fun y hy => (hGp.mem_or_mem hy).resolve_left hsG
  have hH : hilbFn J = diffStep c' (hilbFn G) := by
    funext m
    exact h2 F K ι G s c hG hs hnzd m

  have hnum : intNum F G (Matrix.vecCons c' bs) = intNum F J bs := by
    obtain ⟨-, -, -, h4, h5⟩ := h3 K n bs (hilbFn G) (hilbFn G) 0 0 c'
    unfold intNum
    rw [h5, ← h4, hH]

  have hJ : IsMultiHomogIdeal J := isMultiHomogIdeal_sup_span_of_form hG hs

  have hle : G ≤ J := le_sup_left
  have hr : Ideal.Quotient.mk G s ∈ nonZeroDivisors (MRing ι F ⧸ G) :=
    mem_nonZeroDivisors_of_ne_zero fun h => hsG (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hsucc : ringKrullDim (MRing ι F ⧸ J) + 1 ≤ ringKrullDim (MRing ι F ⧸ G) :=
    ringKrullDim_succ_le_of_surjective (Ideal.Quotient.factor hle)
      (Ideal.Quotient.factor_surjective hle) hr (by
        rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem]
        exact Ideal.mem_sup_right (Ideal.subset_span rfl))
  have hdimJ : ringKrullDim (MRing ι F ⧸ J) <
      ((n + 1 + Fintype.card K : ℕ) : WithBot ℕ∞) := by
    apply withBot_lt_of_add_one_lt
    have he : n + 1 + Fintype.card K + 1 = n + 2 + Fintype.card K := by omega
    rw [he]
    exact lt_of_le_of_lt hsucc hdim

  rw [hnum, h1 F K ι n J hJ hdimJ bs, divCycle_eq_idealCycle]

end

end GroundTheory.Heights₂.Heights.NumbersDVR
