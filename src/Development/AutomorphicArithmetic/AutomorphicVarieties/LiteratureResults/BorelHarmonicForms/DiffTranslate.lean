module

import all Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ExpGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ExpGenC
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
import Mathlib.Tactic.Linter.Style
import Std.Tactic.BVDecide.Normalize.Prop
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ExpGenPi, Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.HolIdExp, Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DiffTranslate

-- ===== clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ExpGenPi =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ExpGenPi", "h": "module\n\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.WignerHighestWeights.ExpGenC\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.MatrixExponential\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.ENatToNat\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem gen_prod {ι : Type} [Fintype ι] {a : ℕ} (H : Submonoid (Matrix (Fin a) (Fin a) (ι → ℂ)))
    (hH : ∀ X, NormedSpace.exp X ∈ H) (y : Matrix (Fin a) (Fin a) (ι → ℂ)) (hy : IsUnit y) : y ∈ H := by
  apply _root_.gen_pi <;> assumption

theorem UpperTheory.V.Lit.Bor.expGenPi :
    UpperTheory.V.Lit.Bor.ExpGenPi := by
  intro T _ a H hH y
  have h : y.val ∈ H.map (Units.coeHom _) := by
    refine gen_prod (ι := T) (H.map (Units.coeHom _)) ?_ y.val y.isUnit
    intro X
    obtain ⟨u, hu⟩ := Matrix.isUnit_exp X
    exact ⟨u, hH X u hu, hu⟩
  obtain ⟨u, hu, h'⟩ := h
  have : u = y := Units.ext h'
  exact this ▸ hu
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ExpGenPi =====

-- ===== clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.HolIdExp =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.HolIdExp", "h": "module\n\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.MatrixExponential\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.RingTheory.PicardGroup\n\n"}
section -- clump:auto
@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem emb_split {E : Type} [Field E] [_root_.NumberField.IsTotallyComplex E] (z : (E →+* ℂ) → ℂ) :
    ∃ u v : Cinf E, z = emb E u + Complex.I • emb E v := by
  refine ⟨fun w => (z w.embedding + starRingEnd ℂ (z (ComplexEmbedding.conjugate w.embedding))) / 2,
    fun w => -Complex.I * (z w.embedding - starRingEnd ℂ (z (ComplexEmbedding.conjugate w.embedding))) / 2, ?_⟩
  funext τ
  change z τ = coord τ _ + Complex.I * coord τ _
  have key : ∃ w : InfinitePlace E, τ = w.embedding ∨ τ = ComplexEmbedding.conjugate w.embedding := by
    refine ⟨InfinitePlace.mk τ, ?_⟩
    have h' : InfinitePlace.mk (InfinitePlace.mk τ).embedding = InfinitePlace.mk τ := InfinitePlace.mk_embedding _
    exact (InfinitePlace.mk_eq_iff.1 h').imp Eq.symm Eq.symm
  obtain ⟨w, rfl | rfl⟩ := key
  · rw [UpperTheory.V.FieldIso.coord_embedding, UpperTheory.V.FieldIso.coord_embedding]
    linear_combination ((z w.embedding - starRingEnd ℂ (z (ComplexEmbedding.conjugate w.embedding))) / 2) * Complex.I_mul_I
  · rw [UpperTheory.V.FieldIso.coord_conj, UpperTheory.V.FieldIso.coord_conj, UpperTheory.V.FieldIso.coord_embedding,
      UpperTheory.V.FieldIso.coord_embedding]
    simp only [map_div₀, map_add (f := _), map_sub, map_mul, map_neg, Complex.conj_I, Complex.conj_conj, map_ofNat]
    linear_combination (-(starRingEnd ℂ (z w.embedding) - z (ComplexEmbedding.conjugate w.embedding)) / 2) * Complex.I_mul_I

private theorem emb_cont {E : Type} [Field E] : Continuous (emb E) := by
  refine continuous_pi fun τ => ?_
  change Continuous (coord τ)
  unfold coord
  split_ifs
  · exact continuous_apply _
  · exact Complex.continuous_conj.comp (continuous_apply _)

open scoped Matrix.Norms.Operator in
private theorem exp_map_emb {E : Type} [Field E] [NumberField E] {a : ℕ} (Y : Matrix (Fin a) (Fin a) (Cinf E)) :
    (NormedSpace.exp Y).map (emb E) = NormedSpace.exp (Y.map (emb E)) :=
  NormedSpace.map_exp (RingHom.mapMatrix (m := Fin a) (emb E)) (continuous_id.matrix_map emb_cont) Y

open scoped Matrix.Norms.Operator in
private theorem exp_diff {T : Type} [Fintype T] {a : ℕ} (P Q : Matrix (Fin a) (Fin a) (T → ℂ)) :
    Differentiable ℂ fun s : ℂ => (fun i j => NormedSpace.exp (P + s • Q) i j : Fin a → Fin a → T → ℂ) := by
  have h : Differentiable ℂ fun s : ℂ => NormedSpace.exp (P + s • Q) := fun s =>
    (NormedSpace.exp_analytic (𝕂 := ℂ) (P + s • Q)).differentiableAt.comp s
      (f := fun s : ℂ => P + s • Q) ((differentiableAt_const P).add (differentiableAt_id.smul_const Q))
  refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
  let l : Matrix (Fin a) (Fin a) (T → ℂ) →ₗ[ℂ] (T → ℂ) := Matrix.entryLinearMap ℂ (T → ℂ) i j
  exact (LinearMap.toContinuousLinearMap l).differentiable.comp h

theorem UpperTheory.V.Lit.Bor.holIdExp :
    UpperTheory.V.Lit.Bor.HolIdExp := by
  intro E _ _ _ a Φ hΦ h0 X
  choose A B hAB using fun i j => emb_split (X i j)
  let P := (Matrix.of A).map (emb E)
  let Q := (Matrix.of B).map (emb E)
  have hX : X = P + Complex.I • Q := by
    exact Matrix.ext fun i j => hAB i j
  have hd : Differentiable ℂ fun s : ℂ => Φ fun i j => NormedSpace.exp (P + s • Q) i j :=
    differentiableOn_univ.1 (hΦ.comp (exp_diff P Q).differentiableOn fun s _ => Matrix.isUnit_exp (P + s • Q))
  have hr : ∀ t : ℝ, (Φ fun i j => NormedSpace.exp (P + (t : ℂ) • Q) i j) = 0 := fun t => by
    have e : P + (t : ℂ) • Q = (Matrix.of A + t • Matrix.of B).map (emb E) := by
      ext i j τ
      change coord τ (A i j) + (t : ℂ) * coord τ (B i j) = coord τ (A i j + t • B i j)
      rw [map_add (f := _), UpperTheory.V.FieldIso.coord_smul, Complex.real_smul]
    rw [e, ← exp_map_emb]
    exact h0 (Matrix.isUnit_exp (Matrix.of A + t • Matrix.of B)).unit
  have hf : ∃ᶠ s in nhdsWithin (0 : ℂ) {0}ᶜ, (Φ fun i j => NormedSpace.exp (P + s • Q) i j) = (fun _ => 0) s := by
    have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ)) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · simpa using (Complex.continuous_ofReal.tendsto 0).mono_left nhdsWithin_le_nhds
      · exact eventually_nhdsWithin_of_forall fun t ht => by simpa using ht
    exact ht.frequently (Filter.Frequently.of_forall hr)
  have := AnalyticOnNhd.eq_of_frequently_eq (fun s _ => hd.analyticAt s) analyticOnNhd_const hf
  rw [hX]
  exact congrFun this Complex.I
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.HolIdExp =====

-- ===== clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DiffTranslate =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DiffTranslate", "h": "module\n\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ExpGenPi\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.HolIdExp\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\n\n"}
section -- clump:auto
@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private theorem diff_translate {T : Type} [Fintype T] {a : ℕ} (Φ : (Fin a → Fin a → T → ℂ) → ℂ)
    (hΦ : DifferentiableOn ℂ Φ {x | IsUnit (Matrix.of x)}) (A B : GL (Fin a) (T → ℂ)) :
    DifferentiableOn ℂ (fun x : Fin a → Fin a → T → ℂ => Φ (fun i j => (A.val * Matrix.of x * B.val) i j))
      {x | IsUnit (Matrix.of x)} := by
  have hd : Differentiable ℂ
      (fun x : Fin a → Fin a → T → ℂ => (fun i j => (A.val * Matrix.of x * B.val) i j : Fin a → Fin a → T → ℂ)) := by
    refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => differentiable_pi.2 fun t => ?_
    simp only [Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Matrix.of_apply]
    fun_prop
  refine hΦ.comp hd.differentiableOn fun x hx => ?_
  exact (A.isUnit.mul hx).mul B.isUnit

theorem UpperTheory.V.Lit.Bor.holId :
    UpperTheory.V.Lit.Bor.HolId := by
  intro E _ _ _ a
  have hv : ∀ y : GL (Fin a) (Cinf E),
      (GeneralLinearGroup.map (emb E) y).val = Matrix.of (fun i j => emb E (y.val i j)) := fun y => rfl
  let S : Submonoid (GL (Fin a) ((E →+* ℂ) → ℂ)) :=
    { carrier := {g | ∀ Φ : (Fin a → Fin a → (E →+* ℂ) → ℂ) → ℂ,
        DifferentiableOn ℂ Φ {x | IsUnit (Matrix.of x)} →
        (∀ y : GL (Fin a) (Cinf E), Φ (fun i j => emb E (y.val i j)) = 0) → Φ (fun i j => g.val i j) = 0}
      one_mem' := fun Φ _ h0 => by
        have h := h0 1
        have e : (fun i j => emb E ((1 : GL (Fin a) (Cinf E)).val i j)) =
            fun i j => (1 : GL (Fin a) ((E →+* ℂ) → ℂ)).val i j := by
          have := hv 1
          rw [map_one] at this
          exact this.symm
        rwa [e] at h
      mul_mem' := fun {g h} hg hh Φ hΦ h0 => by
        have h1 : ∀ y : GL (Fin a) (Cinf E),
            Φ (fun i j => ((GeneralLinearGroup.map (emb E) y).val * h.val) i j) = 0 := fun y => by
          have := hh _ (diff_translate Φ hΦ (GeneralLinearGroup.map (emb E) y) 1) fun z => by
            have h2 := h0 (y * z)
            have h3 := hv (y * z)
            rw [map_mul, Units.val_mul, hv z] at h3
            simp only [Units.val_one, mul_one, h3]
            exact h2
          simp only [Units.val_one, mul_one] at this
          exact this
        have := hg _ (diff_translate Φ hΦ 1 h) fun z => by
          simp only [Units.val_one, one_mul]
          exact h1 z
        simp only [Units.val_one, one_mul] at this
        exact this }
  intro Φ hΦ h0 g
  refine expGenPi _ a S (fun X y hy Ψ hΨ h1 => ?_) g Φ hΦ h0
  rw [hy]
  exact holIdExp E a Ψ hΨ h1 X
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DiffTranslate =====
