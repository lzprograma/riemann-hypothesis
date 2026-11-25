module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoordGrading
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HhGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSpan
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivLift
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerGen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PresIndep
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PresNew
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.MapPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ObsClass
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.TactVanish
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ObsPres
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PiSpanVariable
import Mathlib.RingTheory.AdicCompletion.Noetherian
import Mathlib.RingTheory.MvPowerSeries.Equiv

-- This file was produced by scripts/clump.py from the modules listed below.
-- Members: Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedGrading, Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTangent, Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedUniv, Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.RelPres, Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LemmaP

-- ===== clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedGrading =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedGrading", "h": "module\n\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoordGrading\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.HhGroup\nimport Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.TactVanish\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private def tc {R ι X : Type} [CommRing R] [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X)
    (t : Multiplicative X →* Rˣ) : Matrix ι ι R →* Matrix ι ι R where
  toFun h := Matrix.of fun a b => (t (Multiplicative.ofAdd (w a - w b)) : R) * h a b
  map_one' := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · simp [Matrix.one_apply_ne hab]
  map_mul' h h' := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    have : w a - w b = (w a - w c) + (w c - w b) := by abel
    rw [this, ofAdd_add, map_mul, Units.val_mul]
    ring

private theorem tc_apply {R ι X : Type} [CommRing R] [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X)
    (t : Multiplicative X →* Rˣ) (h : Matrix ι ι R) (a b : ι) :
    tc w t h a b = (t (Multiplicative.ofAdd (w a - w b)) : R) * h a b := rfl

private theorem tc_fix {R ι X : Type} [CommRing R] [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X)
    (t : Multiplicative X →* Rˣ) (h : Matrix ι ι R) (hh : ∀ a b, w a ≠ w b → h a b = 0) : tc w t h = h := by
  ext a b
  rw [tc_apply]
  by_cases hab : w a = w b
  · simp [hab]
  · simp [hh a b hab]

private theorem map_mul_alg {O R S ι : Type} [CommRing O] [CommRing R] [CommRing S] [Algebra O R] [Algebra O S]
    [Fintype ι] [DecidableEq ι] (f : R →ₐ[O] S) (A B : Matrix ι ι R) : (A * B).map f = A.map f * B.map f :=
  Matrix.map_mul (f := (f : R →+* S))

section

variable {O : Type} [CommRing O] [IsLocalRing O] {ι X : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X]
  {w : ι → X} {Φ : FormData O w} {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {rbar : Γ →* Matrix ι ι (ResidueField O)} {r0 : Γ →* Matrix ι ι O}
  {R : Type} [CommRing R] [Algebra O R] [IsCO O R]

private def tl (w : ι → X) (t : Multiplicative X →* Rˣ) (ht : ∀ j, res O R (t j) = 1) (r : Lift O rbar R) :
    Lift O rbar R where
  hom := (tc w t).comp r.hom
  cont a b N := by
    have := (r.cont a b N).comp
      (fun x => Ideal.Quotient.mk (maximalIdeal R ^ N) (t (Multiplicative.ofAdd (w a - w b)) : R) * x)
    exact this
  red g a b := by
    show res O R ((t (Multiplicative.ofAdd (w a - w b)) : R) * r.hom g a b) = _
    rw [map_mul, ht, one_mul, r.red]

private theorem inH_comap {r : Lift O rbar R} (h : Φ.InH r0 R r) {H : Type} [Group H] [TopologicalSpace H]
    (φ : H →* Γ) (hφ : Continuous φ) : Φ.InH (r0.comp φ) R (r.comap φ hφ) := fun s => by
  have := h (φ s)
  rw [← map_inv] at this
  exact this

variable {F : Frame Γ} {L : ∀ q, Cond O (rbar.comp (F.ψ q))}
  {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B}

private theorem framed_map (hL : ∀ q, Φ.IsLocCond (r0.comp (F.ψ q)) (F.N q) (L q)) {i : B →ₐ[O] R}
    {r : Lift O rbar R} {α : F.T → Matrix ι ι R} (h : IsFramed Φ r0 F L ρ i r α)
    {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') :
    IsFramed Φ r0 F L ρ (f.comp i) (r.map f) (fun v => (α v).map f) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hm := (hh_group O ι X w Φ R).2.2.2.1 R' f
  refine ⟨fun s => ?_, fun q => ?_, fun v => hm _ (h3 v), ?_, fun v s => ?_⟩
  · have := hm _ (h1 s)
    have e : ((r0 s⁻¹).map (algebraMap O R)).map f = (r0 s⁻¹).map (algebraMap O R') := by
      ext a b
      simp
    rw [map_mul_alg, e] at this
    exact this
  · obtain ⟨I, hI⟩ := (hL q).closed R _ (inH_comap h1 (F.ψ q) (F.hψ q))
    have h0 := (hI R (AlgHom.id O R)).1 (h2 q)
    exact (hI R' f).2 fun x hx => by rw [show x = 0 from h0 x hx, map_zero]
  · simp [h4]
  · have := congrArg (fun A : Matrix ι ι R => A.map f) (h5 v s)
    simp only [map_mul_alg] at this
    exact this

private theorem framed_torus (hL : ∀ q, Φ.IsLocCond (r0.comp (F.ψ q)) (F.N q) (L q))
    (h0 : ∀ g a b, w a ≠ w b → r0 g a b = 0) {i i' : B →ₐ[O] R}
    {r : Lift O rbar R} {α : F.T → Matrix ι ι R} (h : IsFramed Φ r0 F L ρ i r α)
    (t : Multiplicative X →* Rˣ) (ht : ∀ j, res O R (t j) = 1)
    (hi : ∀ v s a b, i' ((ρ v).hom s a b) = t (Multiplicative.ofAdd (w a - w b)) * i ((ρ v).hom s a b)) :
    IsFramed Φ r0 F L ρ i' (tl w t ht r) (fun v => tc w t (α v)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hm : ∀ h, Φ.HH h → Φ.HH (tc w t h) := (hh_group O ι X w Φ R).2.2.2.2.2 t
  refine ⟨fun s => ?_, fun q => ?_, fun v => hm _ (h3 v), ?_, fun v s => ?_⟩
  · have := hm _ (h1 s)
    rw [map_mul, tc_fix w t ((r0 s⁻¹).map _) fun a b hab => by simp [h0 _ a b hab]] at this
    exact this
  · exact (hL q).torus R _ _ t (inH_comap h1 (F.ψ q) (F.hψ q)) ht (fun g a b => rfl) (h2 q)
  · simp [h4]
  · have := congrArg (tc w t) (h5 v s)
    simp only [map_mul] at this
    have e : ((ρ v).hom s).map i' = tc w t (((ρ v).hom s).map i) := by
      ext a b
      exact hi v s a b
    rw [e]
    exact this

end

private theorem algHom_ext_on_generators {O X : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O]
    [IsAdicComplete (maximalIdeal O) O] [AddCommGroup X] {B : Type} [CommRing B] [Algebra O B] [IsCO O B]
    (W : WPres O X B) (hz : ∀ s, W.z s ∈ maximalIdeal B) {R' : Type} [CommRing R'] [Algebra O R']
    [IsCO O R'] (f g : B →ₐ[O] R') (h : ∀ s, f (W.z s) = g (W.z s)) : f = g := by
  have hC : ∀ (H : MvPowerSeries W.σ O →ₐ[O] R') (x : O), H (C x) = Algebra.ofId O R' x := fun H x => by
    have := H.commutes x
    rw [MvPowerSeries.algebraMap_apply] at this
    exact this
  have hm : ∀ s, f (W.z s) ∈ maximalIdeal R' := fun s => by
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hz s
  have key : f.comp W.π = g.comp W.π :=
    (co_ev O O R' W.σ (Algebra.ofId O R') (fun s => f (W.z s)) hm).unique ⟨hC _, fun _ => rfl⟩
      ⟨hC _, fun s => (h s).symm⟩
  ext x
  obtain ⟨y, rfl⟩ := W.surj x
  exact DFunLike.congr_fun key y

private theorem const_mem {O X R ι : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R]
    (W : WPres O X R) (w : ι → X) {a b : ι} {c : O} (hc : w a ≠ w b → c = 0) {x : R}
    (hx : x - algebraMap O R c ∈ W.part (w a - w b)) : x ∈ W.part (w a - w b) := by
  have h2 : algebraMap O R c ∈ W.part (w a - w b) := by
    by_cases hab : w a = w b
    · rw [hab, sub_self, Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (SetLike.GradedOne.one_mem : (1 : R) ∈ W.part 0)
    · rw [hc hab, map_zero]
      exact zero_mem _
  simpa using add_mem hx h2

private theorem const_eig {O X R R' ι : Type} [CommRing O] [AddCommGroup X] [CommRing R] [Algebra O R]
    [CommRing R'] [Algebra O R'] (f f' : R →ₐ[O] R') (t : Multiplicative X →* R'ˣ)
    (w : ι → X) {a b : ι} {c : O} (hc : w a ≠ w b → c = 0) {x : R}
    (hx : f' x = t (Multiplicative.ofAdd (w a - w b)) * f x) :
    f' (x - algebraMap O R c) = t (Multiplicative.ofAdd (w a - w b)) * f (x - algebraMap O R c) := by
  rw [map_sub f', map_sub f, AlgHom.commutes, AlgHom.commutes, hx, mul_sub]
  by_cases hab : w a = w b
  · simp [hab]
  · simp [hc hab]

theorem UpperTheory.V.Alg.framed_grading :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q))), (∀ q, ∀ n ∈ F.N q, rbar (F.ψ q n) = 1) → (∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) → (∀ q, L q O (r0.comap (F.ψ q) (F.hψ q))) →
      ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B), (∀ v, Φ.InH (r0.hom.comp (F.φ v)) B (ρ v)) → ∀ (WB : WPres O X B), (∀ s, WB.z s ∈ maximalIdeal B) → (∀ v s a b, (ρ v).hom s a b ∈ WB.part (w a - w b)) →
      ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (i : B →ₐ[O] R) (r : Lift O rbar R) (α : F.T → Matrix ι ι R), IsUnivFramed Φ r0.hom F L ρ i r α →
      ∃ W : WPres O X R, (∀ s, W.z s ∈ maximalIdeal R) ∧ (∀ s, i (WB.z s) ∈ W.part (WB.wt s)) ∧ (∀ s a b, r.hom s a b ∈ W.part (w a - w b)) ∧ ∀ v a b, α v a b ∈ W.part (w a - w b) := by
  intro O _ _ _ _ ι X _ _ _ _ _ w Φ _ Γ _ _ _ rbar r0 _ hn0 F L _ hL _ B _ _ _ ρ _ WB hzB hρ R _ _ _ i r α ⟨hfr, hu⟩
  have h0 := hn0.2.2
  have h1 : ∀ a b, w a ≠ w b → (1 : Matrix ι ι O) a b = 0 := fun a b hab =>
    Matrix.one_apply_ne fun e => hab (by rw [e])
  let e : WB.σ ⊕ (Γ × ι × ι) ⊕ (F.T × ι × ι) → R := Sum.elim (fun s => i (WB.z s))
    (Sum.elim (fun s => r.hom s.1 s.2.1 s.2.2 - algebraMap O R (r0.hom s.1 s.2.1 s.2.2))
      fun s => α s.1 s.2.1 s.2.2 - algebraMap O R ((1 : Matrix ι ι O) s.2.1 s.2.2))
  have hem : ∀ s, e s ∈ maximalIdeal R := by
    rintro (s | ⟨g, a, b⟩ | ⟨v, a, b⟩)
    · show i (WB.z s) ∈ _
      rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
      exact hzB s
    · show r.hom g a b - algebraMap O R (r0.hom g a b) ∈ _
      rw [← res_eq_zero_iff O, map_sub, r.red, AlgHom.commutes, ← r0.red g a b, sub_eq_zero]
      exact (res O O).commutes _
    · show α v a b - algebraMap O R ((1 : Matrix ι ι O) a b) ∈ _
      have k : res O R (α v a b) = (1 : Matrix ι ι (ResidueField O)) a b :=
        congrFun (congrFun (hfr.2.2.1 v).2.2 a) b
      rw [← res_eq_zero_iff O, map_sub, k, AlgHom.commutes, sub_eq_zero, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
  obtain ⟨W, u, hW, he⟩ := coord_grading O X R _ e
    (Sum.elim WB.wt (Sum.elim (fun s => w s.2.1 - w s.2.2) fun s => w s.2.1 - w s.2.2)) hem
    (fun R' _ _ _ f f' h => by
      refine (hu R' _ _ _ (framed_map hL hfr f)).unique ⟨rfl, rfl, fun _ => rfl⟩ ⟨?_, ?_, fun v => ?_⟩
      · exact algHom_ext_on_generators WB hzB _ _ fun s => (h (.inl s)).symm
      · ext g a b
        have : f (r.hom g a b - algebraMap O R _) = f' (r.hom g a b - algebraMap O R _) :=
          h (.inr (.inl (g, a, b)))
        simp only [map_sub, AlgHom.commutes, sub_left_inj] at this
        exact this.symm
      · ext a b
        have : f (α v a b - algebraMap O R _) = f' (α v a b - algebraMap O R _) :=
          h (.inr (.inr (v, a, b)))
        simp only [map_sub, AlgHom.commutes, sub_left_inj] at this
        exact this.symm)
    (fun R' _ _ _ f t ht => by
      obtain ⟨i', hi', -⟩ := tact O X B WB hzB R' (f.comp i) t
      obtain ⟨f', ⟨k1, k2, k3⟩, -⟩ := hu R' _ _ _
        (framed_torus hL h0 (framed_map hL hfr f) t ht fun v s a b => hi' _ _ (hρ v s a b))
      refine ⟨f', ?_⟩
      rintro (s | ⟨g, a, b⟩ | ⟨v, a, b⟩)
      · exact (DFunLike.congr_fun k1 _).trans (hi' _ _ (WB.z_mem s))
      · exact const_eig f f' t w (h0 g a b) (congrArg (fun x => x.hom g a b) k2)
      · exact const_eig f f' t w (h1 a b) (congrFun (congrFun (k3 v) a) b))
  exact ⟨W, fun s => by rw [(hW s).1]; exact hem _, fun s => he (.inl s),
    fun g a b => const_mem W w (h0 g a b) (he (.inr (.inl (g, a, b)))),
    fun v a b => const_mem W w (h1 a b) (he (.inr (.inr (v, a, b))))⟩
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedGrading =====

-- ===== clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTangent =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTangent", "h": "module\n\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSpan\n\n"}
section -- clump:auto
@[expose] public section

open IsLocalRing Matrix TrivSqZeroExt UpperTheory.V.Alg
noncomputable section
namespace UpperTheory.V.Alg.FramedTangent

private abbrev D (O : Type) [CommRing O] [IsLocalRing O] := DualNumber (ResidueField O)

@[simp] private theorem res_dual {O : Type} [CommRing O] [IsLocalRing O] [IsCO O (D O)] (x : D O) : res O (D O) x = x.fst := by
  have := (co_res O).1; obtain ⟨a, ha⟩ := residue_surjective x.fst
  rw [← res_map (fstHom O (ResidueField O) (ResidueField O))]; change res O (ResidueField O) x.fst = x.fst; rw [← ha]; exact (res O _).commutes a

@[simp] private theorem fst_map {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [IsCO O (D O)]
    (f : R →ₐ[O] D O) (y : R) : (f y).fst = res O R y := by rw [← res_dual, res_map]

private theorem abstract {O R B S X : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] [CommRing B] [Algebra O B] [IsCO O B]
    (i : B →ₐ[O] R) (z : S → R) (hz : ∀ s, z s ∈ maximalIdeal R) (wt : S → X) (H : X → Type) [∀ j, AddCommGroup (H j)]
    [∀ j, Module (ResidueField O) (H j)] (l : ∀ j, S → Module.Dual (ResidueField O) (H j)) (ha : ∀ j s x, wt s ≠ j → l j s x = 0)
    (hb : ∀ j x, (∀ s, l j s x = 0) → x = 0) (hc : ∀ j x, ∃ f : R →ₐ[O] D O, (∀ b, (f (i b)).snd = 0) ∧ ∀ s, (f (z s)).snd = l j s x)
    (hd : ∀ f : R →ₐ[O] D O, (∀ b, (f (i b)).snd = 0) → ∀ j, ∃ x, ∀ s, wt s = j → l j s x = (f (z s)).snd)
    (he : ∀ f : R →ₐ[O] D O, (∀ b, (f (i b)).snd = 0) → (∀ s, (f (z s)).snd = 0) → ∀ y, (f y).snd = 0) :
    ∃ (τ : Type) (_ : Fintype τ) (u : τ → S), maximalIdeal R ≤ Ideal.span (Set.range (z ∘ u)) ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 ∧
      (∀ c : τ → O, ∑ t, c t • (z ∘ u) t ∈ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 → ∀ t, c t ∈ maximalIdeal O) ∧
      ∀ j, Nat.card {t // (wt ∘ u) t = j} = Module.finrank (ResidueField O) (H j) := by
  classical
  have := (co_res O).2
  have snd_zero (f : R →ₐ[O] D O) (hf : ∀ b, (f (i b)).snd = 0) (T : Set R) (hT : T ⊆ maximalIdeal R) (h : ∀ s ∈ T, (f s).snd = 0) {y : R}
      (hy : y ∈ Ideal.span T ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2) : (f y).snd = 0 := by
    suffices Ideal.span T ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 ≤ RingHom.ker f from congrArg snd (this hy)
    refine sup_le (sup_le (Ideal.span_le.2 fun s hs => TrivSqZeroExt.ext ((fst_map f s).trans ((res_eq_zero_iff O R s).2 (hT hs))) (h s hs))
      (Ideal.map_le_iff_le_comap.2 fun b hb => TrivSqZeroExt.ext ((fst_map f _).trans ((res_map i b).trans ((res_eq_zero_iff O B b).2 hb))) (hf b))) ?_
    rw [sq, Ideal.mul_le]; intro a ha1 b hb1; rw [← res_eq_zero_iff O] at ha1 hb1; exact TrivSqZeroExt.ext (by simp [ha1]) (by simp [ha1, hb1])
  have span_of (T : Set R) (hT : T ⊆ maximalIdeal R) (H' : ∀ f : R →ₐ[O] D O, (∀ b, (f (i b)).snd = 0) → (∀ s ∈ T, (f s).snd = 0) → ∀ y, (f y).snd = 0) :
      maximalIdeal R ≤ Ideal.span T ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 := co_span O R B i T hT fun f f' h1 h2 => by
    have := H' { toFun := fun y => (res O R y, (f y).snd - (f' y).snd)
                 map_one' := TrivSqZeroExt.ext (map_one _) (by show (f 1).snd - (f' 1).snd = 0; simp)
                 map_mul' := fun y y' => TrivSqZeroExt.ext (map_mul _ y y') (by show (f (y * y')).snd - (f' (y * y')).snd = res O R y * _ + _ * res O R y'; simp; ring)
                 map_zero' := TrivSqZeroExt.ext (map_zero _) (by show (f 0).snd - (f' 0).snd = 0; simp)
                 map_add' := fun y y' => TrivSqZeroExt.ext (map_add _ y y') (by show (f (y + y')).snd - (f' (y + y')).snd = (_ - _) + (_ - _); simp; abel)
                 commutes' := fun a => TrivSqZeroExt.ext ((res O R).commutes a) (by show (f _).snd - (f' _).snd = 0; rw [AlgHom.commutes, AlgHom.commutes, sub_self]) }
      (fun b => sub_eq_zero.2 (congrArg snd (DFunLike.congr_fun h1 b))) (fun s hs => sub_eq_zero.2 (congrArg snd (h2 s hs)))
    ext y; exacts [by simp, sub_eq_zero.1 (this y)]
  obtain ⟨S0, hS0⟩ : ∃ S0 : Finset S, maximalIdeal R ≤ Ideal.span (z '' S0) ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 := by
    obtain ⟨T, hT, hT'⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 (IsNoetherian.noetherian (Ideal.span (Set.range z)))
    rw [← Set.image_univ] at hT; obtain ⟨S0, -, h⟩ := Finset.subset_set_image_iff.1 hT; subst h; refine ⟨S0, ?_⟩; rw [← Finset.coe_image]
    exact (span_of _ (Set.range_subset_iff.2 hz) fun f h h' => he f h fun s => h' _ ⟨s, rfl⟩).trans (by rw [Ideal.span, hT'])
  have db (j : X) : ∃ (κ : Type) (a : κ → {s : S0 // wt s = j}), Function.Injective a ∧ Nat.card κ = Module.finrank (ResidueField O) (H j) ∧
      (∀ x, (∀ t, l j (a t).1 x = 0) → x = 0) ∧ ∀ t, ∃ x, l j (a t).1 x = 1 ∧ ∀ t', t' ≠ t → l j (a t').1 x = 0 := by
    let l' (s : {s : S0 // wt s = j}) := l j s.1
    have hl' (x : H j) (hx : ∀ s, l' s x = 0) : x = 0 := by
      obtain ⟨f, hf, hf'⟩ := hc j x; exact hb j x fun s => (hf' s).symm.trans (snd_zero f hf _ (by rintro _ ⟨s, -, rfl⟩; exact hz s)
        (by rintro _ ⟨s, hs, rfl⟩; rw [hf']; exact if e : wt s = j then hx ⟨⟨s, hs⟩, e⟩ else ha j s x e) (hS0 (hz s)))
    have : FiniteDimensional (ResidueField O) (H j) := .of_injective (LinearMap.pi l') ((injective_iff_map_eq_zero _).2 fun x hx => hl' x (congrFun hx))
    obtain ⟨κ, a, ha', h1, h2⟩ := exists_linearIndependent' (ResidueField O) l'
    have htop : Submodule.span (ResidueField O) (Set.range l') = ⊤ := by
      rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := Submodule.span _ (Set.range l')), show (Submodule.span _ (Set.range l')).dualCoannihilator = ⊥
        from eq_bot_iff.2 fun x hx => by rw [Submodule.mem_dualCoannihilator] at hx; exact hl' x fun s => hx _ (Submodule.subset_span ⟨s, rfl⟩), Submodule.dualAnnihilator_bot]
    let b := Module.Basis.mk h2 (h1.trans htop).ge
    refine ⟨κ, a, ha', (Module.finrank_eq_nat_card_basis b).symm.trans Subspace.dual_finrank_eq, fun x hx => (Module.forall_dual_apply_eq_zero_iff (ResidueField O) x).1
      (DFunLike.congr_fun (b.ext fun t => by rw [Module.Basis.mk_apply]; exact hx t : Module.Dual.eval (ResidueField O) (H j) x = 0)), fun t => ?_⟩
    obtain ⟨x, hx⟩ := (Module.evalEquiv (ResidueField O) (H j)).surjective (b.coord t)
    have hcoord (t') : l' (a t') x = b.coord t (b t') := by rw [← hx, Module.Basis.mk_apply]; rfl
    exact ⟨x, by simp [l', hcoord], fun t' ht' => by simp [l', hcoord, ht']⟩
  choose κ a a1 a2 a3 a4 using db
  have : Finite (Σ j, κ j) := .of_injective (fun t : Σ j, κ j => (a t.1 t.2).1) fun ⟨j, t⟩ ⟨j', t'⟩ e => by
    obtain rfl : j = j' := (a j t).2.symm.trans ((congrArg (wt ∘ Subtype.val) e).trans (a j' t').2); exact congrArg (Sigma.mk j) (a1 j (Subtype.ext e))
  refine ⟨Σ j, κ j, Fintype.ofFinite _, fun t => (a t.1 t.2).1, span_of _ (Set.range_subset_iff.2 fun _ => hz _) fun f h h' => he f h fun s => ?_,
    fun c hcm ⟨j, t⟩ => ?_, fun j => (Nat.card_congr (Equiv.ofBijective (fun t : κ j => ⟨⟨j, t⟩, (a j t).2⟩)
      ⟨fun _ _ e => by simpa using e, fun ⟨⟨j', t⟩, e⟩ => by cases (a j' t).2.symm.trans e; exact ⟨t, rfl⟩⟩)).symm.trans (a2 j)⟩
  · obtain ⟨x, hx⟩ := hd f h (wt s); rw [← hx s rfl, a3 _ x fun t => (hx _ (a _ t).2).trans (h' _ ⟨⟨_, t⟩, rfl⟩), map_zero]
  · obtain ⟨x, x1, x2⟩ := a4 j t; obtain ⟨f, hf, hf'⟩ := hc j x
    have h3 := snd_zero f hf ∅ (Set.empty_subset _) (by simp) (by simpa using hcm)
    rw [map_sum, snd_sum, Finset.sum_eq_single ⟨j, t⟩] at h3
    · rw [map_smul, snd_smul, hf', x1, Algebra.smul_def, mul_one] at h3; exact (residue_eq_zero_iff _).1 h3
    · rintro ⟨j', t'⟩ - e; rw [map_smul, snd_smul, hf']
      exact if e' : j' = j then by subst e'; simp [x2 t' (e ∘ congrArg _)] else by simp [ha j _ x ((a j' t').2.trans_ne e')]
    · simp

private theorem mext {ι k : Type} [CommRing k] {M M' : Matrix ι ι (DualNumber k)} (h1 : M.map fst = M'.map fst) (h2 : M.map snd = M'.map snd) : M = M' :=
  Matrix.ext fun a b => TrivSqZeroExt.ext (congrFun (congrFun h1 a) b) (congrFun (congrFun h2 a) b)

private theorem msnd_mul {ι k : Type} [CommRing k] [Fintype ι] (M M' : Matrix ι ι (DualNumber k)) :
    (M * M').map snd = M.map fst * M'.map snd + M.map snd * M'.map fst := by ext a b; simp [Matrix.mul_apply, snd_sum, Finset.sum_add_distrib, mul_comm]

open Classical in
private def mask {ι X k : Type} [AddCommGroup X] [Zero k] (w : ι → X) (j : X) (Y : Matrix ι ι k) : Matrix ι ι k := of fun a b => if w a - w b = j then Y a b else 0

section
variable {O ι Γ : Type} [CommRing O] [IsLocalRing O] [Fintype ι] [DecidableEq ι] [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* Matrix ι ι (ResidueField O)}
@[simp] private theorem lift_fst [IsCO O (D O)] (r : Lift O rbar (D O)) (s : Γ) : (r.hom s).map fst = rbar s := Matrix.ext fun a b => by rw [← r.red, res_dual]; rfl
variable {X : Type} [AddCommGroup X] {w : ι → X}

private theorem framed_iff [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (Φ : FormData O w) [IsCO O (D O)] (r0 : Lift O rbar O) (F : Frame Γ)
    (L : ∀ q, Cond O (rbar.comp (F.ψ q))) {B : Type} [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B)
    (hL : ∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) (h0 : ∀ q, L q O (r0.comap (F.ψ q) (F.hψ q))) (i : B →ₐ[O] D O) (hi : ∀ b, (i b).snd = 0)
    (r : Lift O rbar (D O)) (α : F.T → Matrix ι ι (D O)) :
    IsFramed Φ r0.hom F L ρ i r α ↔ (∀ s, (r.hom s).map snd * rbar s⁻¹ ∈ Φ.g (ResidueField O)) ∧ (∀ q, ∀ n ∈ F.N q, (r.hom (F.ψ q n)).map snd = 0) ∧
      (∀ v, (α v).map fst = 1 ∧ (α v).map snd ∈ Φ.g (ResidueField O)) ∧ (α F.v0).map snd = 0 ∧
      ∀ v s, rbar (F.φ v s) * (α v).map snd + (r.hom (F.φ v s)).map snd = (α v).map snd * rbar (F.φ v s) := by
  have := (co_res O).1; have mfst1 : (1 : Matrix ι ι (D O)).map fst = 1 := Matrix.map_one fst rfl rfl
  have mfst (A M : Matrix ι ι (D O)) : (A * M).map fst = A.map fst * M.map fst := Matrix.map_mul (f := (fstHom O _ _).toRingHom)
  have msnd1 : (1 : Matrix ι ι (D O)).map snd = 0 := Matrix.ext fun _ _ => by simp [Matrix.one_apply, apply_ite snd]
  have hh (h : Matrix ι ι (D O)) : Φ.HH h ↔ h.map fst = 1 ∧ h.map snd ∈ Φ.g (ResidueField O) := by
    have e1 : (Φ.JR (D O)).map fst = Φ.JR (ResidueField O) := rfl; have e2 : (Φ.JR (D O)).map snd = 0 := rfl
    have e3 (e : h.map fst = 1) : (hᵀ * Φ.JR _ * h).map snd = (h.map snd)ᵀ * Φ.JR _ + Φ.JR _ * h.map snd := by simp [msnd_mul, mfst, transpose_map, e, e1, e2, add_comm]
    rw [FormData.HH, show h.map (res O _) = h.map fst from Matrix.ext fun _ _ => res_dual _]
    exact ⟨fun ⟨a1, a2, a3⟩ => ⟨a3, by rw [← e3 a3, a1, e2], fun a b e => by simp [a2 a b e]⟩,
      fun ⟨a1, a2, a3⟩ => ⟨mext (by simp [mfst, transpose_map, a1, e1]) (by rw [e3 a1, a2, e2]),
        fun a b e => TrivSqZeroExt.ext ((congrFun (congrFun a1 a) b).trans (Matrix.one_apply_ne (e ∘ congrArg _))) (a3 a b e), a1⟩⟩
  have inH {H : Type} [Group H] [TopologicalSpace H] {rb : H →* Matrix ι ι (ResidueField O)} (r0' : Lift O rb O) (r' : Lift O rb (D O)) :
      Φ.InH r0'.hom _ r' ↔ ∀ s, (r'.hom s).map snd * rb s⁻¹ ∈ Φ.g (ResidueField O) := forall_congr' fun s => by
    have e1 : ((r0'.hom s⁻¹).map (algebraMap O (D O))).map fst = rb s⁻¹ := lift_fst (r0'.map (Algebra.ofId O _)) s⁻¹
    simp [hh, mfst, msnd_mul, e1, show ((r0'.hom s⁻¹).map (algebraMap O (D O))).map snd = 0 from rfl, ← map_mul]
  have e1 (v) (s) : (((ρ v).hom s).map i).map fst = rbar (F.φ v s) := lift_fst ((ρ v).map i) s
  have e2 (v) (s) : (((ρ v).hom s).map i).map snd = 0 := Matrix.ext fun _ _ => hi _
  rw [IsFramed, inH r0 r]; refine and_congr_right fun h1 => and_congr (forall_congr' fun q => ?_) ?_
  · let r0q := r0.comap (F.ψ q) (F.hψ q); let r1 := r0q.map (Algebra.ofId O (D O)); have er1 (s) : (r1.hom s).map snd = 0 := rfl
    have h1q : L q _ r1 := by
      obtain ⟨I, hI⟩ := (hL q).closed O r0q fun s => by
        change Φ.HH (r0q.hom s * r0q.hom s⁻¹); rw [← map_mul, mul_inv_cancel, map_one]; exact ⟨by simp, fun _ _ hab => Matrix.one_apply_ne (hab ∘ congrArg _), by simp⟩
      exact (hI _ _).2 fun x hx => by have hx0 : x = 0 := (hI O (.id O O)).1 (h0 q) x hx; simp [hx0]
    rw [(hL q).tangent _ _ (fstHom O (ResidueField O) (ResidueField O)) (fun x => ⟨inl x, rfl⟩) ?_ r1 (r.comap (F.ψ q) (F.hψ q))
      ((inH r0q r1).2 fun s => by simp [er1, zero_mem]) ((inH r0q _).2 fun s => by change (r.hom (F.ψ q s)).map snd * _ ∈ _; simpa [← map_inv] using h1 (F.ψ q s))
      (Lift.ext (MonoidHom.ext fun s => (lift_fst r1 s).trans (lift_fst (r.comap (F.ψ q) (F.hψ q)) s).symm)) h1q]
    · exact forall₂_congr fun n _ => ⟨fun h => (congrArg (map · snd) h).trans (er1 n),
        fun h => mext ((lift_fst (r.comap (F.ψ q) (F.hψ q)) n).trans (lift_fst r1 n).symm) (h.trans (er1 n).symm)⟩
    · rw [eq_bot_iff, Ideal.mul_le]; intro x hx y hy; rw [← res_eq_zero_iff O, res_dual] at hx
      exact Ideal.mem_bot.2 (TrivSqZeroExt.ext (by simp [hx]) (by simp [hx, show y.fst = 0 from hy]))
  · simp only [hh]; refine and_congr_right fun h2 => and_congr ⟨fun h => by rw [h, msnd1], fun h => mext ((h2 _).1.trans mfst1.symm) (h.trans msnd1.symm)⟩
      (forall₂_congr fun v s => ⟨fun h => ?_, fun h => mext (by rw [mfst, mfst, lift_fst, e1, (h2 v).1, mul_one, one_mul]) ?_⟩)
    · simpa only [msnd_mul, lift_fst, (h2 v).1, e1, e2, mul_one, mul_zero, zero_add] using congrArg (map · snd) h
    · simpa only [msnd_mul, lift_fst, (h2 v).1, e1, e2, mul_one, mul_zero, zero_add] using h

private def ell {Φ : FormData O w} (F : Frame Γ) (hbar : Φ.Normalises rbar) (j : X) :
    (Γ × ι × ι) ⊕ (F.T × ι × ι) → Module.Dual (ResidueField O) (F.H1c (FormData.adRep hbar j))
  | .inl (s, a, b) => ⟨⟨fun x => ((x.1.1 s).1 * rbar s) a b, fun _ _ => by simp [add_mul]⟩, fun _ _ => by simp⟩
  | .inr (v, a, b) => ⟨⟨fun x => -(x.1.2 v).1 a b, fun _ _ => by simp [add_comm]⟩, fun _ _ => by simp⟩
end
end UpperTheory.V.Alg.FramedTangent

open UpperTheory.V.Alg.FramedTangent in
theorem UpperTheory.V.Alg.framed_tangent :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q))), (∀ q, ∀ n ∈ F.N q, rbar (F.ψ q n) = 1) → (∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) → (∀ q, L q O (r0.comap (F.ψ q) (F.hψ q))) →
      ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B), (∀ v, Φ.InH (r0.hom.comp (F.φ v)) B (ρ v)) → ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (i : B →ₐ[O] R) (r : Lift O rbar R) (α : F.T → Matrix ι ι R), IsUnivFramed Φ r0.hom F L ρ i r α →
      ∃ (τ : Type) (_ : Fintype τ) (z : τ → R) (wt : τ → X),
        (∀ t, ∃ a b, wt t = w a - w b ∧ ((∃ s, z t = r.hom s a b - algebraMap O R (r0.hom s a b)) ∨ ∃ v, z t = (α v - 1) a b)) ∧
        maximalIdeal R ≤ Ideal.span (Set.range z) ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 ∧
        (∀ c : τ → O, ∑ t, c t • z t ∈ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 → ∀ t, c t ∈ maximalIdeal O) ∧
        ∀ j, Nat.card {t // wt t = j} = Module.finrank (ResidueField O) (F.H1c (FormData.adRep hbar j)) := by
  intro O _ _ _ _ ι X _ _ _ w Φ _ Γ _ _ _ rbar r0 hbar _ F L _ hL h0 B _ _ _ ρ _ R _ _ _ i r α ⟨hF, hU⟩
  classical
  have := (co_res O).1; have := (co_res O).2
  have lift_lc (r' : Lift O rbar (D O)) : IsLocallyConstant r'.hom := (IsLocallyConstant.iff_eventually_eq _).2 fun x =>
    (Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => (IsLocallyConstant.iff_eventually_eq _).1 (IsLocallyConstant.desc _ _ (r'.cont a b 2)
      (by rw [RingHom.injective_iff_ker_eq_bot, Ideal.mk_ker, sq, eq_bot_iff, Ideal.mul_le]; intro u hu v hv; rw [← res_eq_zero_iff O, res_dual] at hu hv
          exact Ideal.mem_bot.2 (TrivSqZeroExt.ext (by simp [hu]) (by simp [hu, hv])))) x).mono fun _ => Matrix.ext
  have hrbar : IsLocallyConstant rbar := funext (lift_fst (r0.map (Algebra.ofId O _))) ▸ (lift_lc (r0.map (Algebra.ofId O _))).comp (map · fst)
  have mask_mul (j : X) (Y A : Matrix ι ι (ResidueField O)) (hA : ∀ a b, w a ≠ w b → A a b = 0) : mask w j (Y * A) = mask w j Y * A := Matrix.ext fun a b => by
    by_cases e : w a - w b = j <;> simp only [mask, Matrix.mul_apply, of_apply, e, ↓reduceIte]
    exacts [Finset.sum_congr rfl fun c _ => if n : w c = w b then by simp [n, e] else by simp [hA c b n], (Finset.sum_eq_zero fun c _ => if n : w c = w b then by simp [n, e] else by simp [hA c b n]).symm]
  have mul_mask (j : X) (Y A : Matrix ι ι (ResidueField O)) (hA : ∀ a b, w a ≠ w b → A a b = 0) : mask w j (A * Y) = A * mask w j Y := Matrix.ext fun a b => by
    by_cases e : w a - w b = j <;> simp only [mask, Matrix.mul_apply, of_apply, e, ↓reduceIte]
    exacts [Finset.sum_congr rfl fun c _ => if n : w a = w c then by simp [← n, e] else by simp [hA a c n], (Finset.sum_eq_zero fun c _ => if n : w a = w c then by simp [← n, e] else by simp [hA a c n]).symm]
  have mask_mem (j : X) {Y : Matrix ι ι (ResidueField O)} (hY : Y ∈ Φ.g (ResidueField O)) : mask w j Y ∈ Φ.gw (ResidueField O) j := by
    refine ⟨⟨Matrix.ext fun a b => ?_, fun a b e => by simp [mask, hY.2 a b e]⟩, fun a b e => by simp [mask, e]⟩
    have hJ (u v : ι) (e : w u + w v ≠ Φ.c) : Φ.JR (ResidueField O) u v = 0 := by simp [FormData.JR, show Φ.J u v = 0 from by_contra fun n => e (Φ.hw u v n)]
    have h := congrFun (congrFun hY.1 a) b; simp only [Matrix.add_apply, Matrix.mul_apply, transpose_apply, Matrix.zero_apply, mask, of_apply] at h ⊢
    by_cases e : Φ.c - w a - w b = j
    · rw [← h]; congr 1 <;> refine Finset.sum_congr rfl fun c _ => ?_
      exacts [if n : w c + w b = Φ.c then by simp [show w c - w a = j by rw [← e, ← n]; abel] else by simp [hJ c b n],
        if n : w a + w c = Φ.c then by simp [show w c - w b = j by rw [← e, ← n]; abel] else by simp [hJ a c n]]
    · rw [Finset.sum_eq_zero fun c _ => if n : w c + w b = Φ.c then by simp [show w c - w a ≠ j from fun m => e (by rw [← m, ← n]; abel)] else by simp [hJ c b n],
        Finset.sum_eq_zero fun c _ => if n : w a + w c = Φ.c then by simp [show w c - w b ≠ j from fun m => e (by rw [← m, ← n]; abel)] else by simp [hJ a c n], add_zero]
  let z : (Γ × ι × ι) ⊕ (F.T × ι × ι) → R := Sum.elim (fun p => r.hom p.1 p.2.1 p.2.2 - algebraMap O R (r0.hom p.1 p.2.1 p.2.2)) fun p => (α p.1 - 1) p.2.1 p.2.2
  let wt : (Γ × ι × ι) ⊕ (F.T × ι × ι) → X := Sum.elim (fun p => w p.2.1 - w p.2.2) fun p => w p.2.1 - w p.2.2
  have z1 (f : R →ₐ[O] D O) (s a b) : (f (z (.inl (s, a, b)))).snd = ((r.map f).hom s).map snd a b := by show (f (_ - _)).snd = _; rw [map_sub, snd_sub, AlgHom.commutes]; exact sub_zero _
  have z2 (f : R →ₐ[O] D O) (v a b) : (f (z (.inr (v, a, b)))).snd = ((α v).map f).map snd a b := by show (f (α v a b - (1 : Matrix ι ι R) a b)).snd = _; by_cases e : a = b <;> simp [Matrix.one_apply, e]
  have hmap (f : R →ₐ[O] D O) : IsFramed Φ r0.hom F L ρ (f.comp i) (r.map f) fun v => (α v).map f := by
    obtain ⟨a1, a2, a3, a4, a5⟩ := hF; have hm (A A' : Matrix ι ι R) : (A * A').map f = A.map f * A'.map f := Matrix.map_mul (f := (f : R →+* D O))
    have map_HH (A : Matrix ι ι R) (hA : Φ.HH A) : Φ.HH (A.map f) :=
      ⟨by rw [show Φ.JR _ = (Φ.JR R).map f from Matrix.ext fun a b => (f.commutes (Φ.J a b)).symm, ← transpose_map, ← hm, ← hm, hA.1],
        fun a b hab => by simp [hA.2.1 a b hab], by rw [← hA.2.2]; exact Matrix.ext fun _ _ => res_map f _⟩
    refine ⟨fun s => ?_, fun q => ?_, fun v => map_HH _ (a3 v), by simp [a4], fun v s => Matrix.ext fun a b =>
      congrFun (congrFun (by simpa only [hm] using congrArg (map · f) (a5 v s) : (r.hom (F.φ v s)).map f * (α v).map f = (α v).map f * (((ρ v).hom s).map i).map f) a) b⟩
    · change Φ.HH ((r.hom s).map f * _); simpa [hm, show ((r0.hom s⁻¹).map (algebraMap O R)).map f = (r0.hom s⁻¹).map (algebraMap O _) from Matrix.ext fun _ _ => f.commutes _] using map_HH _ (a1 s)
    · obtain ⟨I, hI⟩ := (hL q).closed R (r.comap (F.ψ q) (F.hψ q)) fun s => by change Φ.HH (r.hom (F.ψ q s) * _); simpa [← map_inv] using a1 (F.ψ q s)
      exact (hI _ f).2 fun x hx => by have hx0 : x = 0 := (hI R (.id O R)).1 (a2 q) x hx; simp [hx0]
  have inv1 (s) : rbar s⁻¹ * rbar s = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have inv2 (s) : rbar s * rbar s⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  refine Exists.elim (abstract i z ?_ wt (fun j => F.H1c (FormData.adRep hbar j)) (ell F hbar) ?_ ?_ ?_ ?_ ?_) ?_; rotate_right
  · rintro τ ⟨hτ, u, u1, u2, u3⟩; refine ⟨τ, hτ, z ∘ u, wt ∘ u, fun t => ?_, u1, u2, u3⟩
    rcases uxh : u t with ⟨s, a, b⟩ | ⟨v, a, b⟩; exacts [⟨a, b, by simp [wt, uxh], .inl ⟨s, by simp [z, uxh]⟩⟩, ⟨a, b, by simp [wt, uxh], .inr ⟨v, by simp [z, uxh]⟩⟩]
  · rintro (⟨s, a, b⟩ | ⟨v, a, b⟩) <;> rw [← res_eq_zero_iff O]
    · show res O R (_ - _) = 0; rw [map_sub, r.red, ← r0.red, AlgHom.commutes, sub_eq_zero]; exact (res O O).commutes _
    · show res O R (α v a b - (1 : Matrix ι ι R) a b) = 0; rw [map_sub, show res O R (α v a b) = (1 : Matrix ι ι _) a b from congrFun (congrFun (hF.2.2.1 v).2.2 a) b]; by_cases e : a = b <;> simp [Matrix.one_apply, e]
  · rintro j (⟨s, a, b⟩ | ⟨v, a, b⟩) x e
    · change w a - w b ≠ j at e; have hfix : mask w j (x.1.1 s).1 = (x.1.1 s).1 := Matrix.ext fun a' b' => by by_cases h : w a' - w b' = j <;> simp [mask, h, (x.1.1 s).2.2 a' b']
      change ((x.1.1 s).1 * rbar s) a b = 0; rw [← hfix, ← mask_mul j _ _ (hbar.2.2 s)]; simp [mask, e]
    · exact neg_eq_zero.2 ((x.1.2 v).2.2 a b e)
  · intro j x hx; refine Subtype.ext (Prod.ext (funext fun s => Subtype.ext ?_) (funext fun v => Subtype.ext (Matrix.ext fun a b => neg_eq_zero.1 (hx (.inr (v, a, b))))))
    have h0s : (x.1.1 s).1 * rbar s = 0 := Matrix.ext fun a b => hx (.inl (s, a, b)); show (x.1.1 s).1 = 0; rw [← mul_one (x.1.1 s).1, ← inv2 s, ← mul_assoc, h0s, zero_mul]
  · intro j x; let i0 : B →ₐ[O] D O := (inlAlgHom O (ResidueField O) (ResidueField O)).comp (res O B)
    let r1 : Lift O rbar (D O) :=
      ⟨⟨⟨fun s => of fun a b => (rbar s a b, ((x.1.1 s).1 * rbar s) a b), mext ((map_one rbar).trans (Matrix.map_one fst (by simp) (by simp)).symm) (by
          change (x.1.1 1).1 * rbar 1 = (1 : Matrix ι ι _).map snd; rw [show x.1.1 1 = 0 by simpa using x.2.2.1 1 1]; ext; simp [Matrix.one_apply, apply_ite snd])⟩,
        fun s t => mext (by have mfst (A M : Matrix ι ι (D O)) : (A * M).map fst = A.map fst * M.map fst := Matrix.map_mul (f := (fstHom O _ _).toRingHom); rw [mfst]; exact map_mul rbar s t) (by
          have h : (x.1.1 (s * t)).1 = (x.1.1 s).1 + rbar s * (x.1.1 t).1 * rbar s⁻¹ := congrArg Subtype.val (x.2.2.1 s t); rw [msnd_mul]
          change (x.1.1 (s * t)).1 * rbar (s * t) = rbar s * ((x.1.1 t).1 * rbar t) + (x.1.1 s).1 * rbar s * rbar t
          rw [h, add_mul, mul_assoc _ (rbar s⁻¹), ← map_mul, inv_mul_cancel_left, map_mul, add_comm]; simp only [mul_assoc])⟩,
        fun a b N => (x.2.1.prodMk hrbar).comp fun p => Ideal.Quotient.mk (maximalIdeal (D O) ^ N) (p.2 a b, (p.1.1 * p.2) a b), fun _ _ _ => res_dual _⟩
    obtain ⟨f, ⟨f1, f2, f3⟩, -⟩ := hU _ i0 r1 (fun v => of fun a b => ((1 : Matrix ι ι _) a b, (-(x.1.2 v).1) a b)) ((framed_iff Φ r0 F L ρ hL h0 i0 (fun _ => rfl) r1 _).2
      ⟨fun s => by change (x.1.1 s).1 * rbar s * rbar s⁻¹ ∈ _; rw [mul_assoc, inv2, mul_one]; exact (x.1.1 s).2.1,
        fun q n hn => by change (x.1.1 (F.ψ q n)).1 * _ = 0; simp [x.2.2.2.1 q n hn], fun v => ⟨rfl, neg_mem (x.1.2 v).2.1⟩, by change -(x.1.2 F.v0).1 = 0; simp [x.2.2.2.2.2],
        fun v s => by
          have h : (x.1.1 (F.φ v s)).1 = rbar (F.φ v s) * (x.1.2 v).1 * rbar (F.φ v s)⁻¹ - (x.1.2 v).1 := congrArg Subtype.val (x.2.2.2.2.1 v s)
          change rbar (F.φ v s) * -(x.1.2 v).1 + (x.1.1 (F.φ v s)).1 * rbar (F.φ v s) = -(x.1.2 v).1 * rbar (F.φ v s); rw [h, sub_mul, mul_assoc, inv1, mul_one, mul_neg, neg_mul]; abel⟩)
    refine ⟨f, fun b => by rw [show f (i b) = i0 b from DFunLike.congr_fun f1 b]; rfl, ?_⟩
    rintro (⟨s, a, b⟩ | ⟨v, a, b⟩); exacts [by rw [z1, f2]; rfl, by rw [z2, f3]; rfl]
  · intro f hf j; obtain ⟨b1, b2, b3, b4, b5⟩ := (framed_iff Φ r0 F L ρ hL h0 (f.comp i) hf _ _).1 (hmap f)
    have madd (Y Z : Matrix ι ι (ResidueField O)) : mask w j (Y + Z) = mask w j Y + mask w j Z := Matrix.ext fun a b => by by_cases e : w a - w b = j <;> simp [mask, e]
    have msub (Y Z : Matrix ι ι (ResidueField O)) : mask w j (Y - Z) = mask w j Y - mask w j Z := Matrix.ext fun a b => by by_cases e : w a - w b = j <;> simp [mask, e]
    refine ⟨⟨(fun s => ⟨_, mask_mem j (b1 s)⟩, fun v => ⟨_, mask_mem j (neg_mem (b3 v).2)⟩),
      IsLocallyConstant.desc _ Subtype.val (((lift_lc (r.map f)).prodMk (hrbar.comp_continuous continuous_inv)).comp fun p => mask w j (p.1.map snd * p.2)) Subtype.val_injective,
      fun s t => Subtype.ext ?_, fun q n hn => Subtype.ext (Matrix.ext fun _ _ => by simp [b2 q n hn, mask]),
      fun v s => Subtype.ext ?_, Subtype.ext (Matrix.ext fun _ _ => by simp [b4, mask])⟩, ?_⟩
    · show mask w j _ = mask w j _ + rbar s * mask w j _ * rbar s⁻¹
      rw [← mul_mask j _ _ (hbar.2.2 s), ← mask_mul j _ _ (hbar.2.2 s⁻¹), ← madd, MonoidHom.map_mul, msnd_mul, lift_fst, lift_fst, _root_.mul_inv_rev,
        MonoidHom.map_mul, add_mul, mul_assoc _ (rbar t), ← mul_assoc (rbar t), inv2, one_mul, add_comm]; simp only [mul_assoc]
    · show mask w j _ = rbar (F.φ v s) * mask w j _ * rbar (F.φ v s)⁻¹ - mask w j _
      rw [← mul_mask j _ _ (hbar.2.2 _), ← mask_mul j _ _ (hbar.2.2 _), ← msub, eq_sub_of_add_eq' (b5 v s), sub_mul, mul_assoc, inv2]; congr 1; simp only [mul_neg, neg_mul, mul_one]; abel
    · rintro (⟨s, a, b⟩ | ⟨v, a, b⟩) e
      · change w a - w b = j at e; show (mask w j (((r.map f).hom s).map snd * rbar s⁻¹) * rbar s) a b = _; rw [z1, ← mask_mul j _ _ (hbar.2.2 s), mul_assoc, inv1, mul_one]; simp [mask, e]
      · change w a - w b = j at e; show -(mask w j _ a b) = _; rw [z2, neg_eq_iff_eq_neg]; simp [mask, e]
  · intro f hf hz y; let f0 : R →ₐ[O] D O := (inlAlgHom O (ResidueField O) (ResidueField O)).comp (res O R)
    have key (y) (hy : (f y).snd = 0) : f0 y = f y := TrivSqZeroExt.ext (by simp [f0]) hy.symm
    have := (hU _ _ _ _ (hmap f)).unique (y₁ := f0) (y₂ := f) ⟨AlgHom.ext fun b => key _ (hf b),
      Lift.ext (MonoidHom.ext fun s => Matrix.ext fun a b => key _ ((z1 f s a b).symm.trans (hz _))),
      fun v => Matrix.ext fun a b => key _ ((z2 f v a b).symm.trans (hz _))⟩ ⟨rfl, rfl, fun _ => rfl⟩
    rw [← this]; rfl
end -- clump:auto
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTangent =====

-- ===== clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedUniv =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedUniv", "h": "module\n\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivLift\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.MvPowerSeries.Inverse\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Tactic.TypeStar\nimport Mathlib.Topology.Sheaves.Init\nimport Std.Tactic.BVDecide.Normalize.Prop\n\n"}
section -- clump:auto
@[expose] public section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

section
variable {O : Type} [CommRing O] [IsLocalRing O]

private theorem map_max {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R] [CommRing R'] [Algebra O R'] [IsCO O R']
    (f : R →ₐ[O] R') {x : R} (hx : x ∈ maximalIdeal R) : f x ∈ maximalIdeal R' := by
  rwa [← res_eq_zero_iff O, UpperTheory.V.Alg.res_map f, res_eq_zero_iff]

private theorem quot_univ {A K : Type} [CommRing A] [Algebra O A] [IsCO O A] [CommRing K] [Algebra O K] [Nontrivial K]
    (I : Ideal A) (f0 : A →ₐ[O] K) (h0 : ∀ x ∈ I, f0 x = 0) :
    ∃ (A' : Type) (_ : CommRing A') (_ : Algebra O A') (_ : IsCO O A') (p : A →ₐ[O] A'), (∀ x ∈ I, p x = 0) ∧
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] (f : A →ₐ[O] R'), (∀ x ∈ I, f x = 0) →
        ∃! g : A' →ₐ[O] R', g.comp p = f := by
  have hne : I ≠ ⊤ := fun e => by
    have := h0 1 (e ▸ Submodule.mem_top)
    simp at this
  haveI := Ideal.Quotient.nontrivial_iff.2 hne
  haveI : IsCO O (A ⧸ I) := co_quot O A _ (Ideal.Quotient.mkₐ O I) (Ideal.Quotient.mkₐ_surjective O I)
  refine ⟨A ⧸ I, inferInstance, inferInstance, inferInstance, Ideal.Quotient.mkₐ O I,
    fun x hx => Ideal.Quotient.eq_zero_iff_mem.2 hx, fun R' _ _ f hf => ⟨Ideal.Quotient.liftₐ I f hf, rfl, fun g hg => ?_⟩⟩
  refine Ideal.Quotient.algHom_ext _ ?_
  rw [hg]
  rfl

private theorem pres [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    (A : Type) [CommRing A] [Algebra O A] [IsCO O A] :
    ∃ (n : ℕ) (π : MvPowerSeries (Fin n) O →ₐ[O] A), Function.Surjective π := by
  obtain ⟨n, a, ha⟩ := Submodule.fg_iff_exists_fin_generating_family.1 (IsNoetherian.noetherian (maximalIdeal A))
  have ham : ∀ s, a s ∈ maximalIdeal A := fun s => ha ▸ Submodule.subset_span ⟨s, rfl⟩
  haveI := co_mvps O O (Fin n)
  obtain ⟨F, ⟨-, hF⟩, -⟩ := co_ev O O A (Fin n) (Algebra.ofId O A) a ham
  refine ⟨n, F, co_surj O _ A F (le_trans ?_ le_sup_left)⟩
  rw [← ha, Submodule.span_le]
  rintro _ ⟨s, rfl⟩
  rw [← hF]
  refine Ideal.mem_map_of_mem _ ?_
  intro hu
  have := MvPowerSeries.isUnit_iff_constantCoeff.1 hu
  simp at this

private theorem X_mem {R σ : Type} [CommRing R] [IsLocalRing R] (s : σ) :
    (X s : MvPowerSeries σ R) ∈ maximalIdeal (MvPowerSeries σ R) := by
  intro hu
  have := MvPowerSeries.isUnit_iff_constantCoeff.1 hu
  simp at this

private noncomputable def Ca (O : Type) [CommRing O] (σ R : Type) [CommRing R] [Algebra O R] : R →ₐ[O] MvPowerSeries σ R :=
  IsScalarTower.toAlgHom O R (MvPowerSeries σ R)

private theorem coprod2 [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    (A B : Type) [CommRing A] [Algebra O A] [IsCO O A] [CommRing B] [Algebra O B] [IsCO O B] :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra O S) (_ : IsCO O S) (j : A →ₐ[O] S) (i : B →ₐ[O] S),
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (j' : A →ₐ[O] R') (i' : B →ₐ[O] R'),
        ∃! f : S →ₐ[O] R', f.comp j = j' ∧ f.comp i = i' := by
  obtain ⟨n, π, hπ⟩ := pres (O := O) A
  haveI := co_mvps O O (Fin n)
  haveI := co_mvps O B (Fin n)
  haveI := (co_res O).1
  obtain ⟨e, ⟨-, he⟩, -⟩ := co_ev O O (MvPowerSeries (Fin n) B) (Fin n) (Algebra.ofId O _) X X_mem
  have ext0 : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (F G : MvPowerSeries (Fin n) O →ₐ[O] R'),
      (∀ s, F (X s) = G (X s)) → F = G := fun R' _ _ _ F G h =>
    (co_ev O O R' (Fin n) (Algebra.ofId O _) (fun s => G (X s)) fun s => map_max G (X_mem s)).unique
      ⟨F.commutes, h⟩ ⟨G.commutes, fun _ => rfl⟩
  have key : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (j' : A →ₐ[O] R') (i' : B →ₐ[O] R'),
      ∃! F : MvPowerSeries (Fin n) B →ₐ[O] R', F.comp e = j'.comp π ∧ F.comp (Ca O _ B) = i' := by
    intro R' _ _ _ j' i'
    obtain ⟨F, ⟨h1, h2⟩, h3⟩ := co_ev O B R' (Fin n) i' (fun s => j' (π (X s)))
      fun s => map_max (j'.comp π) (X_mem s)
    refine ⟨F, ⟨ext0 _ _ _ fun s => by simp [he, h2], AlgHom.ext h1⟩, fun G hG => h3 G ⟨fun x => ?_, fun s => ?_⟩⟩
    · exact DFunLike.congr_fun hG.2 x
    · rw [← he]
      exact DFunLike.congr_fun hG.1 (X s)
  have kill : ∀ (R' : Type) [CommRing R'] [Algebra O R'] (j' : A →ₐ[O] R') (F : MvPowerSeries (Fin n) B →ₐ[O] R'),
      F.comp e = j'.comp π → ∀ x ∈ (RingHom.ker π).map e, F x = 0 := by
    intro R' _ _ j' F hF
    refine Ideal.map_le_iff_le_comap (K := RingHom.ker F).2 fun x hx => ?_
    show F (e x) = 0
    rw [show F (e x) = j' (π x) from DFunLike.congr_fun hF x, show π x = 0 from hx, map_zero]
  obtain ⟨F0, ⟨hF0, -⟩, -⟩ := key _ (res O A) (res O B)
  obtain ⟨S, _, _, _, p, hp, hS⟩ := quot_univ _ F0 (kill _ _ _ hF0)
  have H : RingHom.ker π.toRingHom ≤ RingHom.ker (p.comp e).toRingHom := fun x hx => hp _ (Ideal.mem_map_of_mem _ hx)
  let j : A →ₐ[O] S := AlgHom.liftOfSurjective π hπ (p.comp e) H
  have hj : j.comp π = p.comp e := AlgHom.ext fun x => AlgHom.liftOfSurjective_apply π hπ (p.comp e) H x
  refine ⟨S, inferInstance, inferInstance, inferInstance, j, p.comp (Ca O _ B), fun R' _ _ _ j' i' => ?_⟩
  obtain ⟨F, ⟨h1, h2⟩, h3⟩ := key R' j' i'
  obtain ⟨g, hg, hg'⟩ := hS R' F (kill _ _ _ h1)
  refine ⟨g, ⟨(AlgHom.cancel_right hπ).1 ?_, ?_⟩, fun g' h' => hg' g' (h3 _ ⟨?_, h'.2⟩)⟩
  · rw [AlgHom.comp_assoc, hj, ← AlgHom.comp_assoc, hg, h1]
  · rw [← AlgHom.comp_assoc, hg, h2]
  · rw [AlgHom.comp_assoc, ← hj, ← AlgHom.comp_assoc, h'.1]

end

section
variable {O : Type} [CommRing O] [IsLocalRing O] {R : Type} [CommRing R] [Algebra O R]

private def Cut (O R : Type) [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R]
    (P : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'], (R →ₐ[O] R') → Prop) : Prop :=
  ∃ I : Ideal R, ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'),
    P R' f ↔ ∀ x ∈ I, f x = 0

private theorem Cut.eq (x y : R) : Cut O R fun _ _ _ _ f => f x = f y :=
  ⟨Ideal.span {x - y}, fun R' _ _ _ f => by
    constructor
    · intro h z hz
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hz
      simp [h]
    · intro h
      have := h _ (Ideal.mem_span_singleton_self _)
      rwa [map_sub, sub_eq_zero] at this⟩

private theorem Cut.all {κ : Sort*} {P : κ → ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'], (R →ₐ[O] R') → Prop}
    (h : ∀ i, Cut O R (P i)) : Cut O R fun R' _ _ _ f => ∀ i, P i R' f := by
  choose I hI using h
  refine ⟨⨆ i, I i, fun R' _ _ _ f => ?_⟩
  simp only [hI]
  exact (iSup_le_iff (f := I) (a := RingHom.ker f)).symm

private theorem Cut.and {P Q : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'], (R →ₐ[O] R') → Prop}
    (h : Cut O R P) (h' : Cut O R Q) : Cut O R fun R' _ _ _ f => P R' f ∧ Q R' f := by
  obtain ⟨I, hI⟩ := h
  obtain ⟨J, hJ⟩ := h'
  refine ⟨I ⊔ J, fun R' _ _ _ f => ?_⟩
  simp only [hI, hJ]
  exact (sup_le_iff (a := I) (b := J) (c := RingHom.ker f)).symm

private theorem Cut.congr {P Q : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'], (R →ₐ[O] R') → Prop}
    (h : Cut O R P) (e : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'), Q R' f ↔ P R' f) :
    Cut O R Q := by
  obtain ⟨I, hI⟩ := h
  exact ⟨I, fun R' _ _ _ f => (e R' f).trans (hI R' f)⟩

private theorem Cut.mat {ι : Type} (x y : Matrix ι ι R) : Cut O R fun _ _ _ _ f => x.map f = y.map f :=
  (Cut.all fun a => Cut.all fun b => Cut.eq (x a b) (y a b)).congr fun _ _ _ _ _ => Matrix.ext_iff.symm

private theorem Cut.univ [IsCO O R] {P : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'], (R →ₐ[O] R') → Prop}
    (h : Cut O R P) {K : Type} [CommRing K] [Algebra O K] [IsCO O K] (f0 : R →ₐ[O] K) (h0 : P K f0) :
    ∃ (A' : Type) (_ : CommRing A') (_ : Algebra O A') (_ : IsCO O A') (p : R →ₐ[O] A'), P A' p ∧
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'), P R' f →
        ∃! g : A' →ₐ[O] R', g.comp p = f := by
  obtain ⟨I, hI⟩ := h
  obtain ⟨A', _, _, _, p, hp, hA⟩ := quot_univ I f0 ((hI K f0).1 h0)
  exact ⟨A', inferInstance, inferInstance, inferInstance, p, (hI A' p).2 hp,
    fun R' _ _ _ f hf => hA R' f ((hI R' f).1 hf)⟩

variable {ι X : Type} [Fintype ι] [DecidableEq ι] [AddCommGroup X] {w : ι → X} (Φ : FormData O w) [IsCO O R]

omit [IsLocalRing O] [IsCO O R] in
private theorem map_alg {R' : Type} [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R') (M : Matrix ι ι O) :
    (M.map (algebraMap O R)).map f = M.map (algebraMap O R') := Matrix.ext fun _ _ => f.commutes _

omit [IsLocalRing O] [IsCO O R] in
private theorem mmul {R' : Type} [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R') (M N : Matrix ι ι R) :
    (M * N).map f = M.map f * N.map f := Matrix.map_mul

omit [IsLocalRing O] [IsCO O R] in
private theorem mone {R' : Type} [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R') :
    (1 : Matrix ι ι R).map f = 1 := Matrix.map_one _ (map_zero f) (map_one f)

private theorem cut_HH (h : Matrix ι ι R) (hh : h.map (res O R) = 1) :
    Cut O R fun _ _ _ _ f => Φ.HH (h.map f) := by
  refine ((Cut.mat (h.transpose * Φ.JR R * h) (Φ.JR R)).and (Cut.all fun a => Cut.all fun b =>
    Cut.all fun (_ : Φ.blk a ≠ Φ.blk b) => Cut.eq (h a b) 0)).congr fun R' _ _ _ f => ?_
  have e : (h.map f).map (res O R') = 1 := by
    rw [← hh]; exact Matrix.ext fun a b => UpperTheory.V.Alg.res_map f _
  simp only [FormData.HH, FormData.JR, mmul, map_alg, e, and_true, map_zero, Matrix.map_apply, Matrix.transpose_map]

private theorem HH_one : Φ.HH (1 : Matrix ι ι R) :=
  ⟨by simp, fun a b h => Matrix.one_apply_ne fun e => h (e ▸ rfl), mone _⟩

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* Matrix ι ι (ResidueField O)}

private theorem hom_map {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') (r : Lift O rbar R)
    (s : Γ) : (r.map f).hom s = (r.hom s).map f := rfl

private theorem hom_res (r : Lift O rbar R) (s : Γ) : (r.hom s).map (res O R) = rbar s := Matrix.ext (r.red s)

variable [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]

private theorem cut_InH (r0 : Lift O rbar O) (r : Lift O rbar R) :
    Cut O R fun R' _ _ _ f => Φ.InH r0.hom R' (r.map f) := by
  refine (Cut.all fun s => cut_HH Φ (r.hom s * (r0.hom s⁻¹).map (algebraMap O R)) ?_).congr fun R' _ _ _ f => ?_
  · have e : (r0.hom s⁻¹).map (algebraMap O (ResidueField O)) = rbar s⁻¹ := by
      rw [← hom_res r0]
      exact Matrix.ext fun a b => ((res O O).commutes _).symm
    rw [mmul, map_alg, hom_res, e, ← map_mul, mul_inv_cancel, map_one]
  · simp only [FormData.InH, mmul, map_alg, hom_map]

private theorem InH_self (r0 : Lift O rbar O) : Φ.InH r0.hom O r0 := fun s => by
  have e : (r0.hom s⁻¹).map (algebraMap O O) = r0.hom s⁻¹ := rfl
  rw [e, ← map_mul, mul_inv_cancel, map_one]
  exact HH_one Φ

end

section
variable {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
  {ι : Type} [Fintype ι] [DecidableEq ι] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
  {rbar : Γ →* Matrix ι ι (ResidueField O)}

private theorem all_univ {R0 : Type} [CommRing R0] [Algebra O R0] [IsCO O R0] (u : Lift O rbar R0)
    (hu : Represents (fun _ _ _ _ _ => True) u) (T : Type) [Finite T]
    (B : Type) [CommRing B] [Algebra O B] [IsCO O B] :
    ∃ (A : Type) (_ : CommRing A) (_ : Algebra O A) (_ : IsCO O A) (i : B →ₐ[O] A) (r : Lift O rbar A)
      (α : T → Matrix ι ι A), (∀ v, (α v).map (res O A) = 1) ∧
      ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (i' : B →ₐ[O] R') (r' : Lift O rbar R')
        (α' : T → Matrix ι ι R'), (∀ v, (α' v).map (res O R') = 1) →
        ∃! f : A →ₐ[O] R', f.comp i = i' ∧ r.map f = r' ∧ ∀ v, (α v).map f = α' v := by
  obtain ⟨S, _, _, _, j, i, hS⟩ := coprod2 (O := O) R0 B
  haveI := co_mvps O S (T × ι × ι)
  let Y : T → Matrix ι ι (MvPowerSeries (T × ι × ι) S) := fun v => Matrix.of fun a b => X (v, a, b)
  have hY : ∀ (R' : Type) [CommRing R'] [Algebra O R'] (f : MvPowerSeries (T × ι × ι) S →ₐ[O] R') v,
      (1 + Y v).map f = 1 + Matrix.of fun a b => f (X (v, a, b)) := fun R' _ _ f v => by
    rw [Matrix.map_add _ (map_add f), mone]; rfl
  refine ⟨MvPowerSeries (T × ι × ι) S, inferInstance, inferInstance, inferInstance, (Ca O _ S).comp i,
    u.map ((Ca O _ S).comp j), fun v => 1 + Y v, fun v => ?_, fun R' _ _ _ i' r' α' hα => ?_⟩
  · rw [hY, add_eq_left]
    exact Matrix.ext fun a b => (res_eq_zero_iff O _ _).2 (X_mem _)
  · obtain ⟨j', hj, hj'⟩ := (hu R').2 r' trivial
    obtain ⟨g, ⟨hg1, hg2⟩, hg⟩ := hS R' j' i'
    obtain ⟨f, ⟨h1, h2⟩, h3⟩ := co_ev O S R' (T × ι × ι) g (fun s => (α' s.1 - 1) s.2.1 s.2.2) fun s => by
      rw [← res_eq_zero_iff O]
      have : (α' s.1 - 1).map (res O R') = 0 := by rw [Matrix.map_sub _ (map_sub _), hα, mone, sub_self]
      exact congrFun (congrFun this s.2.1) s.2.2
    have h1' : f.comp (Ca O _ S) = g := AlgHom.ext h1
    refine ⟨f, ⟨?_, ?_, fun v => ?_⟩, fun f' ⟨k1, k2, k3⟩ => h3 f' ⟨fun x => ?_, fun s => ?_⟩⟩
    · rw [← AlgHom.comp_assoc, h1', hg2]
    · rw [← hj, ← hg1, ← h1']; rfl
    · rw [hY, ← eq_sub_iff_add_eq']
      exact Matrix.ext fun a b => h2 (v, a, b)
    · exact DFunLike.congr_fun (hg (f'.comp (Ca O _ S)) ⟨hj' _ k2, k1⟩) x
    · have := k3 s.1
      rw [hY, ← eq_sub_iff_add_eq'] at this
      exact congrFun (congrFun this s.2.1) s.2.2

private theorem framed_of_univ {X : Type} [AddCommGroup X] {w : ι → X} (Φ : FormData O w)
    {R0 : Type} [CommRing R0] [Algebra O R0] [IsCO O R0] (u : Lift O rbar R0)
    (hu : Represents (fun _ _ _ _ _ => True) u) (r0 : Lift O rbar O)
    (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q)))
    (hL : ∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) (hL0 : ∀ q, L q O (r0.comap (F.ψ q) (F.hψ q)))
    (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (i : B →ₐ[O] R) (r : Lift O rbar R)
      (α : F.T → Matrix ι ι R), IsUnivFramed Φ r0.hom F L ρ i r α := by
  haveI := (co_res O).1
  obtain ⟨A, _, _, _, i, r, α, hα, hA⟩ := all_univ u hu F.T B
  have c1 : Cut O A fun R' _ _ _ f => Φ.InH r0.hom R' (r.map f) ∧ (∀ v, Φ.HH ((α v).map f)) ∧ (α F.v0).map f = 1 ∧
      ∀ v s, (r.map f).hom (F.φ v s) * (α v).map f = (α v).map f * ((ρ v).hom s).map (f.comp i) := by
    refine ((cut_InH Φ r0 r).and ((Cut.all fun v => cut_HH Φ _ (hα v)).and ((Cut.mat (α F.v0) 1).and
      (Cut.all fun v => Cut.all fun s =>
        Cut.mat (r.hom (F.φ v s) * α v) (α v * ((ρ v).hom s).map i))))).congr fun R' _ _ _ f => ?_
    simp only [mone, mmul]
    rfl
  have e0 : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (r' : Lift O rbar R'),
      r'.map (res O R') = r0.map (res O O) := fun R' _ _ _ r' =>
    Lift.ext (MonoidHom.ext fun s => (hom_res r' s).trans (hom_res r0 s).symm)
  obtain ⟨A1, _, _, _, p, ⟨p1, p2, p3, p4⟩, hA1⟩ := c1.univ (res O A) (by
    refine ⟨?_, fun v => ?_, hα _, fun v s => ?_⟩
    · rw [e0]
      obtain ⟨I, hI⟩ := cut_InH Φ r0 r0
      refine (hI _ _).2 fun x hx => ?_
      rw [show x = 0 from (hI O (AlgHom.id O O)).1 (InH_self Φ r0) x hx, map_zero]
    · rw [hα]; exact HH_one Φ
    · rw [hα, mul_one, one_mul, hom_map, hom_res]
      exact Matrix.ext fun a b => ((UpperTheory.V.Alg.res_map i _).trans ((ρ v).red s a b)).symm)
  have c2 : Cut O A1 fun R' _ _ _ f => ∀ q, L q R' (((r.map p).map f).comap (F.ψ q) (F.hψ q)) :=
    Cut.all fun q => (hL q).closed A1 ((r.map p).comap (F.ψ q) (F.hψ q)) fun s => by
      have := p1 (F.ψ q s)
      rwa [← map_inv] at this
  obtain ⟨A2, _, _, _, p', hp', hA2⟩ := c2.univ (res O A1) (fun q => by
    rw [e0]
    obtain ⟨I, hI⟩ := (hL q).closed O (r0.comap (F.ψ q) (F.hψ q)) (InH_self Φ (r0.comap (F.ψ q) (F.hψ q)))
    refine (hI _ (res O O)).2 fun x hx => ?_
    rw [show x = 0 from (hI O (AlgHom.id O O)).1 (hL0 q) x hx, map_zero])
  refine ⟨A2, inferInstance, inferInstance, inferInstance, (p'.comp p).comp i, r.map (p'.comp p),
    fun v => (α v).map (p'.comp p), ?_, fun R' _ _ _ i' r' α' ⟨k1, k2, k3, k4, k5⟩ => ?_⟩
  · obtain ⟨I, hI⟩ := c1
    obtain ⟨q1, q2, q3, q4⟩ := (hI A2 (p'.comp p)).2 fun x hx => by
      rw [AlgHom.comp_apply, (hI A1 p).1 ⟨p1, p2, p3, p4⟩ x hx, map_zero]
    exact ⟨q1, hp', q2, q3, q4⟩
  · obtain ⟨f, ⟨rfl, rfl, h3⟩, hf⟩ := hA R' i' r' α' fun v => (k3 v).2.2
    obtain rfl : α' = fun v => (α v).map f := funext fun v => (h3 v).symm
    obtain ⟨g, rfl, hg⟩ := hA1 R' f ⟨k1, k3, k4, k5⟩
    obtain ⟨g', rfl, hg'⟩ := hA2 R' g k2
    exact ⟨g', ⟨rfl, rfl, fun _ => rfl⟩, fun g'' h => hg' g'' (hg _ (hf ((g''.comp p').comp p) h))⟩

end

theorem UpperTheory.V.Alg.framed_univ :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (ι X : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup X] (w : ι → X) (Φ : FormData O w), IsUnit (2 : O) → ∀ [Finite (ResidueField O)] [CharP (ResidueField O) l] (Γ : Type) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (rbar : Γ →* Matrix ι ι (ResidueField O)) (r0 : Lift O rbar O) (hbar : Φ.Normalises rbar), Φ.Normalises r0.hom → ∀ [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [T2Space Γ], PhiCond Γ l → ∀ (F : Frame Γ) (L : ∀ q, Cond O (rbar.comp (F.ψ q))), (∀ q, ∀ n ∈ F.N q, rbar (F.ψ q n) = 1) → (∀ q, Φ.IsLocCond (r0.hom.comp (F.ψ q)) (F.N q) (L q)) → (∀ q, L q O (r0.comap (F.ψ q) (F.hψ q))) →
      ∀ (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (ρ : ∀ v, Lift O (rbar.comp (F.φ v)) B), (∀ v, Φ.InH (r0.hom.comp (F.φ v)) B (ρ v)) → ∀ (_ : Unit),
      ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (_ : IsCO O R) (i : B →ₐ[O] R) (r : Lift O rbar R) (α : F.T → Matrix ι ι R), IsUnivFramed Φ r0.hom F L ρ i r α := by
  intro l _ O _ _ _ _ ι X _ _ _ w Φ _ _ _ Γ _ _ _ rbar r0 _ _ _ _ _ hΦ F L _ hL hL0 B _ _ _ ρ _ _
  have hc : IsLocallyConstant rbar := by
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x => ?_
    have := Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun b => (r0.cont a b 1).eventually_eq x
    filter_upwards [this] with y hy
    refine Matrix.ext fun a b => ?_
    have h := Ideal.Quotient.eq.1 (hy a b)
    rw [pow_one, ← res_eq_zero_iff O, map_sub, sub_eq_zero, r0.red, r0.red] at h
    exact h
  obtain ⟨R0, _, _, _, u, hu⟩ := univ_lift l O Γ ι rbar hΦ hc
  exact framed_of_univ Φ u hu r0 F L hL hL0 B ρ
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedUniv =====

-- ===== clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.RelPres =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.RelPres", "h": "module\n\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries\npublic import Mathlib.RingTheory.MvPowerSeries.Inverse\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerGen\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PresIndep\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.PresNew\nimport Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PiSpanVariable\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.MvPowerSeries.Equiv\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Topology.Sheaves.Init\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps\n\n"}
section -- clump:auto
@[expose] public section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

open UpperTheory.V.Alg.ObsPres

private theorem rel_pres_max_le {O : Type} [CommRing O] [IsLocalRing O] {X : Type} [AddCommGroup X] {R : Type}
    [CommRing R] [Algebra O R] [IsCO O R] (W : WPres O X R) (hz : ∀ s, W.z s ∈ maximalIdeal R) :
    maximalIdeal R ≤ Ideal.span (Set.range W.z) ⊔ (maximalIdeal O).map (algebraMap O R) := by
  intro x hx
  obtain ⟨f, rfl⟩ := W.surj x
  have h1 := _root_.UpperTheory.Reformulated.B.PowerSeriesMemSpanAllVariables.pi_span_X Finset.univ (f - algebraMap O _ (constantCoeff f)) (fun n hn => by
    have : n = 0 := Finsupp.ext fun i => hn i (Finset.mem_univ i)
    subst this
    simp [MvPowerSeries.algebraMap_apply])
  have h2 : ∀ I : Ideal R, (∀ s, W.z s ∈ I) → W.π f - algebraMap O R (constantCoeff f) ∈ I := by
    intro I hI
    have hle : Ideal.span (Set.range (MvPowerSeries.X : W.σ → MvPowerSeries W.σ O)) ≤ I.comap W.π := by
      rw [Ideal.span_le]
      rintro _ ⟨s, rfl⟩
      exact hI s
    have := hle h1
    rwa [Ideal.mem_comap, map_sub, AlgHom.commutes] at this
  have h3 : algebraMap O R (constantCoeff f) ∈ maximalIdeal R := by
    simpa using sub_mem hx (h2 _ hz)
  have h4 : constantCoeff f ∈ maximalIdeal O := fun hu => h3 (hu.map _)
  have h5 := h2 (Ideal.span (Set.range W.z)) fun s => Ideal.subset_span ⟨s, rfl⟩
  simpa using add_mem (Ideal.mem_sup_left h5)
    (Ideal.mem_sup_right (Ideal.mem_map_of_mem (algebraMap O R) h4))

theorem UpperTheory.V.Alg.rel_pres :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (WB : WPres O X B) (W₀ : WPres O X R) (i : B →ₐ[O] R), (∀ s, WB.z s ∈ maximalIdeal B) → (∀ s, W₀.z s ∈ maximalIdeal R) → (∀ s, i (WB.z s) ∈ W₀.part (WB.wt s)) →
      ∀ (τ : Type) [Fintype τ] (z : τ → R) (wt : τ → X), (∀ t, z t ∈ maximalIdeal R ∧ z t ∈ W₀.part (wt t)) →
      maximalIdeal R ≤ Ideal.span (Set.range z) ⊔ (maximalIdeal B).map i ⊔ maximalIdeal R ^ 2 →
      ∃ (W : WPres O X R) (κ : Type) (_ : Fintype κ) (e : WB.σ ⊕ τ ≃ W.σ) (f : κ → MvPowerSeries W.σ O) (wf : κ → X), IsRelPres WB i W e f wf ∧
        (∀ t, W.z (e (.inr t)) = z t ∧ W.wt (e (.inr t)) = wt t) ∧ (∀ j, W.part j = W₀.part j) ∧
        ∀ c : κ → O, ∑ u, c u • f u ∈ (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)) ⊔ maximalIdeal (MvPowerSeries W.σ O) * RingHom.ker W.π → ∀ u, c u ∈ maximalIdeal O := by
  intro O _ _ _ _ X _ _ _ B _ _ _ R _ _ _ WB W₀ i hB h0 hi τ _ z wt hz hgen
  classical
  have him : ∀ s, i (WB.z s) ∈ maximalIdeal R := fun s => by
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hB s
  have hz' : ∀ s : WB.σ ⊕ τ, Sum.elim (fun s => i (WB.z s)) z s ∈ maximalIdeal R ∧
      Sum.elim (fun s => i (WB.z s)) z s ∈ W₀.part (Sum.elim WB.wt wt s) := by
    rintro (s | t)
    · exact ⟨him s, hi s⟩
    · exact hz t
  obtain ⟨W, e, he⟩ := pres_new O X R W₀ h0 (WB.σ ⊕ τ) (Sum.elim WB.wt wt) (Sum.elim (fun s => i (WB.z s)) z) hz'
    (hgen.trans (sup_le_sup_right (sup_le (le_sup_of_le_left (Ideal.span_mono (by
      rintro _ ⟨t, rfl⟩
      exact ⟨.inr t, rfl⟩))) (by
        refine (Ideal.map_mono (rel_pres_max_le WB hB)).trans ?_
        rw [Ideal.map_sup]
        refine sup_le_sup ?_ ?_
        · rw [Ideal.map_span]
          refine Ideal.span_mono ?_
          rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
          exact ⟨.inl s, rfl⟩
        · rw [Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
          intro c hc
          rw [Ideal.mem_comap, Ideal.mem_comap, AlgHom.commutes]
          exact Ideal.mem_map_of_mem _ hc)) _))
  have hW : ∀ s, W.z s ∈ maximalIdeal R ∧ W.z s ∈ W₀.part (W.wt s) := fun s => by
    obtain ⟨s, rfl⟩ := e.surjective s
    rw [(he s).1, (he s).2]
    exact hz' s
  have hpart := pres_indep O X R W₀ h0 W (fun s => (hW s).1) fun s => (hW s).2
  have hcomm : W.π.comp (MvPowerSeries.rename fun s => e (.inl s)) = i.comp WB.π := by
    refine (co_ev O O R WB.σ (Algebra.ofId _ _) _ him).unique ⟨fun x => ?_, fun s => ?_⟩ ⟨fun x => ?_, fun s => rfl⟩
    · exact AlgHom.commutes _ x
    · rw [AlgHom.comp_apply, rename_X]
      exact (he (.inl s)).1
    · exact AlgHom.commutes _ x
  have hcomm' : ∀ x, W.π (MvPowerSeries.rename (fun s => e (.inl s)) x) = i (WB.π x) :=
    fun x => AlgHom.congr_fun hcomm x
  haveI : IsCO O (MvPowerSeries W.σ O) := co_mvps O O W.σ
  obtain ⟨n, g, c, hg, hK⟩ := ker_gen O X W.σ W.wt _ W.homog
  have hle : (RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s)) ≤ RingHom.ker W.π := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, RingHom.mem_ker, hcomm', (RingHom.mem_ker).1 hx, map_zero]
  obtain ⟨s, hs, hmin⟩ := UpperTheory.V.Alg.ObsPres.op_min (RingHom.ker W.π)
    ((RingHom.ker WB.π).map (MvPowerSeries.rename fun s => e (.inl s))) g (by rw [← hK, sup_eq_right.2 hle])
  refine ⟨W, s, inferInstance, e, fun u => g u, fun u => c u, ⟨fun s => (he (.inl s)).2, hcomm', fun u => hg u, hs⟩,
    fun t => he (.inr t), hpart, fun a ha u hu => ?_⟩
  refine hmin (fun u => algebraMap O _ (a u)) ?_ u (hu.map _)
  simpa only [Algebra.smul_def] using ha
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.RelPres =====

-- ===== clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LemmaP =====
-- clump-header: {"m": "Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LemmaP", "h": "module\n\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTwoCoboundaries\npublic import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSurj\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedGrading\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedTangent\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.FramedUniv\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.KerGen\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.MapPart\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ObsClass\npublic import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.RelPres\nimport Mathlib.Algebra.Order.Floor.Extended\nimport Mathlib.Algebra.Order.Floor.Semifield\nimport Mathlib.Algebra.Order.Interval.Basic\nimport Mathlib.Analysis.Complex.UpperHalfPlane.Basic\nimport Mathlib.Analysis.Normed.Algebra.GelfandRadius\nimport Mathlib.Analysis.SpecialFunctions.Bernstein\nimport Mathlib.Analysis.SpecialFunctions.Gamma.Basic\nimport Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp\nimport Mathlib.Combinatorics.Enumerative.DyckWord\nimport Mathlib.Combinatorics.SimpleGraph.Triangle.Removal\nimport Mathlib.Data.NNRat.Floor\nimport Mathlib.Data.Nat.Choose.Multinomial\nimport Mathlib.Geometry.Euclidean.Volume.Basic\nimport Mathlib.NumberTheory.Chebyshev\nimport Mathlib.NumberTheory.Height.NumberField\nimport Mathlib.NumberTheory.Height.Projectivization\nimport Mathlib.NumberTheory.LucasLehmer\nimport Mathlib.NumberTheory.SelbergSieve\nimport Mathlib.RingTheory.AdicCompletion.Noetherian\nimport Mathlib.RingTheory.Coalgebra.IsFrobenius\nimport Mathlib.RingTheory.Henselian\nimport Mathlib.RingTheory.HopfAlgebra.Basic\nimport Mathlib.RingTheory.Radical.NatInt\nimport Mathlib.RingTheory.WittVector.IsPoly\nimport Mathlib.Tactic.Basify\nimport Mathlib.Tactic.Echelon.Zsqrtd\nimport Mathlib.Tactic.Inclusion.Extension.Core.Core\nimport Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp\nimport Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic\nimport Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses\nimport Mathlib.Tactic.Linter.HaveILetI\nimport Mathlib.Tactic.Linter.Style\nimport Mathlib.Tactic.NormNum.Irrational\nimport Mathlib.Tactic.NormNum.IsCoprime\nimport Mathlib.Tactic.NormNum.IsSquare\nimport Mathlib.Tactic.NormNum.LegendreSymbol\nimport Mathlib.Tactic.NormNum.ModEq\nimport Mathlib.Tactic.NormNum.NatFib\nimport Mathlib.Tactic.NormNum.NatLog\nimport Mathlib.Tactic.NormNum.NatSqrt\nimport Mathlib.Tactic.NormNum.Ordinal\nimport Mathlib.Tactic.NormNum.Parity\nimport Mathlib.Tactic.NormNum.Prime\nimport Mathlib.Tactic.NormNum.RealSqrt\nimport Mathlib.Tactic.Polynomial.Basic\nimport Mathlib.Tactic.ReduceModChar\nimport Mathlib.Topology.Sheaves.Init\n\n"}
section -- clump:auto
@[expose] public section

open IsLocalRing MvPowerSeries UpperTheory.V.Alg

private theorem lp_wcomp_mul {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X) {c : X}
    {a : MvPowerSeries σ O} (ha : a ∈ wtPart O wt c) (j : X) (b : MvPowerSeries σ O) :
    wcomp O wt j (b * a) = wcomp O wt (j - c) b * a := by
  classical
  ext n
  rw [coeff_wcomp, coeff_mul, coeff_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = c
    · rw [coeff_wcomp, ite_eq_left]
      rw [← h, ← hp', map_add (f := _), h2, add_sub_cancel_right]
    · rw [ha _ h2, mul_zero, mul_zero]
  · refine (Finset.sum_eq_zero fun p hp => ?_).symm
    have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
    by_cases h2 : Finsupp.weight wt p.2 = c
    · rw [coeff_wcomp, ite_eq_right, zero_mul]
      intro h1
      exact h (by rw [← hp', map_add (f := _), h1, h2, sub_add_cancel])
    · rw [ha _ h2, mul_zero]

private theorem lp_homog_mul {O σ X κ : Type} [CommRing O] [AddCommGroup X] [Fintype κ] (wt : σ → X)
    (I : Ideal (MvPowerSeries σ O)) (hI : IsHomog O wt I) (f : κ → MvPowerSeries σ O) (c : κ → X)
    (hf : ∀ u, f u ∈ wtPart O wt (c u)) : IsHomog O wt (I * Ideal.span (Set.range f)) := by
  intro x hx j
  refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
  · obtain ⟨d, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hb

    rw [Finset.mul_sum, map_sum]
    refine Ideal.sum_mem _ fun u _ => ?_
    rw [← mul_assoc, lp_wcomp_mul wt (hf u)]
    exact Ideal.mul_mem_mul (hI _ (I.mul_mem_right _ ha) _) (Ideal.subset_span ⟨u, rfl⟩)
  · rw [map_add (f := _)]; exact add_mem ha hb

private theorem lp_homog_sup {O σ X : Type} [CommRing O] [AddCommGroup X] (wt : σ → X)
    (I J : Ideal (MvPowerSeries σ O)) (hI : IsHomog O wt I) (hJ : IsHomog O wt J) : IsHomog O wt (I ⊔ J) := by
  intro x hx j
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add (f := _)]
  exact Submodule.add_mem_sup (hI a ha j) (hJ b hb j)


private theorem lp_homog_max {O σ X : Type} [CommRing O] [IsLocalRing O] [AddCommGroup X] (wt : σ → X) :
    IsHomog O wt (maximalIdeal (MvPowerSeries σ O)) := by
  intro x hx j
  rw [UpperTheory.V.Alg.ObsPres.op_mem_max] at hx ⊢
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_wcomp]
  split_ifs
  · exact hx
  · exact zero_mem _


private theorem lp_pad {X κ : Type} [Fintype κ] (wf : κ → X) (n : X → ℕ) (S : Finset X)
    (hS : ∀ j, j ∉ S → n j = 0) (h : ∀ j, Nat.card {u // wf u = j} ≤ n j) :
    ∃ (κ' : Type) (_ : Fintype κ') (wf' : κ' → X), ∀ j, Nat.card {u : κ ⊕ κ' // Sum.elim wf wf' u = j} = n j := by
  classical
  refine ⟨Σ j : S, Fin (n j - Nat.card {u // wf u = j}), inferInstance, fun x => x.1, fun j => ?_⟩
  rw [Nat.card_congr (Equiv.subtypeSum), Nat.card_sum]
  simp only [Sum.elim_inl, Sum.elim_inr]
  by_cases hj : j ∈ S
  · have e : {x : (Σ j : S, Fin (n j - Nat.card {u // wf u = j})) // (x.1 : X) = j} ≃
        Fin (n j - Nat.card {u // wf u = j}) :=
      (Equiv.subtypeEquivRight (fun x => by
        rw [← Subtype.ext_iff (a2 := (⟨j, hj⟩ : S))])).trans
        (Equiv.sigmaSubtype (β := fun j : S => Fin (n j - Nat.card {u // wf u = j})) ⟨j, hj⟩)
    rw [Nat.card_congr e, Nat.card_eq_fintype_card (α := Fin _), Fintype.card_fin]
    have := h j
    omega
  · haveI : IsEmpty {x : (Σ j : S, Fin (n j - Nat.card {u // wf u = j})) // (x.1 : X) = j} :=
      ⟨fun x => hj (x.2 ▸ x.1.1.2)⟩
    have := h j
    rw [hS j hj] at this ⊢
    have h0 : Nat.card {x : (Σ j : S, Fin (n j - Nat.card {u // wf u = j})) // (x.1 : X) = j} = 0 :=
      Nat.card_of_isEmpty
    omega


private theorem lp_ob_zero {O ι X Γ : Type} [CommRing O] [IsLocalRing O] [Fintype ι] [DecidableEq ι] [AddCommGroup X]
    {w : ι → X} (Φ : FormData O w) [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* Matrix ι ι (ResidueField O)}
    (hbar : Φ.Normalises rbar) (F : Frame Γ) (j : X) (hj : ∀ a b, w a - w b ≠ j) :
    Module.finrank (ResidueField O) (F.Ob (FormData.adRep hbar j)) = 0 := by
  haveI : Subsingleton (Φ.gw (ResidueField O) j) :=
    ⟨fun x y => Subtype.ext (Matrix.ext fun a b => (x.2.2 a b (hj a b)).trans (y.2.2 a b (hj a b)).symm)⟩
  haveI : Subsingleton (F.Ob (FormData.adRep hbar j)) := (Submodule.mkQ_surjective _).subsingleton
  exact Module.finrank_zero_of_subsingleton

theorem UpperTheory.V.Alg.lemmaP :
    LemmaP := by
  intro l _ O _ _ _ _ _ _ hl ι X _ _ _ _ _ w Φ Γ _ _ _ _ _ _ hΦ rbar r0 hbar h0 F L hN hL hL0 hfin B _ _ _ WB ρ hWB hρ hρw
  classical
  have h2 : IsUnit (2 : O) := by
    rw [← residue_ne_zero_iff_isUnit, map_ofNat]
    intro h
    have h' := (CharP.cast_eq_zero_iff (ResidueField O) l 2).1 (by exact_mod_cast h)
    exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h')
  obtain ⟨R, _, _, _, i, r, α, hU⟩ := framed_univ l O ι X w Φ h2 Γ rbar r0 hbar h0 hΦ F L hN hL hL0 B ρ hρ ()
  obtain ⟨W₀, g1, g2, g3, g4⟩ := framed_grading O ι X w Φ h2 Γ rbar r0 hbar h0 F L hN hL hL0 B ρ hρ WB hWB hρw R i r α hU
  obtain ⟨τ, _, z, wt, t1, t2, t3, t4⟩ := framed_tangent O ι X w Φ h2 Γ rbar r0 hbar h0 F L hN hL hL0 B ρ hρ R i r α hU
  have hone : ∀ c : O, algebraMap O R c ∈ W₀.part 0 := fun c => by
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ SetLike.GradedOne.one_mem
  have hz : ∀ t, z t ∈ maximalIdeal R ∧ z t ∈ W₀.part (wt t) := by
    intro t
    obtain ⟨a, b, hab, ⟨s, hs⟩ | ⟨v, hv⟩⟩ := t1 t
    · rw [hs, hab]
      refine ⟨?_, sub_mem (g3 s a b) ?_⟩
      · rw [← res_eq_zero_iff O, map_sub, r.red, ← r0.red, sub_eq_zero]
        exact (res_map (Algebra.ofId O R) _).symm
      · by_cases e : w a = w b
        · rw [e, sub_self]; exact hone _
        · rw [h0.2.2 s a b e, map_zero]; exact zero_mem _
    · rw [hv, hab, Matrix.sub_apply]
      refine ⟨?_, sub_mem (g4 v a b) ?_⟩
      · have := congrFun (congrFun (hU.1.2.2.1 v).2.2 a) b
        rw [Matrix.map_apply] at this
        rw [← res_eq_zero_iff O, map_sub, this, sub_eq_zero, Matrix.one_apply, Matrix.one_apply]
        split_ifs <;> simp
      · rw [Matrix.one_apply]
        split_ifs with e
        · rw [e, sub_self]; exact SetLike.GradedOne.one_mem
        · exact zero_mem _
  obtain ⟨W, κ, _, e, f, wf, hrel, p1, p2, p3⟩ := rel_pres O X B R WB W₀ i hWB g1 g2 τ z wt hz t2
  obtain ⟨q1, q2, q3, q4⟩ := hrel
  have bound : ∀ j, Nat.card {u // wf u = j} ≤ Module.finrank (ResidueField O) (F.Ob (FormData.adRep hbar j)) := by
    haveI : IsCO O (MvPowerSeries W.σ O) := co_mvps O O _
    haveI : IsCO O (MvPowerSeries WB.σ O) := co_mvps O O _
    have hX : ∀ (σ : Type) (s : σ), (MvPowerSeries.X s : MvPowerSeries σ O) ∈ maximalIdeal _ := fun σ s => by
      rw [UpperTheory.V.Alg.ObsPres.op_mem_max]; simp
    set ren : MvPowerSeries WB.σ O →ₐ[O] MvPowerSeries W.σ O := MvPowerSeries.rename fun s => e (.inl s) with hren
    set N : Ideal (MvPowerSeries W.σ O) := (RingHom.ker WB.π).map ren ⊔ maximalIdeal _ * RingHom.ker W.π with hNdef
    have hrp : ∀ j, ∀ x ∈ wtPart O WB.wt j, ren x ∈ wtPart O W.wt j := fun j x hx => by
      obtain ⟨y, hy, hy'⟩ := map_part O X _ (WPres.free O WB.wt) (fun s => hX _ s) _ (WPres.free O W.wt)
        (fun s => hX _ s) ren (fun (s : WB.σ) => ⟨MvPowerSeries.X (e (.inl s)),
          (show _ ∈ wtPart O W.wt (WB.wt s) from q1 s ▸ X_mem_wtPart O W.wt (e (.inl s))),
          (show MvPowerSeries.X (e (.inl s)) = ren (MvPowerSeries.X s) by rw [hren, rename_X])⟩) j x ⟨x, hx, rfl⟩
      have : y = ren x := hy'
      exact this ▸ hy
    have hNh : IsHomog O W.wt N := by
      obtain ⟨n, a, c, ha, ha'⟩ := ker_gen O X _ WB.wt _ WB.homog
      obtain ⟨n', a', c', hb, hb'⟩ := ker_gen O X _ W.wt _ W.homog
      refine lp_homog_sup _ _ _ ?_ ?_
      · rw [ha', Ideal.map_span, ← Set.range_comp, ← Ideal.top_mul (Ideal.span _)]
        exact lp_homog_mul _ _ (fun _ _ _ => Submodule.mem_top) _ c fun u => hrp _ _ (ha u)
      · rw [hb']
        exact lp_homog_mul _ _ (lp_homog_max _) _ c' hb
    have hNK : N ≤ RingHom.ker W.π := sup_le (q4 ▸ le_sup_left) Ideal.mul_le_right
    let π : MvPowerSeries W.σ O →ₐ[O] MvPowerSeries W.σ O ⧸ N := Ideal.Quotient.mkₐ O N
    have hπ : Function.Surjective π := Ideal.Quotient.mk_surjective
    have hπ0 : ∀ x, π x = 0 ↔ x ∈ N := fun x => Ideal.Quotient.eq_zero_iff_mem
    let p : (MvPowerSeries W.σ O ⧸ N) →ₐ[O] R := Ideal.Quotient.liftₐ N W.π hNK
    have hpπ : ∀ x, p (π x) = W.π x := fun x => rfl
    haveI : Nontrivial (MvPowerSeries W.σ O ⧸ N) := p.toRingHom.domain_nontrivial
    haveI : IsCO O (MvPowerSeries W.σ O ⧸ N) := co_quot O _ _ π hπ
    let WA : WPres O X (MvPowerSeries W.σ O ⧸ N) :=
      { σ := W.σ, wt := W.wt, π := π, surj := hπ
        homog := fun x hx j => (hπ0 _).2 (hNh x ((hπ0 _).1 hx) j) }
    let iA : B →ₐ[O] (MvPowerSeries W.σ O ⧸ N) := AlgHom.liftOfSurjective WB.π WB.surj (π.comp ren) fun x hx =>
      (hπ0 _).2 (Ideal.mem_sup_left (Ideal.mem_map_of_mem ren hx))
    have hiA : ∀ x, iA (WB.π x) = π (ren x) := fun x => AlgHom.liftOfSurjective_apply _ _ _ _ x
    have hpi : p.comp iA = i := AlgHom.ext fun x => by
      obtain ⟨x, rfl⟩ := WB.surj x
      rw [AlgHom.comp_apply, hiA, hpπ, q2]
    have hp : Function.Surjective p := fun x => by
      obtain ⟨y, rfl⟩ := W.surj x
      exact ⟨π y, rfl⟩
    have hm : maximalIdeal _ * RingHom.ker p = ⊥ := by
      rw [eq_bot_iff, Ideal.mul_le]
      intro x hx y hy
      obtain ⟨x, rfl⟩ := hπ x
      obtain ⟨y, rfl⟩ := hπ y
      rw [Ideal.mem_bot, ← map_mul, hπ0]
      exact Ideal.mem_sup_right (Ideal.mul_mem_mul ((UpperTheory.V.Alg.ObsPres.op_loc π x).1 hx) hy)
    have hε0 : ∀ u, p (π (f u)) = 0 := fun u => by
      have : f u ∈ RingHom.ker W.π := q4 ▸ Ideal.mem_sup_right (Ideal.subset_span ⟨u, rfl⟩)
      exact this
    have hkp : RingHom.ker p = Ideal.span (Set.range fun u => π (f u)) := by
      refine le_antisymm (fun y hy => ?_) (Ideal.span_le.2 (by rintro _ ⟨u, rfl⟩; exact hε0 u))
      obtain ⟨y, rfl⟩ := hπ y
      have hy' : y ∈ RingHom.ker W.π := hy
      rw [q4] at hy'
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy'
      rw [map_add (f := _), (hπ0 a).2 (Ideal.mem_sup_left ha), zero_add]
      obtain ⟨d, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 hb

      rw [map_sum]
      refine Ideal.sum_mem _ fun u _ => ?_
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨u, rfl⟩)
    have hind : ∀ c : κ → O, ∑ u, c u • π (f u) = 0 → ∀ u, c u ∈ maximalIdeal O := fun c hc => by
      refine p3 c ((hπ0 _).1 ?_)

      rw [map_sum]
      simpa only [map_smul] using hc
    have hpart : ∀ j, ∀ x ∈ W₀.part j, x ∈ (WA.part j).map p.toLinearMap := fun j x hx => by
      rw [← p2] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨π y, ⟨y, hy, rfl⟩, rfl⟩
    have hker : RingHom.ker p ≤ (maximalIdeal B).map iA ⊔ maximalIdeal _ ^ 2 := by
      refine UpperTheory.V.Alg.ObsPres.op_ker e iA p π hπ (fun s => ⟨WB.z s, hWB s, ?_⟩) fun c hc => t3 c ?_
      · rw [WPres.z, hiA, rename_X]
      · rw [hpi] at hc
        have : ∀ t, p (π (MvPowerSeries.X (e (.inr t)))) = z t := fun t => (p1 t).1
        simpa only [this] using hc
    obtain ⟨o, ho⟩ := obs_class O ι X w Φ h2 Γ rbar r0 hbar h0 F L hN hL hL0 B ρ hρ _ R p hp hm WA
      (fun s => (UpperTheory.V.Alg.ObsPres.op_loc π _).2 (hX _ s)) κ (fun u => π (f u)) wf (fun u => ⟨f u, q3 u, rfl⟩) hkp hind iA r α
      (hpi ▸ hU.1) (fun v s a b => by
        obtain ⟨y, hy, hy'⟩ := hρw v s a b
        have hy'' : WB.π y = (ρ v).hom s a b := hy'
        rw [← hy'', hiA]
        exact ⟨_, hrp _ _ hy, rfl⟩)
      (fun s a b => hpart _ _ (g3 s a b)) (fun v a b => hpart _ _ (g4 v a b))
    intro j
    haveI := hfin j
    have hli : LinearIndependent (ResidueField O) (o j) := by
      rw [Fintype.linearIndependent_iff]
      intro cb hcb
      choose c hc using fun u => residue_surjective (cb u)
      have h3 := UpperTheory.V.Alg.ObsPres.op_detect iA p hm hker (fun u => π (f u)) hε0 hind
        (fun u => if h : wf u = j then c ⟨u, h⟩ else 0) (by
          intro A' _ _ _ p' p'' η k1 k2 k3 k4 k5
          obtain ⟨r', α', m1, m2, m3⟩ := ho j c (by simpa only [hc] using hcb) A' p' p'' η k1 k2 k3 k4
            (fun u => by rw [k5, dite_eq_left u.2]) (fun u hu => by rw [k5, dite_eq_right hu, zero_smul])
          obtain ⟨s, ⟨s1, s2, s3⟩, -⟩ := hU.2 A' _ r' α' m1
          refine ⟨s, ?_, by rw [hpi, s1]⟩
          refine (hU.2 R i r α hU.1).unique ⟨?_, ?_, fun v => ?_⟩ ⟨rfl, rfl, fun v => rfl⟩
          · rw [AlgHom.comp_assoc, s1, ← AlgHom.comp_assoc, k2, hpi]
          · rw [← s2] at m2; exact m2
          · have m4 := m3 v
            rw [← s3 v] at m4; exact m4)
      intro u
      have h4 := h3 u
      rw [dite_eq_left u.2] at h4
      rw [← hc, residue_eq_zero_iff]
      exact h4
    rw [Nat.card_eq_fintype_card]
    exact hli.fintype_card_le_finrank
  obtain ⟨κ', _, wf', hpad⟩ := lp_pad wf (fun j => Module.finrank (ResidueField O) (F.Ob (FormData.adRep hbar j)))
    (Finset.univ.image fun x : ι × ι => w x.1 - w x.2)
    (fun j hj => lp_ob_zero Φ hbar F j fun a b h => hj (Finset.mem_image.2 ⟨(a, b), Finset.mem_univ _, h⟩)) bound
  refine ⟨R, _, _, inferInstance, i, r, α, W, τ, κ ⊕ κ', inferInstance, inferInstance, e, Sum.elim f fun _ => 0,
    Sum.elim wf wf', hU, ⟨q1, q2, ?_, ?_⟩, fun s a b => p2 _ ▸ g3 s a b, fun v a b => p2 _ ▸ g4 v a b, fun t => ?_,
    fun j => ?_, hpad⟩
  · rintro (u | u)
    · exact q3 u
    · exact zero_mem _
  · rw [q4]
    congr 1
    refine le_antisymm (Ideal.span_mono ?_) (Ideal.span_le.2 ?_)
    · rintro _ ⟨u, rfl⟩
      exact ⟨.inl u, rfl⟩
    · rintro _ ⟨u | u, rfl⟩
      · exact Ideal.subset_span ⟨u, rfl⟩
      · exact zero_mem _
  · rw [(p1 t).1, (p1 t).2]
    exact t1 t
  · simp only [(p1 _).2]
    exact t4 j
end -- clump:auto
end -- clump:auto
-- ===== end clump member: Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LemmaP =====
