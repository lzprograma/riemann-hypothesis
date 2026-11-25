module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ResidueCharMemLevelPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueFixedPointOfAdicContraction
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DecompositionGroupEquivLocalGaloisGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartGr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ChartSum
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Coprod
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.LiftGrading
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivCond
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.DvrFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DecEmb
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.PhiCond
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpChartL
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.SpChartP
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OnCompMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.OnCompSelf
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.TotallySplit
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
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Connected.Separation
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.PredMulSumPadicValNatFactorialAddCardLe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsInertiaInfiniteCyclotomic
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.ClosedOfSet

@[expose] public section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section Series

open MvPowerSeries

variable {O E σ τ : Type} [CommRing O] [CommRing E] [Algebra O E]

private theorem lb_ext [Finite σ] [Finite τ] (f g : MvPowerSeries σ O →ₐ[O] MvPowerSeries τ E)
    (h0 : ∀ s, constantCoeff (f (X s)) = 0) (h : ∀ s, f (X s) = g (X s)) : f = g := by
  refine AlgHom.ext fun p => MvPowerSeries.ext fun d => ?_
  have := GlobalTheory.algHom_sub_mem_pow f g (J := GlobalTheory.germIdeal τ E) h0 (fun s => h s ▸ h0 s)
    (n := d.degree + 1) (fun s => by simp [h s]) p
  have h2 := GlobalTheory.mem_germIdeal_pow_iff.1 this d (Nat.lt_succ_self _)
  rwa [map_sub, sub_eq_zero] at h2

private theorem lb_graded [Finite σ] [Finite τ] {G : Type} [AddCommGroup G] (w : σ → G) (w' : τ → G)
    (F : MvPowerSeries σ O →ₐ[O] MvPowerSeries τ E) (h0 : ∀ s, constantCoeff (F (X s)) = 0)
    (hw : ∀ s, F (X s) ∈ wtPart E w' (w s)) (j : G) (f : MvPowerSeries σ O) (hf : f ∈ wtPart O w j) :
    F f ∈ wtPart E w' j := by
  classical
  have ha : HasSubst fun s => F (X s) := hasSubst_of_constantCoeff_zero h0
  rw [lb_ext F (substAlgHom ha) h0 fun s => (substAlgHom_X ha s).symm]
  intro n hn
  rw [coe_substAlgHom, coeff_subst ha]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  by_cases hd : Finsupp.weight w d = j
  · have : (d.prod fun s k => F (X s) ^ k) ∈ wtPart E w' j := by
      rw [← hd, Finsupp.weight_apply, Finsupp.sum]
      exact SetLike.prod_pow_mem_graded (wtPart E w') w (fun s => F (X s)) d (fun s _ => hw s)
    rw [this n hn, smul_zero]
  · rw [hf d hd, zero_smul]

private theorem lb_const [Finite σ] (x : MvPowerSeries σ O →ₐ[O] O) (h0 : ∀ s, x (X s) = 0) (f : MvPowerSeries σ O) :
    x f = constantCoeff f :=
  sub_eq_zero.1 (Ideal.mem_bot.1
    (GlobalTheory.algHom_sub_constantCoeff_mem x (K := ⊥) (fun s => Ideal.mem_bot.2 (h0 s)) f))

private theorem lb_max {K : Type} [Field K] : maximalIdeal (MvPowerSeries τ K) = GlobalTheory.germIdeal τ K := by
  ext f
  rw [mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff, isUnit_iff_ne_zero, not_not]
  rfl

private theorem lb_chart [IsDomain O] [Finite τ] {R Y : Type} [CommRing R] [Algebra O R] [AddCommGroup Y]
    (W : WPres O Y R) (x : R →ₐ[O] O) (hz : ∀ s, x (W.z s) = 0) (P : Ideal R) (u : τ → Y)
    (φ : R →ₐ[O] MvPowerSeries τ (FractionRing O)) (hφ : Loc.IsCompl P x φ) (hy : ∃ y, x y ≠ 0 ∧ ∀ a ∈ P, y * a = 0)
    (hw : ∀ s, φ (W.z s) ∈ wtPart (FractionRing O) u (W.wt s)) :
    ∃ h : W.HasOrigin, W.origin h = x ∧ IsChart W.part x u φ := by
  classical
  have hc : ∀ f, x (W.π f) = constantCoeff f := lb_const (x.comp W.π) hz
  have h : W.HasOrigin := fun f hf => by rw [← hc, hf, map_zero]
  refine ⟨h, AlgHom.ext fun a => ?_, ?_, hφ.const, fun i => ?_, fun f hf hl => ?_⟩
  · obtain ⟨f, rfl⟩ := W.surj a
    rw [W.origin_π, hc]
  · rintro j _ ⟨f, hf, rfl⟩
    exact lb_graded W.wt u (φ.comp W.π) (fun s => (hφ.const (W.z s)).trans (by rw [hz, map_zero])) hw j f hf
  · obtain ⟨a, c, hc0, ha⟩ := hφ.dense 2 (X i)
    rw [lb_max] at ha
    have key : ∀ i', coeff (Finsupp.single i' 1) (φ a) = c • (if i' = i then 1 else 0 : FractionRing O) := fun i' => by
      have := GlobalTheory.mem_germIdeal_pow_iff.1 ha (Finsupp.single i' 1) (by simp)
      rw [map_sub, sub_eq_zero] at this
      rw [← this, ← IsScalarTower.algebraMap_smul (FractionRing O) c, map_smul, IsScalarTower.algebraMap_smul, coeff_X]
      simp [Finsupp.single_left_inj]
    refine ⟨a, ?_, fun i' hi => ?_⟩
    · rw [key, ite_eq_left rfl, Algebra.smul_def, mul_one]
      exact fun e => hc0 (IsFractionRing.injective O (FractionRing O) (by rw [e, map_zero]))
    · rw [key, ite_eq_right hi, smul_zero]
  · have h2 : φ f ∈ maximalIdeal (MvPowerSeries τ (FractionRing O)) ^ 2 := by
      rw [lb_max]
      refine GlobalTheory.mem_germIdeal_pow_iff.2 fun d hd => ?_
      obtain h0 | h1 : d.degree = 0 ∨ d.degree = 1 := by omega
      · rw [(Finsupp.degree_eq_zero_iff d).1 h0, coeff_zero_eq_constantCoeff_apply, hφ.const, hf, map_zero]
      · obtain ⟨i, rfl⟩ : ∃ i, d = Finsupp.single i 1 := by
          have : d ∈ Set.range fun i : τ => Finsupp.single i 1 := by
            rw [Finsupp.range_single_one]; exact h1
          obtain ⟨i, hi⟩ := this
          exact ⟨i, hi.symm⟩
        exact hl i
    obtain ⟨c, hc0, hcf⟩ := hφ.inj 2 f h2
    obtain ⟨a, ha, p, hp, e⟩ := Submodule.mem_sup.1 hcf
    obtain ⟨y, hy0, hy⟩ := hy
    have hxp : x p = 0 := by
      apply IsFractionRing.injective O (FractionRing O)
      have : φ p = 0 := by rw [← hφ.ker] at hp; exact hp
      rw [← hφ.const, this, map_zero, map_zero]
    refine ⟨x y * c, mul_ne_zero hy0 hc0, ?_⟩
    rw [mul_smul, ← e, smul_add]
    refine add_mem (Submodule.smul_of_tower_mem _ _ ha) ?_
    have : x y • p = (algebraMap O R (x y) - y) * p := by rw [sub_mul, hy p hp, sub_zero, Algebra.smul_def]
    rw [this, sq]
    exact Ideal.mul_mem_mul (by simp [RingHom.mem_ker]) hxp

end Series

section Abstract

variable {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]

private structure Pk {Γ : Type} [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* M4 (ResidueField O)} (P : Cond O rbar)
    (ρ₀ : Γ →* M4 O) (n : ℤ × ℤ → ℕ) where
  B : Type
  [cB : CommRing B]
  [aB : Algebra O B]
  [coB : IsCO O B]
  W : WPres O (ℤ × ℤ) B
  wt_mem : ∀ i, W.wt i ∈ wts
  org : W.HasOrigin
  z_mem : ∀ i, W.z i ∈ maximalIdeal B
  ρ : Lift O rbar B
  rep : Represents P ρ
  hom : ∀ g i j, ρ.hom g i j ∈ W.part (wt i j)
  at0 : ∀ g i j, W.origin org (ρ.hom g i j) = ρ₀ g i j
  τ : Type
  [fτ : Fintype τ]
  u : τ → ℤ × ℤ
  φ : B →ₐ[O] MvPowerSeries τ (FractionRing O)
  chart : IsChart W.part (W.origin org) u φ
  card : ∀ j, Nat.card {i // u i = j} = n j

attribute [local instance] Pk.cB Pk.aB Pk.coB Pk.fτ

private theorem pk_of {Γ : Type} [Group Γ] [TopologicalSpace Γ] {rbar : Γ →* M4 (ResidueField O)} (P : Cond O rbar)
    (ρ₀ : Γ →* M4 O) (h0 : ∀ g a b, a ≠ b → ρ₀ g a b = 0) (n : ℤ × ℤ → ℕ)
    (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ : Lift O rbar R) (hrep : Represents P ρ) (hst : ρ.TStable w4)
    (x : R →ₐ[O] O) (Q : Ideal R) {m : ℕ} (u : Fin m → ℤ × ℤ) (φ : R →ₐ[O] MvPowerSeries (Fin m) (FractionRing O))
    (hx : (ρ.map x).hom = ρ₀) (hφ : Loc.IsCompl Q x φ) (hy : ∃ y, x y ≠ 0 ∧ ∀ a ∈ Q, y * a = 0)
    (hu : ∀ j, Nat.card {i // u i = j} = n j) (hw : ∀ g a b, φ (ρ.hom g a b) ∈ wtPart (FractionRing O) u (wt a b)) :
    Nonempty (Pk P ρ₀ n) := by
  have hx' : ∀ g a b, x (ρ.hom g a b) = ρ₀ g a b := fun g a b => by rw [← hx]; rfl
  have hres : ∀ g a b, residue O (ρ₀ g a b) = rbar g a b := fun g a b => by
    rw [← (ρ.map x).red g a b, hx]
    exact ((res O O).commutes _).symm
  obtain ⟨W, hW1, hW2⟩ := lift_grading O (ℤ × ℤ) Γ (Fin 4) rbar w4 R ρ (fun g a b => ρ₀ g a b) hres
    (fun g a b h => h0 g a b fun e => h (congrArg w4 e))
    (fun R' _ _ _ f f' e => ((hrep R').2 _ ((hrep R').1 f')).unique e rfl) hst
  have hz : ∀ s, x (W.z s) = 0 := fun s => by
    obtain ⟨g, a, b, e, -⟩ := hW2 s
    rw [e, map_sub, hx', AlgHom.commutes]
    exact sub_self _
  obtain ⟨h, ho, hc⟩ := lb_chart W x hz Q u φ hφ hy fun s => by
    obtain ⟨g, a, b, e, e'⟩ := hW2 s
    rw [e, e', w4_sub_w4_eq_wt, map_sub]
    refine sub_mem (hw g a b) ?_
    by_cases hab : a = b
    · rw [(wt_eq_zero a b).2 hab, AlgHom.commutes, IsScalarTower.algebraMap_apply O (FractionRing O),
        Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ _ (one_mem_wtPart _ _)
    · rw [h0 g a b hab, map_zero, map_zero]
      exact zero_mem _
  refine ⟨{ B := R, W := W, wt_mem := fun s => ?_, org := h, z_mem := fun s => ?_, ρ := ρ, rep := hrep, hom := hW1
            at0 := fun g a b => by rw [ho, hx'], τ := Fin m, u := u, φ := φ, chart := ho ▸ hc, card := hu }⟩
  · obtain ⟨g, a, b, -, e'⟩ := hW2 s
    rw [e', w4_sub_w4_eq_wt]
    exact wt_mem a b
  · rw [← res_eq_zero_iff O, ← res_map x, hz, map_zero]

private theorem card_sigma {T Y : Type} [Fintype T] (τ : T → Type) [∀ v, Fintype (τ v)] (u : ∀ v, τ v → Y) (j : Y) :
    Nat.card {p : Σ v, τ v // u p.1 p.2 = j} = ∑ v, Nat.card {i // u v i = j} := by
  rw [← Nat.card_sigma]
  exact Nat.card_congr
    { toFun := fun p => ⟨p.1.1, p.1.2, p.2⟩
      invFun := fun p => ⟨⟨p.1, p.2.1⟩, p.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

private theorem pk_sum {T : Type} [Fintype T] {Γ : T → Type} [∀ v, Group (Γ v)] [∀ v, TopologicalSpace (Γ v)]
    {rbar : ∀ v, Γ v →* M4 (ResidueField O)} {P : ∀ v, Cond O (rbar v)} {ρ₀ : ∀ v, Γ v →* M4 O} {n : T → ℤ × ℤ → ℕ}
    (K : ∀ v, Pk (P v) (ρ₀ v) (n v)) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra O B) (_ : IsCO O B) (W : WPres O (ℤ × ℤ) B) (org : W.HasOrigin)
      (ρ : ∀ v, Lift O (rbar v) B), (∀ i, W.wt i ∈ wts) ∧ (∀ v, P v B (ρ v)) ∧
      (∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (ρ' : ∀ v, Lift O (rbar v) R), (∀ v, P v R (ρ' v)) →
        ∃! f : B →ₐ[O] R, ∀ v, (ρ v).map f = ρ' v) ∧
      (∀ v g i j, (ρ v).hom g i j ∈ W.part (wt i j)) ∧ (∀ v g i j, W.origin org ((ρ v).hom g i j) = ρ₀ v g i j) ∧
      SmoothPt W.gr ((W.origin org).comp W.A.val) fun j => ∑ v, n v j := by
  obtain ⟨B, i1, i2, i3, ι, W, e, hu, hz, hp, hk⟩ :=
    coprod O (ℤ × ℤ) T (fun v => (K v).B) (fun v => (K v).W) fun v => (K v).z_mem
  obtain ⟨org, ψ, hψ, -⟩ := chart_sum O (ℤ × ℤ) T (fun v => (K v).B) (fun v => (K v).W) (fun v => (K v).org)
    (fun v => (K v).τ) (fun v => (K v).u) (fun v => (K v).φ) (fun v => (K v).chart) B W e (fun v s => (hz v s).1) hk
  refine ⟨B, i1, i2, i3, W, org, fun v => (K v).ρ.map (ι v), fun i => ?_, fun v => ((K v).rep B).1 _,
    fun R _ _ _ ρ' h => ?_, fun v g i j => hp v _ _ ((K v).hom g i j), fun v g i j => ?_,
    (Σ v, (K v).τ), inferInstance, _, _, chart_gr O (ℤ × ℤ) B W org _ _ ψ hψ, fun j => ?_⟩
  · obtain ⟨⟨v, s⟩, rfl⟩ := e.surjective i
    rw [(hz v s).1]
    exact (K v).wt_mem s
  · choose f hf hf' using fun v => ((K v).rep R).2 (ρ' v) (h v)
    obtain ⟨F, hF, hF'⟩ := hu R f
    refine ⟨F, fun v => ?_, fun F' h' => hF' F' fun v => hf' v _ (h' v)⟩
    rw [← hf v, ← hF v]
    rfl
  · rw [← (K v).at0, Lift.map_hom]
    obtain ⟨f, hf⟩ := (K v).W.surj ((K v).ρ.hom g i j)
    rw [← hf, WPres.origin_π]
    refine lb_const (((W.origin org).comp (ι v)).comp (K v).W.π) (fun s => ?_) f
    show W.origin org (ι v ((K v).W.z s)) = 0
    rw [← (hz v s).2, WPres.z, WPres.origin_π, MvPowerSeries.constantCoeff_X]
  · refine (card_sigma (fun v => (K v).τ) (fun v => (K v).u) j).trans ?_
    exact Finset.sum_congr rfl fun v _ => (K v).card j

end Abstract

section Main

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime] {c : Coef l} (D : Raw Ω c)

private theorem pkL (hD : D.Good) (hP : Loc.LocalPublishedTheorems) : Nonempty (Pk D.condL (D.r0At l) dimL) := by
  obtain ⟨ρ₀, -, hpt⟩ := r0pt D hD
  obtain ⟨R, _, _, _, ρ, hrep⟩ := UpperTheory.V.Ws.Po.rep_ex D hD hP l hl.out _ (UpperTheory.V.Ws.Po.closedL D) _
    ((ptMap D hD c.O ρ₀).1 hpt).atL
  obtain ⟨_, _, _⟩ := UpperTheory.V.Ws.Po.frac_alg l c.O
  obtain ⟨x, P, w, φ, hx, hφ, hy, hu, hw⟩ := Loc.spChartL hP D hD (FractionRing c.O) R ρ hrep
  exact pk_of D.condL (D.r0At l)
    (fun g _ _ => Matrix.diagonal_apply_ne fun i => (D.ps i g : c.O)) _ R ρ hrep
    (UpperTheory.V.Ws.Po.tstable hrep fun _ _ _ _ r r' s _ _ hr h => UpperTheory.V.Ws.Po.torusL D r r' s hr h)
    x P w φ hx hφ hy hu hw

private theorem pkP (hD : D.Good) (hP : Loc.LocalPublishedTheorems) (p : ℕ) (hp : p ∈ D.Sb) :
    Nonempty (Pk (D.condP p) (D.r0At p) dimP) := by
  obtain ⟨ρ₀, -, hpt⟩ := r0pt D hD
  obtain ⟨R, _, _, _, ρ, hrep⟩ := UpperTheory.V.Ws.Po.rep_ex D hD hP p ((facts D hD).1 p hp).1 _
    (UpperTheory.V.Ws.Po.closedP D p) _ (((ptMap D hD c.O ρ₀).1 hpt).atP p hp)
  obtain ⟨_, _, _⟩ := UpperTheory.V.Ws.Po.frac_alg l c.O
  obtain ⟨x, P, w, φ, hx, hφ, hy, hu, hw⟩ := Loc.spChartP D hD p hp (FractionRing c.O) R ρ hrep
  exact pk_of (D.condP p) (D.r0At p)
    (fun g _ _ => Matrix.diagonal_apply_ne fun i => (D.ps i g : c.O)) _ R ρ hrep
    (UpperTheory.V.Ws.Po.tstable hrep fun _ _ _ _ r r' s _ _ hr h => UpperTheory.V.Ws.Po.torusP D p r r' s hr h)
    x P w φ hx hφ hy hu hw

end Main

theorem UpperTheory.V.GradeZeroInterpolatingElement.locBase :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → Loc.LocalPublishedTheorems → Nonempty (LocBase D) := by
  intro Ω _ _ _ l _ c D hD hP
  have hne : ∀ p ∈ D.Sb, p ≠ l := fun p hp => ((facts D hD).1 p hp).2.1
  let P : ∀ v : ℕ, Cond c.O (D.rbarAt v) := Function.update D.condP l D.condL
  let n : ℕ → ℤ × ℤ → ℕ := Function.update (fun _ => dimP) l dimL
  have hPl : P l = D.condL := Function.update_self ..
  have hPp : ∀ p ∈ D.Sb, P p = D.condP p := fun p hp => Function.update_of_ne (hne p hp) ..
  have hnl : n l = dimL := Function.update_self ..
  have hnp : ∀ p ∈ D.Sb, n p = dimP := fun p hp => Function.update_of_ne (hne p hp) ..
  have hK : ∀ v : D.T, Nonempty (Pk (P v) (D.r0At v) (n v)) := by
    rintro ⟨v, hv⟩
    obtain rfl | hv' := Finset.mem_insert.1 hv
    · show Nonempty (Pk (P v) _ (n v))
      rw [hPl, hnl]
      exact pkL D hD hP
    · show Nonempty (Pk (P v) _ (n v))
      rw [hPp v hv', hnp v hv']
      exact pkP D hD hP v hv'
  have hE : ∀ (R : Type) [CommRing R] [Algebra c.O R] [IsCO c.O R] (ρ : ∀ v : D.T, Lift c.O (D.rbarAt v) R),
      D.LocEqs ρ ↔ ∀ v : D.T, P v R (ρ v) := fun R _ _ _ ρ => by
    refine ⟨fun h ⟨v, hv⟩ => ?_, fun h => ⟨?_, fun p hp => ?_⟩⟩
    · obtain rfl | hv' := Finset.mem_insert.1 hv
      · show P v R _
        rw [hPl]
        exact h.1
      · show P v R _
        rw [hPp v hv']
        exact h.2 v hv'
    · have : P l R _ := h ⟨l, D.residueChar_mem_levelPrimes⟩
      rw [hPl] at this
      exact this
    · have : P p R _ := h ⟨p, D.mem_T hp⟩
      rw [hPp p hp] at this
      exact this
  obtain ⟨B, _, _, _, W, org, ρ, h1, h2, h3, h4, h5, h6⟩ := pk_sum fun v => (hK v).some
  refine ⟨{ B := B, W := W, wt_mem := h1, org := org, ρ := ρ, eqs := (hE B ρ).2 h2
            univ := fun R _ _ _ ρ' h => h3 R ρ' ((hE R ρ').1 h), hom := h4, at0 := h5, smooth := ?_ }⟩
  convert h6 using 2 with j
  rw [Finset.sum_coe_sort D.T fun v => n v j, Raw.T, Finset.sum_insert fun h => hne l h rfl, hnl,
    Finset.sum_congr rfl fun p hp => by rw [hnp p hp], Finset.sum_const, smul_eq_mul]
