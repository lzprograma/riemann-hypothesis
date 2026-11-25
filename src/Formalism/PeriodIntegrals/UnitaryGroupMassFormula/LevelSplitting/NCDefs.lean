module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.SemidirectExistsOfParts
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.ConjDefs
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelSplitting.MeasAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.TopoAF
import Mathlib.RingTheory.PiTensorProduct
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ClosedStep

section
@[expose] public section

noncomputable section

namespace PI.VolSemiDirect.W

open MeasureTheory

theorem product_haar_measure_holds : ProdHaarG := by
  intro X _ _ _ _ K N H hS hK hN hH hC μN hμN μH hμH
  obtain ⟨hnorm, e, he⟩ := hS
  obtain ⟨_, _, _, _⟩ := hK
  obtain ⟨_, _, _, _⟩ := hN
  obtain ⟨_, _, _, _⟩ := hH
  have hem : Measurable e := e.continuous.measurable
  have hPF : ProdF K N H ((μN.prod μH).map e) μN μH := by
    intro f hf
    have h1 : Measurable (fun k : K => f (k : X)) := hf.comp measurable_subtype_coe
    rw [lintegral_map h1 hem, lintegral_prod (fun p => f ((e p : K) : X)) (h1.comp hem).aemeasurable]
    simp only [he]
  refine ⟨(μN.prod μH).map e, ?_, hPF⟩
  have hLI : (Measure.map e (μN.prod μH)).IsMulLeftInvariant := by
    constructor
    intro k
    set p0 := e.symm k with hp0
    have hk : (k : X) = (p0.1 : X) * (p0.2 : X) := by
      rw [← he, hp0, Homeomorph.apply_symm_apply]
    let T : N × H → N × H := fun p => e.symm (k * e p)
    have hTc : Continuous T := e.symm.continuous.comp (continuous_const.mul e.continuous)
    have hTm : Measurable T := hTc.measurable
    let A : N → N := fun m => ⟨(p0.1 : X) * ((p0.2 : X) * (m : X) * (p0.2 : X)⁻¹),
      N.mul_mem p0.1.2 (hnorm _ p0.2.2 _ m.2)⟩
    let C : N → N := fun m => ⟨(p0.2 : X) * (m : X) * (p0.2 : X)⁻¹, hnorm _ p0.2.2 _ m.2⟩
    have hT : ∀ p : N × H, T p = (A p.1, p0.2 * p.2) := by
      intro p
      apply e.injective
      simp only [T, Homeomorph.apply_symm_apply]
      apply Subtype.ext
      rw [Subgroup.coe_mul, he, he, hk]
      simp only [A, Subgroup.coe_mul]
      group
    have hTAB : T = Prod.map A (fun h => p0.2 * h) := funext fun p => hT p
    have hAm : Measurable A := by
      have hA1 : A = fun m => (T (m, 1)).1 := funext fun m => by rw [hT]
      rw [hA1]
      first
        | exact (continuous_fst.comp (hTc.comp (continuous_id.prodMk continuous_const))).measurable
    have hCA : C = fun m => p0.1⁻¹ * A m := funext fun m => Subtype.ext (by
      simp only [A, C, Subgroup.coe_mul, Subgroup.coe_inv]
      group)
    have hCm : Measurable C := by
      rw [hCA]
      exact (measurable_const_mul _).comp hAm
    have hCinv : Measure.map C μN = μN := by
      ext S hS
      rw [Measure.map_apply hCm hS]
      obtain ⟨B, hB, rfl⟩ := hS
      have key := hC μN hμN (p0.2 : X) p0.2.2 (B.indicator 1) (measurable_one.indicator hB)
      have e1 : ∫⁻ n, B.indicator 1 ((p0.2 : X) * (n : X) * (p0.2 : X)⁻¹) ∂μN =
          μN (C ⁻¹' (Subtype.val ⁻¹' B)) := by
        rw [← lintegral_indicator_one (hCm (measurable_subtype_coe hB))]
        first
          | rfl
      have e2 : ∫⁻ n, B.indicator 1 (n : X) ∂μN = μN (Subtype.val ⁻¹' B) := by
        rw [← lintegral_indicator_one (measurable_subtype_coe hB)]
        first
          | rfl
      rw [← e1, key, e2]
    have hA : Measure.map A μN = μN := by
      have hAC : A = (fun m => p0.1 * m) ∘ C :=
        funext fun m => Subtype.ext (by simp only [A, C, Function.comp_apply, Subgroup.coe_mul])
      rw [hAC, ← Measure.map_map (measurable_const_mul _) hCm, hCinv, map_mul_left_eq_self]
    have hB : Measure.map (fun h : H => p0.2 * h) μH = μH := map_mul_left_eq_self μH p0.2
    calc Measure.map (k * ·) (Measure.map e (μN.prod μH))
        = Measure.map ((k * ·) ∘ e) (μN.prod μH) := by
          rw [Measure.map_map (measurable_const_mul k) hem]
      _ = Measure.map (e ∘ T) (μN.prod μH) := by
          congr 1
          funext p
          simp [T]
      _ = Measure.map e (Measure.map T (μN.prod μH)) := by rw [Measure.map_map hem hTm]
      _ = Measure.map e (μN.prod μH) := by
          rw [hTAB, ← Measure.map_prod_map _ _ hAm (measurable_const_mul _), hA, hB]
  have hFC : IsFiniteMeasureOnCompacts (Measure.map e (μN.prod μH)) := by
    constructor
    intro C hCc
    rw [Measure.map_apply hem hCc.measurableSet]
    exact (e.isCompact_preimage.mpr hCc).measure_lt_top
  have hOP : (Measure.map e (μN.prod μH)).IsOpenPosMeasure := by
    constructor
    intro U hU hne
    rw [Measure.map_apply hem hU.measurableSet]
    exact (hU.preimage e.continuous).measure_ne_zero _ (hne.preimage e.surjective)
  exact ⟨⟩

end PI.VolSemiDirect.W
end


@[expose] public section

noncomputable section

namespace PI.LevelKSplit.W.NC

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub NumberField IsDedekindDomain MeasureTheory PI.LevelKSplit
open PI.LevelKSplit.W.ExS PI.LevelKSplit.W.CD
open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {r : ℕ} (P : Frame E M r)

theorem hR_add_right {r0 : ℕ} (P0 : Frame E M r0) (u x y : Fin M → R ⊗[F] E) : hR R σ J u (x + y) = hR R σ J u x + hR R σ J u y := by
  simp [hR, Formalism.UG.hform, mul_add, Finset.sum_add_distrib]

theorem hR_neg_right {r0 : ℕ} (P0 : Frame E M r0) (u x : Fin M → R ⊗[F] E) : hR R σ J u (-x) = -hR R σ J u x := by
  simp [hR, Formalism.UG.hform, mul_neg, Finset.sum_neg_distrib]

def Wp : AddSubgroup (Fin M → R ⊗[F] E) where
  carrier := {w | (∀ a, hR R σ J (ratV (F := F) R (P.e a)) w = 0) ∧
    (∀ a, hR R σ J (ratV (F := F) R (P.f a)) w = 0)}
  zero_mem' := by
    refine ⟨fun a => ?_, fun a => ?_⟩ <;> simp [hR, Formalism.UG.hform]
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    refine ⟨fun a => ?_, fun a => ?_⟩
    · rw [hR_add_right R σ J P, hx1, hy1, add_zero]
    · rw [hR_add_right R σ J P, hx2, hy2, add_zero]
  neg_mem' := by
    rintro x ⟨hx1, hx2⟩
    refine ⟨fun a => ?_, fun a => ?_⟩
    · rw [hR_neg_right R σ J P, hx1, neg_zero]
    · rw [hR_neg_right R σ J P, hx2, neg_zero]

def pWp (x : Fin M → R ⊗[F] E) : Fin M → R ⊗[F] E :=
  x - ∑ a, hR R σ J (ratV (F := F) R (P.f a)) x • ratV (F := F) R (P.e a)
    - ∑ a, hR R σ J (ratV (F := F) R (P.e a)) x • ratV (F := F) R (P.f a)

def yH (g : HA R σ J) : Fin r → Fin M → R ⊗[F] E :=
  fun a => pWp R σ J P (lin R σ J g (ratV (F := F) R (P.f a)))

def FixXp : Subgroup (HA R σ J) where
  carrier := {g | ∀ v, InXperp R σ J P v → lin R σ J g v = v}
  one_mem' := fun v _ => lin_one R σ J v
  mul_mem' := by
    intro g h hg hh v hv
    simp only [Set.mem_ofPred_eq] at *
    rw [lin_mul, hh v hv, hg v hv]
  inv_mem' := by
    intro g hg v hv
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← hg v hv]
    exact lin_inv_lin R σ J g v

def LevelUnipotentSubgroup : Subgroup (HA R σ J) := Nsub R σ J P ⊓ stabT R σ J P.e

def Zsub : Subgroup (HA R σ J) := Nsub R σ J P ⊓ FixXp R σ J P

end Gen

section Ext

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
  (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)

def NCoord : Prop :=
  IsHermND σ J → (∀ x, σ (σ x) = x) → ∀ (r : ℕ) (P : Frame E M r) (T : F), P.IsStd σ J T →
  ∃ (A Z : Subgroup (HA (Af F) σ J))
    (Ψ : (A × ((Fin r → Wp (Af F) σ J P) × Z)) ≃ₜ Nsub (Af F) σ J P),
    IsClosed (A : Set (HA (Af F) σ J)) ∧ IsClosed (Z : Set (HA (Af F) σ J)) ∧
    (∀ n0 : Nsub (Af F) σ J P, ∃ (a0 : A) (t : A → (Fin r → Wp (Af F) σ J P))
      (c : A × (Fin r → Wp (Af F) σ J P) → Z),
      Continuous t ∧ Continuous c ∧ ∀ u y z, n0 * Ψ (u, y, z) = Ψ (a0 * u, y + t u, c (u, y) * z)) ∧
    ∀ h ∈ Hsub (Af F) σ J P, ∀ u y z, ∃ y' : Fin r → Wp (Af F) σ J P,
      (∀ a, (y' a : Fin M → Af F ⊗[F] E) = lin (Af F) σ J h (y a)) ∧
      h * (Ψ (u, y, z) : HA (Af F) σ J) * h⁻¹ = (Ψ (u, y', z) : HA (Af F) σ J)

def NCAsm : Prop := NCoord F E σ M J → ModV F E σ M J → ConjNH F E σ M J

end Ext

def NCoordAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => NCoord F E σ M J
def NCAsmAll : Prop := ForAllCM fun F E _ _ _ _ σ M J => NCAsm F E σ M J

theorem conjNHAll_of (hC : NCoordAll) (hV : ModVAll) (hA : NCAsmAll) : ConjNHAll := by
  intro F E _ _ _ _ _ σ hCM M J hJ
  exact hA F E σ hCM M J hJ (hC F E σ hCM M J hJ) (hV F E σ hCM M J hJ)

theorem levelSAll_of_parts (hS : SemiNHSAll) (hC : NCoordAll) (hV : ModVAll) (hA : NCAsmAll) :
    PI.LevelKSplit.LevelSAll :=
  PI.LevelKSplit.W.MeasAll.levelSAll_of_exist
    (PI.LevelKSplit.W.ExS.existSAll_of PI.VolSemiDirect.W.product_haar_measure_holds (fun _ _ _ => inferInstance) hS
      (conjNHAll_of hC hV hA))

end PI.LevelKSplit.W.NC
