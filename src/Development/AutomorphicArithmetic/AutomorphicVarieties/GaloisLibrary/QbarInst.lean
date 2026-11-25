module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.SimpleRing.Principal

@[expose] public section

namespace UpperTheory.V.QbarInst

theorem charZero : CharZero (AlgebraicClosure ℚ) := inferInstance

theorem torsionFree : Module.IsTorsionFree ℚ (AlgebraicClosure ℚ) := inferInstance

theorem algClosure : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ

end UpperTheory.V.QbarInst
