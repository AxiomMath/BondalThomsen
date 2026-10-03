module

public import BondalThomsen.Ports.TauCeti.Algebra.Module.Primitive

@[expose] public section

namespace TauCeti

variable {Lattice : Type*} [AddCommGroup Lattice] [Module ℤ Lattice]

def slopeSetoid (Lattice : Type*) [AddCommGroup Lattice] [Module ℤ Lattice] :
    Setoid {vector : Lattice // IsPrimitive vector} where
  r first second := first.val = second.val ∨ first.val = -second.val
  iseqv :=
    { refl := fun _ => Or.inl rfl
      symm := fun equality => equality.imp Eq.symm fun same => by rw [same, neg_neg]
      trans := fun first second => by
        rcases first with first | first <;> rcases second with second | second
        · exact Or.inl (first.trans second)
        · exact Or.inr (first.trans second)
        · exact Or.inr (by rw [first, second])
        · exact Or.inl (by rw [first, second, neg_neg]) }

def Slope (Lattice : Type*) [AddCommGroup Lattice] [Module ℤ Lattice] : Type _ :=
  Quotient (slopeSetoid Lattice)

namespace Slope

def mk (vector : Lattice) (primitive : IsPrimitive vector) : Slope Lattice :=
  Quotient.mk (slopeSetoid Lattice) ⟨vector, primitive⟩

theorem mk_eq_mk {first second : Lattice} (first_primitive : IsPrimitive first)
    (second_primitive : IsPrimitive second) (same : first = second ∨ first = -second) :
    mk first first_primitive = mk second second_primitive := Quotient.sound same

@[simp] theorem mk_eq_mk_iff {first second : Lattice} (first_primitive : IsPrimitive first)
    (second_primitive : IsPrimitive second) :
    mk first first_primitive = mk second second_primitive ↔ first = second ∨ first = -second :=
  ⟨Quotient.exact, mk_eq_mk first_primitive second_primitive⟩

@[elab_as_elim] theorem induction_on {predicate : Slope Lattice → Prop}
    (direction : Slope Lattice)
    (representatives : ∀ vector primitive, predicate (mk vector primitive)) :
    predicate direction := Quotient.inductionOn direction fun vector =>
      representatives vector.val vector.property

end Slope
end TauCeti
