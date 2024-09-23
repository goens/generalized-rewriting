variable (p q : Prop)

instance instEquivalenceIff : Equivalence Iff where
  refl := Iff.refl
  symm := Iff.symm
  trans := Iff.trans


instance instSetoidProp : Setoid Prop where
  r := Iff
  iseqv := instEquivalenceIff


def PropE : Type _ := Quotient instSetoidProp

namespace PropE

instance : Coe Prop PropE where
  coe p := Quotient.mk instSetoidProp p

private def and' : Prop → Prop → PropE
 | p, q => ↑(And p q)

theorem and'_congr : ∀ (a b c d : Prop),
  (a ↔ c) → (b ↔ d) → and' a b = and' c d := by
  intro a b c d hac hbd
  apply Quotient.sound
  exact and_congr hac hbd

def and : PropE → PropE → PropE :=
  Quotient.lift₂ and' and'_congr

private def or' : Prop → Prop → PropE
 | p, q => ↑(Or p q)

theorem or'_congr : ∀ (a b c d : Prop),
  (a ↔ c) → (b ↔ d) → or' a b = or' c d := by
  intro a b c d hac hbd
  apply Quotient.sound
  exact or_congr hac hbd

def or : PropE → PropE → PropE :=
  Quotient.lift₂ or' or'_congr

end PropE

theorem test (h : a ↔ b) : c ∧ (a ∨ b) → a := by
  rw [h, or_self]
  intro ⟨_,h₂⟩; assumption

#print test
#check iff_iff_eq
