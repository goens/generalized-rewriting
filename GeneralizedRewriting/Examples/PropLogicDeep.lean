inductive PropE
  | atom : String → PropE
  | and : PropE → PropE → PropE
  | or : PropE → PropE → PropE
  | not : PropE → PropE

def Context : Type _ := String → Prop

namespace PropE

def sem (Γ : Context) : PropE → Prop
  | atom id => Γ id
  | and e₁ e₂ => And (e₁.sem Γ) (e₂.sem Γ)
  | or e₁ e₂ => Or (e₁.sem Γ) (e₂.sem Γ)
  | not e => Not (e.sem Γ)

variable (Γ : Context)

def equiv : PropE → PropE → Prop
  | p, q => p.sem Γ = q.sem Γ

theorem equiv_refl (p : PropE) : equiv Γ p p := by
  simp [equiv]

theorem equiv_symm {p q : PropE} : equiv Γ p q → equiv Γ q p := by
  simp_all [equiv, sem]

theorem equiv_trans {p q r : PropE} :
  equiv Γ p q → equiv Γ q r → equiv Γ p r := by
  simp_all [equiv, sem]

instance equivalence : Equivalence (equiv Γ) where
  refl := equiv_refl Γ
  symm := equiv_symm Γ
  trans := equiv_trans Γ

instance setoid : Setoid PropE where
  r := equiv Γ
  iseqv := equivalence Γ

end PropE

variable (Γ : Context)

def PropEq : Type _ := Quotient (PropE.setoid Γ)

namespace PropEq

instance : Coe PropE (PropEq Γ) where
  coe p := Quotient.mk (PropE.setoid Γ) p

private def and' : PropE → PropE → PropEq Γ
  | p, q => ↑(PropE.and p q)

theorem and_congr {a b c d : PropE} (h₁ : PropE.setoid Γ |>.r a c) (h₂ : PropE.setoid Γ |>.r b d) :
   PropE.setoid Γ |>.r (PropE.and a b) (.and c d) := by
    simp_all [Setoid.r, PropE.equiv, PropE.sem]

theorem and'_congr {a b c d : PropE} (h₁ : PropE.setoid Γ |>.r a c) (h₂ : PropE.setoid Γ |>.r b d) :
  and' Γ a b = and' Γ c d := by
    apply Quotient.sound
    exact and_congr Γ h₁ h₂

def and : PropEq Γ → PropEq Γ → PropEq Γ :=
  Quotient.lift₂ (and' Γ) (@and'_congr Γ)

theorem and_eq_propand {a₁ a₂ b₁ b₂ : PropE} (ha: PropE.setoid Γ |>.r a₁ a₂) (hb: PropE.setoid Γ |>.r b₁ b₂) :
  and Γ a₁ b₁ = and Γ a₂ b₂ := by
  simp_all [and, Quotient.lift₂, Quotient.lift, PropEq.and']
  unfold Quotient.mk
  simp [Quot.liftBeta (PropEq.and' Γ a₁) _]
  simp [PropEq.and']
  apply Quotient.sound
  apply and_congr Γ ha hb

theorem and_eq' {a b : PropE} : and Γ a b = ↑(PropE.and a b) := by
  simp_all [and, Quotient.lift₂, Quotient.lift, PropEq.and']
  unfold Quotient.mk
  simp [Quot.liftBeta (PropEq.and' Γ a) _]
  simp [PropEq.and', Quotient.mk]

theorem and'_self (p : PropE) : PropE.setoid Γ |>.r (.and p p) p := by
  simp [Setoid.r, PropE.equiv, PropE.sem]

theorem and_self (p : PropEq Γ) : and Γ p p = p := by
  have ⟨p',hp'⟩ := Quotient.exists_rep p
  rw [← hp']
  rw [and_eq' Γ]
  apply Quotient.sound
  exact and'_self Γ p'

private def or' : PropE → PropE → PropEq Γ
  | p, q => ↑(PropE.or p q)

theorem or_congr {a b c d : PropE} (h₁ : PropE.setoid Γ |>.r a c) (h₂ : PropE.setoid Γ |>.r b d) :
   PropE.setoid Γ |>.r (PropE.or a b) (.or c d) := by
    simp_all [Setoid.r, PropE.equiv, PropE.sem]

theorem or'_congr {a b c d : PropE} (h₁ : PropE.setoid Γ |>.r a c) (h₂ : PropE.setoid Γ |>.r b d) :
  or' Γ a b = or' Γ c d := by
    apply Quotient.sound
    exact or_congr Γ h₁ h₂

def or : PropEq Γ → PropEq Γ → PropEq Γ :=
  Quotient.lift₂ (or' Γ) (@or'_congr Γ)

theorem or_eq' {a b : PropE} : or Γ a b = ↑(PropE.or a b) := by
  simp_all [or, Quotient.lift₂, Quotient.lift, PropEq.or']
  unfold Quotient.mk
  simp [Quot.liftBeta (PropEq.or' Γ a) _]
  simp [PropEq.or', Quotient.mk]

theorem or'_self (p : PropE) : PropE.setoid Γ |>.r (.or p p) p := by
  simp [Setoid.r, PropE.equiv, PropE.sem]

theorem or_self (p : PropEq Γ) : or Γ p p = p := by
  have ⟨p',hp'⟩ := Quotient.exists_rep p
  rw [← hp']
  rw [or_eq' Γ]
  apply Quotient.sound
  exact or'_self Γ p'

end PropEq

variable (Γ : Context)

theorem test (hab : ↑(PropE.atom "a" : PropEq Γ) = ↑(PropE.atom "b" : PropEq Γ)) :
  ↑(PropEq.and Γ (PropE.atom "b") (PropE.or (PropE.atom "a") (PropE.atom "b"))) = ↑(PropE.atom "a" : PropEq Γ) := by
  rw [← PropEq.or_eq', ← hab, PropEq.or_self, PropEq.and_self]

theorem test' (hab : PropE.setoid Γ |>.r (PropE.atom "a") (PropE.atom "b")) :
  PropE.setoid Γ |>.r (PropE.and (PropE.atom "b") (PropE.or (PropE.atom "a") (PropE.atom "b"))) (PropE.atom "a") := by
  -- rw [hab] -- tactic 'rewrite' failed, did not find instance of the pattern in the target expression PropE.sem Γ (PropE.atom "a")
  apply Quotient.exact
  exact test Γ (Quotient.sound hab)

/-- This is what we ultimately want to have as statements, building the whole
   scaffolding around `setoid` to get these "automatically"
-/
theorem test'' (hab : PropE.equiv Γ (PropE.atom "a") (PropE.atom "b")) :
  PropE.equiv Γ (PropE.and (PropE.atom "b") (PropE.or (PropE.atom "a") (PropE.atom "b"))) (PropE.atom "a") := by
  apply test'
  simp [Setoid.r, hab]

#print test
#print test'
#print test''
