import Mathlib.Data.Quot

def EquivModN (n : Nat) : Nat → Nat → Prop
  | x, y => x % n = y % n

theorem EquivModN.refl {n : Nat}  : ∀ x : Nat, EquivModN n x x := by
  simp [EquivModN]

theorem EquivModN.symm {n : Nat}  : ∀ {x y : Nat}, EquivModN n x y → EquivModN n y x := by
  simp [EquivModN]
  intros x y h
  rw [h]

theorem EquivModN.trans {n : Nat} : ∀ {x y z : Nat}, EquivModN n x y → EquivModN n y z → EquivModN n x z := by
  simp [EquivModN]
  intros x y z h₁ h₂
  rw [h₁,h₂]

instance EquivModN.isEquiv {n : Nat} : Equivalence (EquivModN n) where
  refl := EquivModN.refl
  trans :=  EquivModN.trans
  symm :=  EquivModN.symm

instance  EquivModN.instSetoid {n : Nat} : Setoid Nat := ⟨EquivModN n, EquivModN.isEquiv⟩

theorem Nat.add_mod_div (m n : Nat) : m % n = m - n * (m / n)  := by
  rw [Nat.sub_eq_of_eq_add]
  calc m = n * (m / n) + m % n := by rw [Nat.div_add_mod]
       _ =   m % n + n * (m / n)  :=  by rw [Nat.add_comm]

theorem EquivModN.add_comm {n : Nat} (x y : Nat) : EquivModN n (x + y) (y + x) := by
  simp [EquivModN, Nat.add_comm]

theorem EquivModN.add_equiv {n : Nat} {x y z : Nat} : EquivModN n x y → EquivModN n (x + z) (y + z) := by
  simp [EquivModN]
  intros h
  simp [← Nat.mod_add_mod]
  rw [Nat.mod_mod, Nat.mod_mod, h]

theorem EquivModN.add_n_eq {n : Nat} (x : Nat) : EquivModN n (x + n) x := by
  simp [EquivModN]

theorem Nat.test1 (x y z : Nat) : (x + y + z) = (y + x + z) := by
  rw [Nat.add_comm x y]

theorem test1 {n : Nat} (x y z : Nat) : EquivModN n (x + y + z) (y + x + z) := by
  -- want something like `grw [EquivModN.add_comm x y]`
  have h := EquivModN.add_comm (n:=n) x y
  have h' : EquivModN n (x + y + z) _ := EquivModN.add_equiv h
  exact h'

theorem test2 {n : Nat} (x y : Nat) : EquivModN n (x + n + y) (x + y) := by
  -- want something like `grw [EquivModN.add_n_eq]`
  have h := EquivModN.add_n_eq (n:=n) x
  exact EquivModN.add_equiv h

#print test1
#print test2

abbrev ModN n := Quotient <| EquivModN.instSetoid (n := n)
abbrev ModN.mk {n : Nat} := Quotient.mk <| EquivModN.instSetoid (n := n)

def ModN.add_congr {n : Nat} :  ∀ {a₁ b₁ a₂ b₂ : Nat}, EquivModN n a₁ a₂ → EquivModN n b₁ b₂ → EquivModN n (a₁ + b₁) (a₂ + b₂) := by
  intro a₁ b₁ a₂ b₂ ha hb
  simp [EquivModN]
  rw [EquivModN.add_equiv ha (z := b₁), Nat.add_comm, EquivModN.add_equiv hb (z := a₂), Nat.add_comm]

def ModN.add {n : Nat} : ModN n → ModN n → ModN n
 | x, y => Quotient.map₂ Nat.add (fun _ _ hx _ _ hy => ModN.add_congr hx hy) x y
   (sa := EquivModN.instSetoid) (sb := EquivModN.instSetoid) (sc := EquivModN.instSetoid)

instance {n : Nat} : Add (ModN n) := ⟨ModN.add⟩

instance {n : Nat} : Coe Nat (ModN n) where
  coe x := Quotient.mk EquivModN.instSetoid x

--local notation a "≣" b  "(mod "n")" => Quotient.mk (EquivModN.instSetoid (n := n)) a = Quotient.mk EquivModN.instSetoid b
local notation a "≣" b  "(mod "n")" => Coe.coe (self := instCoeNatModN (n :=n)) a = Coe.coe (self := instCoeNatModN (n :=n)) b

theorem ModN.add_eq_add_mod_n {n : Nat} {x y : Nat} :
  ModN.add (n:=n) ⟦x⟧ ⟦y⟧ = ⟦x + y⟧ := rfl

theorem ModN.add_n_eq {n : Nat} (x : ModN n) : (x + n) = x := by
   simp [HAdd.hAdd, Add.add]
   rw [add_eq_add_mod_n, ModN.add_congr]



theorem test2_quot {n : Nat} (x y : ModN n) :
  (x + n + y) = x + y := by
  rw [ModN.add_n_eq x]


theorem test2_quot_lifted {n : Nat} (x y : Nat) :
  (x + n + y) ≣ x + y (mod n) := by
  simp [Coe.coe]
  apply Quotient.exact
  rw [test2_quot]
