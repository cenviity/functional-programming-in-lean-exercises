module

section Exercise_1_6_5_1

def List.last? : List α → Option α
  | [] => none
  | [x] => x
  | _ :: xs => last? xs

#guard ([] : List Int).last?.isNone
#guard [1].last?.isSome
#guard [1, 2, 3].last?.isSome

theorem List.last?_eq_getLast? (xs : List α) : xs.last? = xs.getLast? := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    cases tail with
    | nil => rfl
    | cons head' tail' => simp only [last?, getLast?, getLast, ih]

end Exercise_1_6_5_1

section Exercise_1_6_5_2

def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  | [] => none
  | x :: xs' =>
    if predicate x then
      some x
    else xs'.findFirst? predicate

#guard [].findFirst? Char.isAlpha |>.isNone
#guard ['c', '1'].findFirst? Char.isAlpha == some 'c'
#guard ['1', 'd'].findFirst? Char.isAlpha == some 'd'
#guard ['1', '2'].findFirst? Char.isAlpha |>.isNone

theorem List.findFirst?_eq_find? (xs : List α) (pred : α → Bool) :
    xs.findFirst? pred = xs.find? pred := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    simp only [findFirst?, find?, ih]
    cases pred head <;> rfl

end Exercise_1_6_5_2

section Exercise_1_6_5_3

def Prod.switch {α β : Type} (pair : α × β) : β × α :=
  (pair.snd, pair.fst)

#guard (42, "hello").switch == ("hello", 42)

theorem Prod.switch_swaps_fields : (x, y).switch = (y, x) := by
  rfl

end Exercise_1_6_5_3

section Exercise_1_6_5_4

inductive PetName where
  | dogName
  | catName

end Exercise_1_6_5_4

section Exercise_1_6_5_5

def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs, ys with
  | [], _ => []
  | _, [] => []
  | x :: xs', y :: ys' => (x, y) :: zip xs' ys'

#guard zip ([] : List Nat) ([] : List Nat) == []
#guard zip ([] : List Nat) [3, 4] == []
#guard zip [0, 1, 2] [3, 4] == [(0, 3), (1, 4)]
#guard zip [0, 1, 2] [3, 4, 5] == [(0, 3), (1, 4), (2, 5)]

theorem List.zip_eq (xs : List α) (ys : List β) : xs.zip ys = zip xs ys := by
  rfl

end Exercise_1_6_5_5

section Exercise_1_6_5_6

def take {α : Type} (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | 0, _ => []
  | _, [] => []
  | k + 1, x :: xs' => x :: take k xs'

#guard take 3 ["bolete", "oyster"] == ["bolete", "oyster"]
#guard take 1 ["bolete", "oyster"] == ["bolete"]

theorem List.take_eq (n : Nat) (xs : List β) : xs.take n = take n xs := by
  rfl

end Exercise_1_6_5_6

section Exercise_1_6_5_7

def distribute : α × (β ⊕ γ) → (α × β) ⊕ (α × γ)
  | (a, Sum.inl b) => Sum.inl (a, b)
  | (a, Sum.inr c) => Sum.inr (a, c)

#guard distribute (42, (Sum.inl "hello" : String ⊕ Float)) == Sum.inl (42, "hello")
#guard distribute (42, (Sum.inr 5.7 : String ⊕ Float)) == Sum.inr (42, 5.7)

end Exercise_1_6_5_7

section Exercise_1_6_5_8

def doubleToSum : Bool × α → α ⊕ α
  | (false, a) => Sum.inl a
  | (true, a) => Sum.inr a

#guard doubleToSum (false, 42) == Sum.inl 42
#guard doubleToSum (true, "hello") == Sum.inr "hello"

end Exercise_1_6_5_8
