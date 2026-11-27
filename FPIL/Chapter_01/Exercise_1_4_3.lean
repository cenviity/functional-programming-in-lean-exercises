module

section Exercise_1_4_3_1

structure RectangularPrism where
  height : Float
  width : Float
  depth : Float

end Exercise_1_4_3_1

section Exercise_1_4_3_2

def volume (r : RectangularPrism) : Float :=
  r.height * r.width * r.depth

end Exercise_1_4_3_2

section Exercise_1_4_3_3

structure Point where
  x : Float
  y : Float

structure Segment where
  points : Point × Point

def length (s : Segment) : Float :=
  let (p1, p2) := s.points
  let squaredLength := (p2.x - p1.x) ^ 2 + (p2.y - p1.y) ^ 2
  Float.sqrt squaredLength

#guard length ⟨⟨1, 2⟩, ⟨4, 6⟩⟩ == 5

end Exercise_1_4_3_3

section Exercise_1_4_3_4

#check RectangularPrism
#check RectangularPrism.mk
#check RectangularPrism.height
#check RectangularPrism.width
#check RectangularPrism.depth

end Exercise_1_4_3_4

section Exercise_1_4_3_5

structure Hamster where
  name : String
  fluffy : Bool

#check Hamster
#check Hamster.mk
#check Hamster.name
#check Hamster.fluffy

structure Book where
  makeBook ::
  title : String
  author : String
  price : Float

#check Book
#check Book.makeBook
#check Book.title
#check Book.author
#check Book.price

end Exercise_1_4_3_5
