#lang forge

open "cm.sigs.frg"

-- Extra scoring rules
-- Among ribbons, there are three categories:
-- red ribbons with poetry, red ribbons without poetry, and blue ribbons
-- If you hold all of ribbons that belong to a single category, you are awarded
-- extra points
pred redPoetryMatchingRibbon[hand: set Card] {
  #{c: Card | c in hand and c.suit = Ribbon and 
  c.month = Jan or c.month = Feb or c.month = Mar} = 3
}

pred redMatchingRibbon[hand: set Card] {
  #{c: Card | c in hand and c.suit = Ribbon and 
  c.month = Apr or c.month = May or c.month = Jul} = 3
}

pred blueMatchingRibbon[hand: set Card] {
  #{c: Card | c in hand and c.suit = Ribbon and 
  (c.month = Jun or c.month = Sep or c.month = Oct)} = 3
}

-- Some of the animal drawings in the animal cards have birds on it
-- If you have all the bird cards, you get extra points
pred godori[hand: set Card] {
  #{c: Card | c in hand and c.suit = Animal and 
  (c.month = Feb or c.month = Apr or c.month = Aug)} = 3
}