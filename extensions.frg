#lang forge

open "cm.sigs.frg"

-- Extra scoring rules
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

pred godori[hand: set Card] {
  #{c: Card | c in hand and c.suit = Animal and 
  (c.month = Feb or c.month = Apr or c.month = Aug)} = 3
}